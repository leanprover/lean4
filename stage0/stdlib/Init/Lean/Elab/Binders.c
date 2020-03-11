// Lean compiler output
// Module: Init.Lean.Elab.Binders
// Imports: Init.Lean.Elab.Term Init.Lean.Elab.Quotation
#include "runtime/lean.h"
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
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6;
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_2__expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__13;
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_2__expandBinderIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__5;
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabFun___closed__1;
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__6;
extern lean_object* l_Lean_List_format___rarg___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__8;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_1__expandBinderType___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_elabForall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__5;
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__3;
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_object*);
lean_object* l_Lean_Elab_Term_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
extern lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___spec__1___closed__3;
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__18;
extern lean_object* l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_1__expandBinderType(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_1__quoteName___main(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__5;
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_binderTactic___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8;
lean_object* l_Lean_Syntax_isSimpleTermId_x3f(lean_object*, uint8_t);
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4;
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6;
lean_object* l_Lean_Elab_Term_elabFunCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl(lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshFVarId___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__25;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__1;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1;
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_14__regTraceClasses(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__6;
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__3;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__7;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__1;
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*);
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabFun(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__31;
extern lean_object* l_Lean_mkAppStx___closed__6;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_Quotation_isAntiquot(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetBangDecl___closed__1;
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetBangDecl___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__1;
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_5__matchBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1;
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Init_Lean_Elab_Binders_3__expandOptIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl___closed__1;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1;
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_str___elambda__1___closed__2;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
extern lean_object* l_Lean_mkAppStx___closed__5;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__3;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__8;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
lean_object* l_Lean_Elab_Term_elabLetDecl___closed__2;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isTermId_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDecl___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__5;
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__10;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_Quotation_isAntiquotSplice(lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__7;
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
extern lean_object* l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetBangDecl(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__42;
lean_object* l___private_Init_Lean_Elab_Binders_5__matchBinder___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__24;
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__15;
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
extern lean_object* l_Lean_Parser_Term_binderDefault___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl(lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__9;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__4;
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__8;
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
extern lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___spec__1___closed__4;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__30;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__28;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__58;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__3;
lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__3;
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__33;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_3__expandOptIdent(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_12__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l_Lean_Elab_Term_elabBinder(lean_object*);
lean_object* l___private_Init_Lean_Elab_Binders_1__expandBinderType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_mkHole(x_1);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_1__expandBinderType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Binders_1__expandBinderType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_2__expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getArgs(x_1);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_1, x_2, x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_2__expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Binders_2__expandBinderIdent(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_3__expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getNumArgs(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Syntax_getArg(x_1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_mkFreshInstanceName___rarg(x_3);
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
}
lean_object* l___private_Init_Lean_Elab_Binders_3__expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Binders_3__expandOptIdent(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalic auto tactic, antiquotation is not allowed");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_12);
x_18 = lean_nat_dec_lt(x_13, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_57; uint8_t x_58; 
x_20 = lean_array_fget(x_12, x_13);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_13, x_21);
lean_dec(x_13);
x_57 = l_Lean_nullKind;
x_58 = lean_name_eq(x_1, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_23 = x_59;
goto block_56;
}
else
{
uint8_t x_60; 
x_60 = l_Lean_Elab_Term_Quotation_isAntiquotSplice(x_20);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_23 = x_61;
goto block_56;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3;
x_63 = l_Lean_Elab_Term_throwError___rarg(x_20, x_62, x_15, x_16);
lean_dec(x_20);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_56:
{
lean_object* x_24; 
lean_dec(x_23);
lean_inc(x_15);
x_24 = l_Lean_Elab_Term_quoteAutoTactic___main(x_20, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_15, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkAppStx___closed__7;
lean_inc(x_3);
x_34 = lean_name_mk_string(x_3, x_33);
x_35 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___spec__1___closed__4;
lean_inc(x_7);
x_36 = lean_name_mk_string(x_7, x_35);
lean_inc(x_36);
x_37 = l_Lean_addMacroScope(x_31, x_36, x_28);
lean_inc(x_8);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_8);
lean_inc(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
x_40 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___spec__1___closed__3;
lean_inc(x_6);
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_39);
lean_inc(x_5);
x_42 = lean_array_push(x_5, x_41);
lean_inc(x_11);
x_43 = lean_array_push(x_42, x_11);
lean_inc(x_4);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_5);
x_45 = lean_array_push(x_5, x_44);
lean_inc(x_5);
x_46 = lean_array_push(x_5, x_14);
x_47 = lean_array_push(x_46, x_25);
lean_inc(x_10);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_push(x_45, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_49);
x_13 = x_22;
x_14 = x_50;
x_16 = x_32;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
return x_24;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_24, 0);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_24);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalic auto tactic, identifier is not allowed");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_5 = l_unreachable_x21___rarg(x_4);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_Elab_Term_Quotation_isAntiquot(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__8;
x_21 = l_Lean_addMacroScope(x_17, x_20, x_14);
x_22 = lean_box(0);
x_23 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__4;
x_24 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__10;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_29 = lean_array_push(x_27, x_28);
x_30 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_30);
x_31 = l_Lean_mkAppStx___closed__6;
x_32 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__6;
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_35 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(x_7, x_8, x_31, x_30, x_26, x_19, x_32, x_22, x_22, x_33, x_28, x_8, x_34, x_1, x_2, x_18);
lean_dec(x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_37);
lean_dec(x_2);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Term_getMainModule___rarg(x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__15;
x_45 = l_Lean_addMacroScope(x_43, x_44, x_39);
x_46 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__13;
x_47 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__18;
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_array_push(x_26, x_48);
x_50 = lean_array_push(x_49, x_28);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_30);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_26, x_51);
x_53 = l___private_Init_Lean_Elab_Quotation_1__quoteName___main(x_7);
x_54 = lean_array_push(x_26, x_53);
x_55 = lean_array_push(x_54, x_36);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_push(x_52, x_56);
x_58 = l_Lean_mkAppStx___closed__8;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_41, 0, x_59);
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_60 = lean_ctor_get(x_41, 0);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_41);
x_62 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__15;
x_63 = l_Lean_addMacroScope(x_60, x_62, x_39);
x_64 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__13;
x_65 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__18;
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_19);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_63);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_array_push(x_26, x_66);
x_68 = lean_array_push(x_67, x_28);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_30);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_26, x_69);
x_71 = l___private_Init_Lean_Elab_Quotation_1__quoteName___main(x_7);
x_72 = lean_array_push(x_26, x_71);
x_73 = lean_array_push(x_72, x_36);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_70, x_74);
x_76 = l_Lean_mkAppStx___closed__8;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_61);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_2);
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
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_1);
x_83 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Elab_Term_getMainModule___rarg(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
x_90 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__8;
x_91 = l_Lean_addMacroScope(x_87, x_90, x_84);
x_92 = lean_box(0);
x_93 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__4;
x_94 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__10;
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_94);
x_96 = l_Array_empty___closed__1;
x_97 = lean_array_push(x_96, x_95);
x_98 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_99 = lean_array_push(x_97, x_98);
x_100 = l_Lean_mkTermIdFromIdent___closed__2;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_mkAppStx___closed__6;
x_103 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__6;
x_104 = l_Lean_nullKind___closed__2;
x_105 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_106 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(x_7, x_8, x_102, x_100, x_96, x_89, x_103, x_92, x_92, x_104, x_98, x_8, x_105, x_101, x_2, x_88);
lean_dec(x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_108);
lean_dec(x_2);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Lean_Elab_Term_getMainModule___rarg(x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__15;
x_117 = l_Lean_addMacroScope(x_113, x_116, x_110);
x_118 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__13;
x_119 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__18;
x_120 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_120, 0, x_89);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_array_push(x_96, x_120);
x_122 = lean_array_push(x_121, x_98);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_100);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_push(x_96, x_123);
x_125 = l___private_Init_Lean_Elab_Quotation_1__quoteName___main(x_7);
x_126 = lean_array_push(x_96, x_125);
x_127 = lean_array_push(x_126, x_107);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_104);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_array_push(x_124, x_128);
x_130 = l_Lean_mkAppStx___closed__8;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
if (lean_is_scalar(x_115)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_115;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_114);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_7);
lean_dec(x_2);
x_133 = lean_ctor_get(x_106, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_106, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_135 = x_106;
} else {
 lean_dec_ref(x_106);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_8);
lean_dec(x_7);
x_137 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3;
x_138 = l_Lean_Elab_Term_throwError___rarg(x_1, x_137, x_2, x_3);
lean_dec(x_1);
return x_138;
}
}
case 2:
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_1);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_140 = lean_ctor_get(x_1, 1);
x_141 = lean_ctor_get(x_1, 0);
lean_dec(x_141);
x_142 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
lean_dec(x_2);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Elab_Term_getMainModule___rarg(x_144);
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_box(0);
x_149 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__25;
lean_inc(x_143);
lean_inc(x_147);
x_150 = l_Lean_addMacroScope(x_147, x_149, x_143);
x_151 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__24;
x_152 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__28;
x_153 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_152);
x_154 = l_Array_empty___closed__1;
x_155 = lean_array_push(x_154, x_153);
x_156 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_157 = lean_array_push(x_155, x_156);
x_158 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_157);
lean_ctor_set(x_1, 0, x_158);
x_159 = lean_array_push(x_154, x_1);
x_160 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__31;
x_161 = l_Lean_addMacroScope(x_147, x_160, x_143);
x_162 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__30;
x_163 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__33;
x_164 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_164, 0, x_148);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_161);
lean_ctor_set(x_164, 3, x_163);
x_165 = lean_array_push(x_154, x_164);
x_166 = lean_array_push(x_165, x_156);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_array_push(x_154, x_167);
x_169 = l_Lean_mkStxStrLit(x_140, x_148);
x_170 = l_Lean_mkOptionalNode___closed__2;
x_171 = lean_array_push(x_170, x_169);
x_172 = l_Lean_Parser_Term_str___elambda__1___closed__2;
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_array_push(x_168, x_173);
x_175 = l_Lean_nullKind___closed__2;
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = lean_array_push(x_159, x_176);
x_178 = l_Lean_mkAppStx___closed__8;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_145, 0, x_179);
return x_145;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_180 = lean_ctor_get(x_145, 0);
x_181 = lean_ctor_get(x_145, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_145);
x_182 = lean_box(0);
x_183 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__25;
lean_inc(x_143);
lean_inc(x_180);
x_184 = l_Lean_addMacroScope(x_180, x_183, x_143);
x_185 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__24;
x_186 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__28;
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_187, 2, x_184);
lean_ctor_set(x_187, 3, x_186);
x_188 = l_Array_empty___closed__1;
x_189 = lean_array_push(x_188, x_187);
x_190 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_191 = lean_array_push(x_189, x_190);
x_192 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_191);
lean_ctor_set(x_1, 0, x_192);
x_193 = lean_array_push(x_188, x_1);
x_194 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__31;
x_195 = l_Lean_addMacroScope(x_180, x_194, x_143);
x_196 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__30;
x_197 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__33;
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_182);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_197);
x_199 = lean_array_push(x_188, x_198);
x_200 = lean_array_push(x_199, x_190);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_192);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_array_push(x_188, x_201);
x_203 = l_Lean_mkStxStrLit(x_140, x_182);
x_204 = l_Lean_mkOptionalNode___closed__2;
x_205 = lean_array_push(x_204, x_203);
x_206 = l_Lean_Parser_Term_str___elambda__1___closed__2;
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_array_push(x_202, x_207);
x_209 = l_Lean_nullKind___closed__2;
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_array_push(x_193, x_210);
x_212 = l_Lean_mkAppStx___closed__8;
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_181);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_215 = lean_ctor_get(x_1, 1);
lean_inc(x_215);
lean_dec(x_1);
x_216 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
lean_dec(x_2);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Elab_Term_getMainModule___rarg(x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_box(0);
x_224 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__25;
lean_inc(x_217);
lean_inc(x_220);
x_225 = l_Lean_addMacroScope(x_220, x_224, x_217);
x_226 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__24;
x_227 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__28;
x_228 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_228, 0, x_223);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_227);
x_229 = l_Array_empty___closed__1;
x_230 = lean_array_push(x_229, x_228);
x_231 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_232 = lean_array_push(x_230, x_231);
x_233 = l_Lean_mkTermIdFromIdent___closed__2;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = lean_array_push(x_229, x_234);
x_236 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__31;
x_237 = l_Lean_addMacroScope(x_220, x_236, x_217);
x_238 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__30;
x_239 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__33;
x_240 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_240, 0, x_223);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_240, 2, x_237);
lean_ctor_set(x_240, 3, x_239);
x_241 = lean_array_push(x_229, x_240);
x_242 = lean_array_push(x_241, x_231);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_233);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_array_push(x_229, x_243);
x_245 = l_Lean_mkStxStrLit(x_215, x_223);
x_246 = l_Lean_mkOptionalNode___closed__2;
x_247 = lean_array_push(x_246, x_245);
x_248 = l_Lean_Parser_Term_str___elambda__1___closed__2;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = lean_array_push(x_244, x_249);
x_251 = l_Lean_nullKind___closed__2;
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = lean_array_push(x_235, x_252);
x_254 = l_Lean_mkAppStx___closed__8;
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
if (lean_is_scalar(x_222)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_222;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_221);
return x_256;
}
}
default: 
{
lean_object* x_257; lean_object* x_258; 
x_257 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__3;
x_258 = l_Lean_Elab_Term_throwError___rarg(x_1, x_257, x_2, x_3);
lean_dec(x_1);
return x_258;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_quoteAutoTactic___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_auto");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareTacticSyntax___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_ctor_set(x_3, 5, x_7);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_2, 9);
lean_dec(x_9);
lean_ctor_set(x_2, 9, x_5);
x_10 = l_Lean_Elab_Term_getMainModule___rarg(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_17 = l_Lean_addMacroScope(x_11, x_16, x_14);
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_quoteAutoTactic___main(x_1, x_2, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_declareTacticSyntax___closed__4;
x_23 = 1;
lean_inc(x_2);
lean_inc(x_20);
x_24 = l_Lean_Elab_Term_elabTerm(x_20, x_22, x_23, x_2, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l_Lean_Elab_Term_instantiateMVars(x_20, x_25, x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_53 = l_Lean_Elab_Term_getOptions(x_2, x_29);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_declareTacticSyntax___closed__5;
x_57 = l_Lean_checkTraceOption(x_54, x_56);
lean_dec(x_54);
if (x_57 == 0)
{
x_30 = x_55;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_28);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_28);
x_59 = l_Lean_Elab_Term_logTrace(x_56, x_20, x_58, x_2, x_55);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_30 = x_60;
goto block_52;
}
block_52:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_inc(x_17);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_box(0);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_2);
x_37 = l_Lean_Elab_Term_addDecl(x_20, x_36, x_2, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Term_compileDecl(x_20, x_36, x_2, x_38);
lean_dec(x_36);
lean_dec(x_20);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_17);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
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
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
return x_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
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
lean_dec(x_17);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_19);
if (x_65 == 0)
{
return x_19;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_19, 0);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_19);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
x_73 = lean_ctor_get(x_2, 4);
x_74 = lean_ctor_get(x_2, 5);
x_75 = lean_ctor_get(x_2, 6);
x_76 = lean_ctor_get(x_2, 7);
x_77 = lean_ctor_get(x_2, 8);
x_78 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_80 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_70);
lean_ctor_set(x_81, 2, x_71);
lean_ctor_set(x_81, 3, x_72);
lean_ctor_set(x_81, 4, x_73);
lean_ctor_set(x_81, 5, x_74);
lean_ctor_set(x_81, 6, x_75);
lean_ctor_set(x_81, 7, x_76);
lean_ctor_set(x_81, 8, x_77);
lean_ctor_set(x_81, 9, x_5);
lean_ctor_set_uint8(x_81, sizeof(void*)*10, x_78);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 1, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 2, x_80);
x_82 = l_Lean_Elab_Term_getMainModule___rarg(x_3);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Elab_Term_getCurrMacroScope(x_81, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_89 = l_Lean_addMacroScope(x_83, x_88, x_86);
x_90 = lean_box(0);
lean_inc(x_81);
x_91 = l_Lean_Elab_Term_quoteAutoTactic___main(x_1, x_81, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Elab_Term_declareTacticSyntax___closed__4;
x_95 = 1;
lean_inc(x_81);
lean_inc(x_92);
x_96 = l_Lean_Elab_Term_elabTerm(x_92, x_94, x_95, x_81, x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_81);
x_99 = l_Lean_Elab_Term_instantiateMVars(x_92, x_97, x_81, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_124 = l_Lean_Elab_Term_getOptions(x_81, x_101);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Elab_Term_declareTacticSyntax___closed__5;
x_128 = l_Lean_checkTraceOption(x_125, x_127);
lean_dec(x_125);
if (x_128 == 0)
{
x_102 = x_126;
goto block_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_100);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_100);
x_130 = l_Lean_Elab_Term_logTrace(x_127, x_92, x_129, x_81, x_126);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_102 = x_131;
goto block_123;
}
block_123:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_inc(x_89);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_90);
lean_ctor_set(x_104, 2, x_103);
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*3, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_inc(x_81);
x_109 = l_Lean_Elab_Term_addDecl(x_92, x_108, x_81, x_102);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_Elab_Term_compileDecl(x_92, x_108, x_81, x_110);
lean_dec(x_108);
lean_dec(x_92);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_89);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_89);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_81);
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_109, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_121 = x_109;
} else {
 lean_dec_ref(x_109);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_81);
x_132 = lean_ctor_get(x_96, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_96, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_134 = x_96;
} else {
 lean_dec_ref(x_96);
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
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_89);
lean_dec(x_81);
x_136 = lean_ctor_get(x_91, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_91, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_138 = x_91;
} else {
 lean_dec_ref(x_91);
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
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_140 = lean_ctor_get(x_3, 0);
x_141 = lean_ctor_get(x_3, 1);
x_142 = lean_ctor_get(x_3, 2);
x_143 = lean_ctor_get(x_3, 3);
x_144 = lean_ctor_get(x_3, 4);
x_145 = lean_ctor_get(x_3, 5);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_3);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_add(x_145, x_146);
x_148 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_141);
lean_ctor_set(x_148, 2, x_142);
lean_ctor_set(x_148, 3, x_143);
lean_ctor_set(x_148, 4, x_144);
lean_ctor_set(x_148, 5, x_147);
x_149 = lean_ctor_get(x_2, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 5);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 6);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 7);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 8);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_159 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_160 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 x_161 = x_2;
} else {
 lean_dec_ref(x_2);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 10, 3);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_150);
lean_ctor_set(x_162, 2, x_151);
lean_ctor_set(x_162, 3, x_152);
lean_ctor_set(x_162, 4, x_153);
lean_ctor_set(x_162, 5, x_154);
lean_ctor_set(x_162, 6, x_155);
lean_ctor_set(x_162, 7, x_156);
lean_ctor_set(x_162, 8, x_157);
lean_ctor_set(x_162, 9, x_145);
lean_ctor_set_uint8(x_162, sizeof(void*)*10, x_158);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 1, x_159);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 2, x_160);
x_163 = l_Lean_Elab_Term_getMainModule___rarg(x_148);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Elab_Term_getCurrMacroScope(x_162, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_170 = l_Lean_addMacroScope(x_164, x_169, x_167);
x_171 = lean_box(0);
lean_inc(x_162);
x_172 = l_Lean_Elab_Term_quoteAutoTactic___main(x_1, x_162, x_168);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_Elab_Term_declareTacticSyntax___closed__4;
x_176 = 1;
lean_inc(x_162);
lean_inc(x_173);
x_177 = l_Lean_Elab_Term_elabTerm(x_173, x_175, x_176, x_162, x_174);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_162);
x_180 = l_Lean_Elab_Term_instantiateMVars(x_173, x_178, x_162, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_205 = l_Lean_Elab_Term_getOptions(x_162, x_182);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Elab_Term_declareTacticSyntax___closed__5;
x_209 = l_Lean_checkTraceOption(x_206, x_208);
lean_dec(x_206);
if (x_209 == 0)
{
x_183 = x_207;
goto block_204;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_inc(x_181);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_181);
x_211 = l_Lean_Elab_Term_logTrace(x_208, x_173, x_210, x_162, x_207);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_183 = x_212;
goto block_204;
}
block_204:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_inc(x_170);
x_185 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_185, 0, x_170);
lean_ctor_set(x_185, 1, x_171);
lean_ctor_set(x_185, 2, x_184);
x_186 = lean_box(0);
x_187 = 0;
x_188 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_181);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*3, x_187);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
lean_inc(x_162);
x_190 = l_Lean_Elab_Term_addDecl(x_173, x_189, x_162, x_183);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_Elab_Term_compileDecl(x_173, x_189, x_162, x_191);
lean_dec(x_189);
lean_dec(x_173);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_170);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_170);
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_198 = x_192;
} else {
 lean_dec_ref(x_192);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_189);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_162);
x_200 = lean_ctor_get(x_190, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_190, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_202 = x_190;
} else {
 lean_dec_ref(x_190);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_162);
x_213 = lean_ctor_get(x_177, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_177, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_215 = x_177;
} else {
 lean_dec_ref(x_177);
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
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_170);
lean_dec(x_162);
x_217 = lean_ctor_get(x_172, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_172, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_219 = x_172;
} else {
 lean_dec_ref(x_172);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__3() {
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
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__7() {
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
lean_object* _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isNone(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
lean_inc(x_7);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Lean_Parser_Term_binderDefault___elambda__1___closed__2;
x_10 = lean_name_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Term_binderTactic___elambda__1___closed__2;
x_12 = lean_name_eq(x_8, x_11);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_7, x_14);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_15);
x_16 = l_Lean_Elab_Term_declareTacticSyntax(x_15, x_3, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_18);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getMainModule___rarg(x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_box(0);
x_26 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_27 = l_Lean_addMacroScope(x_24, x_26, x_20);
x_28 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2;
x_29 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4;
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Array_empty___closed__1;
x_32 = lean_array_push(x_31, x_30);
x_33 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_34 = lean_array_push(x_32, x_33);
x_35 = l_Lean_mkTermIdFromIdent___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_31, x_36);
x_38 = lean_array_push(x_31, x_1);
x_39 = l_Lean_mkTermIdFrom(x_15, x_17);
lean_dec(x_15);
x_40 = lean_array_push(x_38, x_39);
x_41 = l_Lean_nullKind___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_array_push(x_37, x_42);
x_44 = l_Lean_mkAppStx___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_22, 0, x_45);
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_50 = l_Lean_addMacroScope(x_46, x_49, x_20);
x_51 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2;
x_52 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4;
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_53);
x_56 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_57 = lean_array_push(x_55, x_56);
x_58 = l_Lean_mkTermIdFromIdent___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_array_push(x_54, x_59);
x_61 = lean_array_push(x_54, x_1);
x_62 = l_Lean_mkTermIdFrom(x_15, x_17);
lean_dec(x_15);
x_63 = lean_array_push(x_61, x_62);
x_64 = l_Lean_nullKind___closed__2;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_array_push(x_60, x_65);
x_67 = l_Lean_mkAppStx___closed__8;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_47);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
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
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_8);
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_7, x_74);
lean_dec(x_7);
x_76 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
lean_dec(x_3);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Elab_Term_getMainModule___rarg(x_78);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_box(0);
x_83 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_84 = l_Lean_addMacroScope(x_81, x_83, x_77);
x_85 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6;
x_86 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8;
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_86);
x_88 = l_Array_empty___closed__1;
x_89 = lean_array_push(x_88, x_87);
x_90 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_91 = lean_array_push(x_89, x_90);
x_92 = l_Lean_mkTermIdFromIdent___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_88, x_93);
x_95 = lean_array_push(x_88, x_1);
x_96 = lean_array_push(x_95, x_75);
x_97 = l_Lean_nullKind___closed__2;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_94, x_98);
x_100 = l_Lean_mkAppStx___closed__8;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_79, 0, x_101);
return x_79;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_102 = lean_ctor_get(x_79, 0);
x_103 = lean_ctor_get(x_79, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_79);
x_104 = lean_box(0);
x_105 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_106 = l_Lean_addMacroScope(x_102, x_105, x_77);
x_107 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6;
x_108 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8;
x_109 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_108);
x_110 = l_Array_empty___closed__1;
x_111 = lean_array_push(x_110, x_109);
x_112 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_113 = lean_array_push(x_111, x_112);
x_114 = l_Lean_mkTermIdFromIdent___closed__2;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_array_push(x_110, x_115);
x_117 = lean_array_push(x_110, x_1);
x_118 = lean_array_push(x_117, x_75);
x_119 = l_Lean_nullKind___closed__2;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_array_push(x_116, x_120);
x_122 = l_Lean_mkAppStx___closed__8;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_103);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_3);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_4);
return x_125;
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Binders_2__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
lean_dec(x_11);
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Binders_2__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
lean_dec(x_11);
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Binders_2__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
lean_dec(x_11);
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_5__matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
x_7 = lean_name_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_11 = lean_name_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
x_13 = lean_name_eq(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = l_Lean_Syntax_inhabited;
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_array_get(x_15, x_5, x_16);
x_18 = l___private_Init_Lean_Elab_Binders_3__expandOptIdent(x_17, x_2, x_3);
lean_dec(x_2);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_array_get(x_15, x_5, x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = l_Lean_mkOptionalNode___closed__2;
x_26 = lean_array_push(x_25, x_24);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_array_get(x_15, x_5, x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
x_33 = l_Lean_mkOptionalNode___closed__2;
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = l_Lean_Syntax_inhabited;
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_array_get(x_36, x_5, x_37);
x_39 = l_Lean_Syntax_getArgs(x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_array_get(x_36, x_5, x_40);
x_42 = l___private_Init_Lean_Elab_Binders_1__expandBinderType(x_41);
lean_dec(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__1(x_42, x_43, x_39, x_2, x_3);
lean_dec(x_2);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = l_Lean_Syntax_inhabited;
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_array_get(x_45, x_5, x_46);
x_48 = l_Lean_Syntax_getArgs(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_array_get(x_45, x_5, x_49);
x_51 = l___private_Init_Lean_Elab_Binders_1__expandBinderType(x_50);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_array_get(x_45, x_5, x_52);
lean_inc(x_2);
x_54 = l___private_Init_Lean_Elab_Binders_4__expandBinderModifier(x_51, x_53, x_2, x_3);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__2(x_55, x_57, x_48, x_2, x_56);
lean_dec(x_2);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_48);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = l_Lean_Syntax_inhabited;
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_array_get(x_63, x_5, x_64);
x_66 = l_Lean_Syntax_getArgs(x_65);
lean_dec(x_65);
x_67 = l_Lean_mkHole(x_1);
x_68 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__3(x_67, x_64, x_66, x_2, x_3);
lean_dec(x_2);
return x_68;
}
}
else
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_69;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_5__matchBinder___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_5__matchBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Binders_5__matchBinder(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_6);
lean_inc(x_15);
x_21 = l_Lean_Elab_Term_elabType(x_15, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_mkFVar(x_25);
lean_inc(x_27);
x_28 = lean_array_push(x_3, x_27);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
x_30 = l_Lean_Syntax_getId(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_22);
x_32 = lean_local_ctx_mk_local_decl(x_4, x_25, x_30, x_22, x_31);
lean_inc(x_6);
x_33 = l_Lean_Elab_Term_isClass(x_15, x_22, x_6, x_26);
lean_dec(x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_2, x_36);
lean_dec(x_2);
x_2 = x_37;
x_3 = x_28;
x_4 = x_32;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_39);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_27);
x_44 = lean_array_push(x_5, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_2, x_45);
lean_dec(x_2);
x_2 = x_46;
x_3 = x_28;
x_4 = x_32;
x_5 = x_44;
x_7 = x_42;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
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
lean_dec(x_6);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 3);
x_58 = lean_ctor_get(x_14, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_5);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_6, 0, x_59);
lean_inc(x_6);
lean_inc(x_15);
x_60 = l_Lean_Elab_Term_elabType(x_15, x_6, x_7);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_64);
x_66 = l_Lean_mkFVar(x_64);
lean_inc(x_66);
x_67 = lean_array_push(x_3, x_66);
x_68 = lean_ctor_get(x_13, 0);
lean_inc(x_68);
x_69 = l_Lean_Syntax_getId(x_68);
lean_dec(x_68);
x_70 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_61);
x_71 = lean_local_ctx_mk_local_decl(x_4, x_64, x_69, x_61, x_70);
lean_inc(x_6);
x_72 = l_Lean_Elab_Term_isClass(x_15, x_61, x_6, x_65);
lean_dec(x_15);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_66);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_2, x_75);
lean_dec(x_2);
x_2 = x_76;
x_3 = x_67;
x_4 = x_71;
x_7 = x_74;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
lean_dec(x_73);
x_80 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_78);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_66);
x_83 = lean_array_push(x_5, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_2, x_84);
lean_dec(x_2);
x_2 = x_85;
x_3 = x_67;
x_4 = x_71;
x_5 = x_83;
x_7 = x_81;
goto _start;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_89 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_6);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_60, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_60, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_93 = x_60;
} else {
 lean_dec_ref(x_60);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_95 = lean_ctor_get(x_6, 1);
x_96 = lean_ctor_get(x_6, 2);
x_97 = lean_ctor_get(x_6, 3);
x_98 = lean_ctor_get(x_6, 4);
x_99 = lean_ctor_get(x_6, 5);
x_100 = lean_ctor_get(x_6, 6);
x_101 = lean_ctor_get(x_6, 7);
x_102 = lean_ctor_get(x_6, 8);
x_103 = lean_ctor_get(x_6, 9);
x_104 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_105 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_106 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_6);
x_107 = lean_ctor_get(x_14, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_14, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_14, 4);
lean_inc(x_109);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_110 = x_14;
} else {
 lean_dec_ref(x_14);
 x_110 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_4);
lean_ctor_set(x_111, 2, x_5);
lean_ctor_set(x_111, 3, x_108);
lean_ctor_set(x_111, 4, x_109);
x_112 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_95);
lean_ctor_set(x_112, 2, x_96);
lean_ctor_set(x_112, 3, x_97);
lean_ctor_set(x_112, 4, x_98);
lean_ctor_set(x_112, 5, x_99);
lean_ctor_set(x_112, 6, x_100);
lean_ctor_set(x_112, 7, x_101);
lean_ctor_set(x_112, 8, x_102);
lean_ctor_set(x_112, 9, x_103);
lean_ctor_set_uint8(x_112, sizeof(void*)*10, x_104);
lean_ctor_set_uint8(x_112, sizeof(void*)*10 + 1, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*10 + 2, x_106);
lean_inc(x_112);
lean_inc(x_15);
x_113 = l_Lean_Elab_Term_elabType(x_15, x_112, x_7);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = l_Lean_mkFVar(x_117);
lean_inc(x_119);
x_120 = lean_array_push(x_3, x_119);
x_121 = lean_ctor_get(x_13, 0);
lean_inc(x_121);
x_122 = l_Lean_Syntax_getId(x_121);
lean_dec(x_121);
x_123 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_114);
x_124 = lean_local_ctx_mk_local_decl(x_4, x_117, x_122, x_114, x_123);
lean_inc(x_112);
x_125 = l_Lean_Elab_Term_isClass(x_15, x_114, x_112, x_118);
lean_dec(x_15);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_119);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_2, x_128);
lean_dec(x_2);
x_2 = x_129;
x_3 = x_120;
x_4 = x_124;
x_6 = x_112;
x_7 = x_127;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_dec(x_125);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
lean_dec(x_126);
x_133 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_131);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_119);
x_136 = lean_array_push(x_5, x_135);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_2, x_137);
lean_dec(x_2);
x_2 = x_138;
x_3 = x_120;
x_4 = x_124;
x_5 = x_136;
x_6 = x_112;
x_7 = x_134;
goto _start;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_112);
lean_dec(x_5);
lean_dec(x_2);
x_140 = lean_ctor_get(x_125, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_142 = x_125;
} else {
 lean_dec_ref(x_125);
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
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_112);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = lean_ctor_get(x_113, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_113, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_146 = x_113;
} else {
 lean_dec_ref(x_113);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_6__elabBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Binders_6__elabBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_1, x_2);
lean_inc(x_6);
x_14 = l___private_Init_Lean_Elab_Binders_5__matchBinder(x_13, x_6, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_18 = l___private_Init_Lean_Elab_Binders_6__elabBinderViews___main(x_15, x_17, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_3 = x_22;
x_4 = x_23;
x_5 = x_24;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_7__elabBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Binders_7__elabBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_getLocalInsts(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_10);
x_14 = l___private_Init_Lean_Elab_Binders_7__elabBindersAux___main(x_1, x_12, x_13, x_7, x_10, x_3, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_array_get_size(x_10);
lean_dec(x_10);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_dec(x_28);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 1, x_19);
x_29 = lean_apply_3(x_2, x_18, x_3, x_17);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 3);
x_32 = lean_ctor_get(x_25, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_20);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_3, 0, x_33);
x_34 = lean_apply_3(x_2, x_18, x_3, x_17);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_3, 2);
x_38 = lean_ctor_get(x_3, 3);
x_39 = lean_ctor_get(x_3, 4);
x_40 = lean_ctor_get(x_3, 5);
x_41 = lean_ctor_get(x_3, 6);
x_42 = lean_ctor_get(x_3, 7);
x_43 = lean_ctor_get(x_3, 8);
x_44 = lean_ctor_get(x_3, 9);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_35, 4);
lean_inc(x_50);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 x_51 = x_35;
} else {
 lean_dec_ref(x_35);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 5, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_19);
lean_ctor_set(x_52, 2, x_20);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
x_53 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_36);
lean_ctor_set(x_53, 2, x_37);
lean_ctor_set(x_53, 3, x_38);
lean_ctor_set(x_53, 4, x_39);
lean_ctor_set(x_53, 5, x_40);
lean_ctor_set(x_53, 6, x_41);
lean_ctor_set(x_53, 7, x_42);
lean_ctor_set(x_53, 8, x_43);
lean_ctor_set(x_53, 9, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*10, x_45);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 1, x_46);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 2, x_47);
x_54 = lean_apply_3(x_2, x_18, x_53, x_17);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_17, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_17);
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_3);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_3, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_dec(x_65);
lean_ctor_set(x_59, 2, x_20);
lean_ctor_set(x_59, 1, x_19);
x_66 = lean_apply_3(x_2, x_18, x_3, x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_66, 1);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_67, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_68, 2);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_69, 2);
lean_dec(x_77);
lean_ctor_set(x_69, 2, x_57);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_57);
lean_ctor_set(x_68, 2, x_80);
return x_66;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_68, 0);
x_82 = lean_ctor_get(x_68, 1);
x_83 = lean_ctor_get(x_68, 3);
x_84 = lean_ctor_get(x_68, 4);
x_85 = lean_ctor_get(x_68, 5);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_68);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_57);
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_82);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_83);
lean_ctor_set(x_90, 4, x_84);
lean_ctor_set(x_90, 5, x_85);
lean_ctor_set(x_67, 0, x_90);
return x_66;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_ctor_get(x_67, 1);
x_92 = lean_ctor_get(x_67, 2);
x_93 = lean_ctor_get(x_67, 3);
x_94 = lean_ctor_get(x_67, 4);
x_95 = lean_ctor_get(x_67, 5);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_67);
x_96 = lean_ctor_get(x_68, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_68, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_68, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_68, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_68, 5);
lean_inc(x_100);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 lean_ctor_release(x_68, 5);
 x_101 = x_68;
} else {
 lean_dec_ref(x_68);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_69, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_69, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 x_104 = x_69;
} else {
 lean_dec_ref(x_69);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 3, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_57);
if (lean_is_scalar(x_101)) {
 x_106 = lean_alloc_ctor(0, 6, 0);
} else {
 x_106 = x_101;
}
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_97);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_98);
lean_ctor_set(x_106, 4, x_99);
lean_ctor_set(x_106, 5, x_100);
x_107 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_91);
lean_ctor_set(x_107, 2, x_92);
lean_ctor_set(x_107, 3, x_93);
lean_ctor_set(x_107, 4, x_94);
lean_ctor_set(x_107, 5, x_95);
lean_ctor_set(x_66, 1, x_107);
return x_66;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_108 = lean_ctor_get(x_66, 0);
lean_inc(x_108);
lean_dec(x_66);
x_109 = lean_ctor_get(x_67, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_67, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_67, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_67, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_67, 5);
lean_inc(x_113);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 lean_ctor_release(x_67, 5);
 x_114 = x_67;
} else {
 lean_dec_ref(x_67);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_68, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_68, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_68, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_68, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_68, 5);
lean_inc(x_119);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 lean_ctor_release(x_68, 5);
 x_120 = x_68;
} else {
 lean_dec_ref(x_68);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_69, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_69, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 x_123 = x_69;
} else {
 lean_dec_ref(x_69);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 3, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_57);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set(x_125, 4, x_118);
lean_ctor_set(x_125, 5, x_119);
if (lean_is_scalar(x_114)) {
 x_126 = lean_alloc_ctor(0, 6, 0);
} else {
 x_126 = x_114;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_109);
lean_ctor_set(x_126, 2, x_110);
lean_ctor_set(x_126, 3, x_111);
lean_ctor_set(x_126, 4, x_112);
lean_ctor_set(x_126, 5, x_113);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_108);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_66, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 2);
lean_inc(x_130);
x_131 = !lean_is_exclusive(x_66);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_66, 1);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_128);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_128, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_129);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_129, 2);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_130);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_130, 2);
lean_dec(x_138);
lean_ctor_set(x_130, 2, x_57);
return x_66;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_130, 0);
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_130);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_57);
lean_ctor_set(x_129, 2, x_141);
return x_66;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_129, 0);
x_143 = lean_ctor_get(x_129, 1);
x_144 = lean_ctor_get(x_129, 3);
x_145 = lean_ctor_get(x_129, 4);
x_146 = lean_ctor_get(x_129, 5);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_129);
x_147 = lean_ctor_get(x_130, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_130, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_149 = x_130;
} else {
 lean_dec_ref(x_130);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 3, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
lean_ctor_set(x_150, 2, x_57);
x_151 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_151, 3, x_144);
lean_ctor_set(x_151, 4, x_145);
lean_ctor_set(x_151, 5, x_146);
lean_ctor_set(x_128, 0, x_151);
return x_66;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_152 = lean_ctor_get(x_128, 1);
x_153 = lean_ctor_get(x_128, 2);
x_154 = lean_ctor_get(x_128, 3);
x_155 = lean_ctor_get(x_128, 4);
x_156 = lean_ctor_get(x_128, 5);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_128);
x_157 = lean_ctor_get(x_129, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_129, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_129, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_129, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_129, 5);
lean_inc(x_161);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 x_162 = x_129;
} else {
 lean_dec_ref(x_129);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_130, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_130, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_165 = x_130;
} else {
 lean_dec_ref(x_130);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 3, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 2, x_57);
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(0, 6, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_157);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_159);
lean_ctor_set(x_167, 4, x_160);
lean_ctor_set(x_167, 5, x_161);
x_168 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_152);
lean_ctor_set(x_168, 2, x_153);
lean_ctor_set(x_168, 3, x_154);
lean_ctor_set(x_168, 4, x_155);
lean_ctor_set(x_168, 5, x_156);
lean_ctor_set(x_66, 1, x_168);
return x_66;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_169 = lean_ctor_get(x_66, 0);
lean_inc(x_169);
lean_dec(x_66);
x_170 = lean_ctor_get(x_128, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_128, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_128, 4);
lean_inc(x_173);
x_174 = lean_ctor_get(x_128, 5);
lean_inc(x_174);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 lean_ctor_release(x_128, 5);
 x_175 = x_128;
} else {
 lean_dec_ref(x_128);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_129, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_129, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_129, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_129, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_129, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 x_181 = x_129;
} else {
 lean_dec_ref(x_129);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_130, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_130, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_184 = x_130;
} else {
 lean_dec_ref(x_130);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_57);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_177);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_178);
lean_ctor_set(x_186, 4, x_179);
lean_ctor_set(x_186, 5, x_180);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 6, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_170);
lean_ctor_set(x_187, 2, x_171);
lean_ctor_set(x_187, 3, x_172);
lean_ctor_set(x_187, 4, x_173);
lean_ctor_set(x_187, 5, x_174);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_169);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_59, 0);
x_190 = lean_ctor_get(x_59, 3);
x_191 = lean_ctor_get(x_59, 4);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_59);
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_19);
lean_ctor_set(x_192, 2, x_20);
lean_ctor_set(x_192, 3, x_190);
lean_ctor_set(x_192, 4, x_191);
lean_ctor_set(x_3, 0, x_192);
x_193 = lean_apply_3(x_2, x_18, x_3, x_60);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_198 = x_193;
} else {
 lean_dec_ref(x_193);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_194, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_194, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_194, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_194, 5);
lean_inc(x_203);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 lean_ctor_release(x_194, 4);
 lean_ctor_release(x_194, 5);
 x_204 = x_194;
} else {
 lean_dec_ref(x_194);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_195, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_195, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_195, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_195, 4);
lean_inc(x_208);
x_209 = lean_ctor_get(x_195, 5);
lean_inc(x_209);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 lean_ctor_release(x_195, 5);
 x_210 = x_195;
} else {
 lean_dec_ref(x_195);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_196, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_196, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 x_213 = x_196;
} else {
 lean_dec_ref(x_196);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 3, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
lean_ctor_set(x_214, 2, x_57);
if (lean_is_scalar(x_210)) {
 x_215 = lean_alloc_ctor(0, 6, 0);
} else {
 x_215 = x_210;
}
lean_ctor_set(x_215, 0, x_205);
lean_ctor_set(x_215, 1, x_206);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_207);
lean_ctor_set(x_215, 4, x_208);
lean_ctor_set(x_215, 5, x_209);
if (lean_is_scalar(x_204)) {
 x_216 = lean_alloc_ctor(0, 6, 0);
} else {
 x_216 = x_204;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_199);
lean_ctor_set(x_216, 2, x_200);
lean_ctor_set(x_216, 3, x_201);
lean_ctor_set(x_216, 4, x_202);
lean_ctor_set(x_216, 5, x_203);
if (lean_is_scalar(x_198)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_198;
}
lean_ctor_set(x_217, 0, x_197);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_218 = lean_ctor_get(x_193, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_193, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_222 = x_193;
} else {
 lean_dec_ref(x_193);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_218, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_218, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_218, 4);
lean_inc(x_226);
x_227 = lean_ctor_get(x_218, 5);
lean_inc(x_227);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 lean_ctor_release(x_218, 4);
 lean_ctor_release(x_218, 5);
 x_228 = x_218;
} else {
 lean_dec_ref(x_218);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_219, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_219, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_219, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_219, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_219, 5);
lean_inc(x_233);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 lean_ctor_release(x_219, 4);
 lean_ctor_release(x_219, 5);
 x_234 = x_219;
} else {
 lean_dec_ref(x_219);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_220, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 x_237 = x_220;
} else {
 lean_dec_ref(x_220);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 3, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
lean_ctor_set(x_238, 2, x_57);
if (lean_is_scalar(x_234)) {
 x_239 = lean_alloc_ctor(0, 6, 0);
} else {
 x_239 = x_234;
}
lean_ctor_set(x_239, 0, x_229);
lean_ctor_set(x_239, 1, x_230);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_231);
lean_ctor_set(x_239, 4, x_232);
lean_ctor_set(x_239, 5, x_233);
if (lean_is_scalar(x_228)) {
 x_240 = lean_alloc_ctor(0, 6, 0);
} else {
 x_240 = x_228;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_223);
lean_ctor_set(x_240, 2, x_224);
lean_ctor_set(x_240, 3, x_225);
lean_ctor_set(x_240, 4, x_226);
lean_ctor_set(x_240, 5, x_227);
if (lean_is_scalar(x_222)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_222;
}
lean_ctor_set(x_241, 0, x_221);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_242 = lean_ctor_get(x_3, 1);
x_243 = lean_ctor_get(x_3, 2);
x_244 = lean_ctor_get(x_3, 3);
x_245 = lean_ctor_get(x_3, 4);
x_246 = lean_ctor_get(x_3, 5);
x_247 = lean_ctor_get(x_3, 6);
x_248 = lean_ctor_get(x_3, 7);
x_249 = lean_ctor_get(x_3, 8);
x_250 = lean_ctor_get(x_3, 9);
x_251 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_252 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_253 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_3);
x_254 = lean_ctor_get(x_59, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_59, 3);
lean_inc(x_255);
x_256 = lean_ctor_get(x_59, 4);
lean_inc(x_256);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_257 = x_59;
} else {
 lean_dec_ref(x_59);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(0, 5, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_19);
lean_ctor_set(x_258, 2, x_20);
lean_ctor_set(x_258, 3, x_255);
lean_ctor_set(x_258, 4, x_256);
x_259 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_242);
lean_ctor_set(x_259, 2, x_243);
lean_ctor_set(x_259, 3, x_244);
lean_ctor_set(x_259, 4, x_245);
lean_ctor_set(x_259, 5, x_246);
lean_ctor_set(x_259, 6, x_247);
lean_ctor_set(x_259, 7, x_248);
lean_ctor_set(x_259, 8, x_249);
lean_ctor_set(x_259, 9, x_250);
lean_ctor_set_uint8(x_259, sizeof(void*)*10, x_251);
lean_ctor_set_uint8(x_259, sizeof(void*)*10 + 1, x_252);
lean_ctor_set_uint8(x_259, sizeof(void*)*10 + 2, x_253);
x_260 = lean_apply_3(x_2, x_18, x_259, x_60);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_262, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_260, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_265 = x_260;
} else {
 lean_dec_ref(x_260);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_261, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_261, 2);
lean_inc(x_267);
x_268 = lean_ctor_get(x_261, 3);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 4);
lean_inc(x_269);
x_270 = lean_ctor_get(x_261, 5);
lean_inc(x_270);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 x_271 = x_261;
} else {
 lean_dec_ref(x_261);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_262, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_262, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_262, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_262, 4);
lean_inc(x_275);
x_276 = lean_ctor_get(x_262, 5);
lean_inc(x_276);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 lean_ctor_release(x_262, 3);
 lean_ctor_release(x_262, 4);
 lean_ctor_release(x_262, 5);
 x_277 = x_262;
} else {
 lean_dec_ref(x_262);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_263, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_263, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 x_280 = x_263;
} else {
 lean_dec_ref(x_263);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 3, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
lean_ctor_set(x_281, 2, x_57);
if (lean_is_scalar(x_277)) {
 x_282 = lean_alloc_ctor(0, 6, 0);
} else {
 x_282 = x_277;
}
lean_ctor_set(x_282, 0, x_272);
lean_ctor_set(x_282, 1, x_273);
lean_ctor_set(x_282, 2, x_281);
lean_ctor_set(x_282, 3, x_274);
lean_ctor_set(x_282, 4, x_275);
lean_ctor_set(x_282, 5, x_276);
if (lean_is_scalar(x_271)) {
 x_283 = lean_alloc_ctor(0, 6, 0);
} else {
 x_283 = x_271;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_266);
lean_ctor_set(x_283, 2, x_267);
lean_ctor_set(x_283, 3, x_268);
lean_ctor_set(x_283, 4, x_269);
lean_ctor_set(x_283, 5, x_270);
if (lean_is_scalar(x_265)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_265;
}
lean_ctor_set(x_284, 0, x_264);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_285 = lean_ctor_get(x_260, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_286, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_260, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_289 = x_260;
} else {
 lean_dec_ref(x_260);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_285, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_285, 2);
lean_inc(x_291);
x_292 = lean_ctor_get(x_285, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_285, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_285, 5);
lean_inc(x_294);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 lean_ctor_release(x_285, 4);
 lean_ctor_release(x_285, 5);
 x_295 = x_285;
} else {
 lean_dec_ref(x_285);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_286, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_286, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_286, 3);
lean_inc(x_298);
x_299 = lean_ctor_get(x_286, 4);
lean_inc(x_299);
x_300 = lean_ctor_get(x_286, 5);
lean_inc(x_300);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 lean_ctor_release(x_286, 2);
 lean_ctor_release(x_286, 3);
 lean_ctor_release(x_286, 4);
 lean_ctor_release(x_286, 5);
 x_301 = x_286;
} else {
 lean_dec_ref(x_286);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_287, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_287, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 x_304 = x_287;
} else {
 lean_dec_ref(x_287);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 3, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
lean_ctor_set(x_305, 2, x_57);
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(0, 6, 0);
} else {
 x_306 = x_301;
}
lean_ctor_set(x_306, 0, x_296);
lean_ctor_set(x_306, 1, x_297);
lean_ctor_set(x_306, 2, x_305);
lean_ctor_set(x_306, 3, x_298);
lean_ctor_set(x_306, 4, x_299);
lean_ctor_set(x_306, 5, x_300);
if (lean_is_scalar(x_295)) {
 x_307 = lean_alloc_ctor(0, 6, 0);
} else {
 x_307 = x_295;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_290);
lean_ctor_set(x_307, 2, x_291);
lean_ctor_set(x_307, 3, x_292);
lean_ctor_set(x_307, 4, x_293);
lean_ctor_set(x_307, 5, x_294);
if (lean_is_scalar(x_289)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_289;
}
lean_ctor_set(x_308, 0, x_288);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_309 = !lean_is_exclusive(x_14);
if (x_309 == 0)
{
return x_14;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_14, 0);
x_311 = lean_ctor_get(x_14, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_14);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = l_Array_empty___closed__1;
x_314 = lean_apply_3(x_2, x_313, x_3, x_4);
return x_314;
}
}
}
lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Expr_Inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
x_8 = lean_apply_3(x_1, x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = l_Lean_Elab_Term_elabBinders___rarg(x_6, x_7, x_3, x_4);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabBinder___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_elabType(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_mkForall(x_2, x_3, x_7, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
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
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1___boxed), 5, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_1);
x_19 = l_Lean_Elab_Term_elabBinders___rarg(x_17, x_18, x_3, x_4);
lean_dec(x_17);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabForall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_elabForall___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabForall(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_List_format___rarg___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_inc(x_1);
x_83 = l_Lean_Syntax_isOfKind(x_1, x_82);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_4 = x_84;
goto block_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = l_Lean_Syntax_getArgs(x_1);
x_86 = lean_array_get_size(x_85);
lean_dec(x_85);
x_87 = lean_unsigned_to_nat(3u);
x_88 = lean_nat_dec_eq(x_86, x_87);
lean_dec(x_86);
x_4 = x_88;
goto block_81;
}
block_81:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getMainModule___rarg(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_18 = l_Lean_addMacroScope(x_15, x_17, x_11);
x_19 = lean_box(0);
x_20 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_nullKind___closed__2;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__42;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_29 = lean_array_push(x_28, x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_27, x_30);
x_32 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_33 = lean_array_push(x_31, x_32);
x_34 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__58;
x_35 = lean_array_push(x_33, x_34);
x_36 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_22, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__2;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_43 = lean_array_push(x_41, x_42);
x_44 = lean_array_push(x_43, x_9);
x_45 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_13, 0, x_46);
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_box(0);
x_50 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_51 = l_Lean_addMacroScope(x_47, x_50, x_11);
x_52 = lean_box(0);
x_53 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
x_55 = l_Array_empty___closed__1;
x_56 = lean_array_push(x_55, x_54);
x_57 = l_Lean_nullKind___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__42;
x_60 = lean_array_push(x_59, x_58);
x_61 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_62 = lean_array_push(x_61, x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_60, x_63);
x_65 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_66 = lean_array_push(x_64, x_65);
x_67 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__58;
x_68 = lean_array_push(x_66, x_67);
x_69 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_array_push(x_55, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__2;
x_74 = lean_array_push(x_73, x_72);
x_75 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_array_push(x_76, x_9);
x_78 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_48);
return x_80;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_elabArrow___closed__1;
x_6 = l_Lean_Elab_Term_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabArrow___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_mkOptionalNode___closed__2;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1___boxed), 5, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
x_12 = l_Lean_Elab_Term_elabBinders___rarg(x_10, x_11, x_3, x_4);
lean_dec(x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabDepArrow(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_95; uint8_t x_96; 
x_95 = l_Lean_mkAppStx___closed__8;
lean_inc(x_2);
x_96 = l_Lean_Syntax_isOfKind(x_2, x_95);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = 0;
x_6 = x_97;
goto block_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = l_Lean_Syntax_getArgs(x_2);
x_99 = lean_array_get_size(x_98);
lean_dec(x_98);
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_nat_dec_eq(x_99, x_100);
lean_dec(x_99);
x_6 = x_101;
goto block_94;
}
block_94:
{
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkHole___closed__2;
lean_inc(x_2);
x_8 = l_Lean_Syntax_isOfKind(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l_Lean_Syntax_isSimpleTermId_x3f(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_array_push(x_3, x_14);
lean_ctor_set(x_10, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_array_push(x_3, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Syntax_getArgs(x_2);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = l_Lean_Syntax_isSimpleTermId_x3f(x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_array_push(x_3, x_30);
lean_ctor_set(x_26, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_array_push(x_3, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_2, x_4, x_5);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_array_push(x_3, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_array_push(x_3, x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Syntax_getArg(x_2, x_47);
x_49 = lean_unsigned_to_nat(1u);
x_50 = l_Lean_Syntax_getArg(x_2, x_49);
x_51 = l_Lean_nullKind___closed__2;
lean_inc(x_50);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_48);
x_53 = 1;
x_54 = l_Lean_Syntax_isSimpleTermId_x3f(x_2, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_5);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_array_push(x_3, x_58);
lean_ctor_set(x_54, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_5);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_array_push(x_3, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_5);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Lean_Syntax_getArgs(x_50);
x_66 = lean_array_get_size(x_65);
lean_dec(x_65);
x_67 = lean_nat_dec_eq(x_66, x_49);
lean_dec(x_66);
if (x_67 == 0)
{
uint8_t x_68; lean_object* x_69; 
lean_dec(x_50);
lean_dec(x_48);
x_68 = 1;
x_69 = l_Lean_Syntax_isSimpleTermId_x3f(x_2, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_3);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_array_push(x_3, x_73);
lean_ctor_set(x_69, 0, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_5);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec(x_69);
x_77 = lean_array_push(x_3, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_5);
return x_79;
}
}
}
else
{
lean_dec(x_2);
if (x_1 == 0)
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_80 = l_Lean_Syntax_getArg(x_50, x_47);
lean_dec(x_50);
x_81 = 0;
x_82 = l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main(x_81, x_48, x_3, x_4, x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_80);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = 1;
x_1 = x_90;
x_2 = x_80;
x_3 = x_89;
x_5 = x_88;
goto _start;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_3);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_5);
return x_93;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_Lean_Elab_Binders_8__getFunBinderIdsAux_x3f___main(x_4, x_1, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_1);
lean_inc(x_8);
x_12 = l_Lean_Elab_Term_mkExplicitBinder(x_8, x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
lean_dec(x_8);
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_match___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid binder, simple identifier expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_array_fget(x_1, x_3);
switch (lean_obj_tag(x_11)) {
case 1:
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
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_13, 1);
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_14, 1);
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_15, 1);
x_29 = lean_ctor_get(x_15, 0);
lean_dec(x_29);
x_30 = l_Lean_mkAppStx___closed__1;
x_31 = lean_string_dec_eq(x_28, x_30);
lean_dec(x_28);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_dec(x_25);
lean_free_object(x_13);
lean_dec(x_22);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_32 = 1;
lean_inc(x_11);
x_33 = l_Lean_Syntax_isTermId_x3f(x_11, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_3, x_37);
lean_dec(x_3);
x_39 = l_Lean_mkHole(x_11);
lean_inc(x_35);
x_40 = l_Lean_Elab_Term_mkExplicitBinder(x_35, x_39);
x_41 = lean_array_push(x_4, x_40);
lean_inc(x_5);
x_42 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_38, x_41, x_5, x_36);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_43, 1);
x_47 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_44);
lean_dec(x_5);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Elab_Term_getMainModule___rarg(x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = l_Array_empty___closed__1;
x_53 = lean_array_push(x_52, x_35);
x_54 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_55 = lean_array_push(x_53, x_54);
x_56 = l_Lean_mkTermIdFromIdent___closed__2;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_52, x_57);
x_59 = l_Lean_nullKind___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_62 = lean_array_push(x_61, x_60);
x_63 = lean_array_push(x_62, x_54);
x_64 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_65 = lean_array_push(x_63, x_64);
x_66 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_67 = lean_array_push(x_65, x_66);
lean_inc(x_11);
x_68 = lean_array_push(x_52, x_11);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = lean_ctor_get(x_11, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_11, 0);
lean_dec(x_71);
lean_ctor_set(x_11, 1, x_68);
lean_ctor_set(x_11, 0, x_59);
x_72 = lean_array_push(x_52, x_11);
x_73 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_array_push(x_74, x_46);
x_76 = l_Lean_Parser_Term_matchAlt___closed__2;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_52, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_59);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_array_push(x_67, x_79);
x_81 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_43, 1, x_82);
lean_ctor_set(x_49, 0, x_43);
return x_49;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_11);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_68);
x_84 = lean_array_push(x_52, x_83);
x_85 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_86 = lean_array_push(x_84, x_85);
x_87 = lean_array_push(x_86, x_46);
x_88 = l_Lean_Parser_Term_matchAlt___closed__2;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_array_push(x_52, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_59);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_array_push(x_67, x_91);
x_93 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_43, 1, x_94);
lean_ctor_set(x_49, 0, x_43);
return x_49;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_95 = lean_ctor_get(x_49, 1);
lean_inc(x_95);
lean_dec(x_49);
x_96 = l_Array_empty___closed__1;
x_97 = lean_array_push(x_96, x_35);
x_98 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_99 = lean_array_push(x_97, x_98);
x_100 = l_Lean_mkTermIdFromIdent___closed__2;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_array_push(x_96, x_101);
x_103 = l_Lean_nullKind___closed__2;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_106 = lean_array_push(x_105, x_104);
x_107 = lean_array_push(x_106, x_98);
x_108 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_109 = lean_array_push(x_107, x_108);
x_110 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_111 = lean_array_push(x_109, x_110);
lean_inc(x_11);
x_112 = lean_array_push(x_96, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_113 = x_11;
} else {
 lean_dec_ref(x_11);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_103);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_array_push(x_96, x_114);
x_116 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_117 = lean_array_push(x_115, x_116);
x_118 = lean_array_push(x_117, x_46);
x_119 = l_Lean_Parser_Term_matchAlt___closed__2;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_array_push(x_96, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_103);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_push(x_111, x_122);
x_124 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_43, 1, x_125);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_43);
lean_ctor_set(x_126, 1, x_95);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_127 = lean_ctor_get(x_43, 0);
x_128 = lean_ctor_get(x_43, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_43);
x_129 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_44);
lean_dec(x_5);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_Elab_Term_getMainModule___rarg(x_130);
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
x_134 = l_Array_empty___closed__1;
x_135 = lean_array_push(x_134, x_35);
x_136 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_137 = lean_array_push(x_135, x_136);
x_138 = l_Lean_mkTermIdFromIdent___closed__2;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_array_push(x_134, x_139);
x_141 = l_Lean_nullKind___closed__2;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_144 = lean_array_push(x_143, x_142);
x_145 = lean_array_push(x_144, x_136);
x_146 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_147 = lean_array_push(x_145, x_146);
x_148 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_149 = lean_array_push(x_147, x_148);
lean_inc(x_11);
x_150 = lean_array_push(x_134, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_151 = x_11;
} else {
 lean_dec_ref(x_11);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_141);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_134, x_152);
x_154 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_155 = lean_array_push(x_153, x_154);
x_156 = lean_array_push(x_155, x_128);
x_157 = l_Lean_Parser_Term_matchAlt___closed__2;
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_134, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_141);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_array_push(x_149, x_160);
x_162 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_127);
lean_ctor_set(x_164, 1, x_163);
if (lean_is_scalar(x_133)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_133;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_132);
return x_165;
}
}
else
{
uint8_t x_166; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_5);
x_166 = !lean_is_exclusive(x_42);
if (x_166 == 0)
{
return x_42;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_42, 0);
x_168 = lean_ctor_get(x_42, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_42);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_33, 0);
lean_inc(x_170);
lean_dec(x_33);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Syntax_isNone(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_171);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_175 = l_Lean_Elab_Term_throwError___rarg(x_11, x_174, x_5, x_6);
lean_dec(x_11);
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
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_3, x_181);
lean_dec(x_3);
x_183 = l_Lean_Elab_Term_mkExplicitBinder(x_171, x_180);
x_184 = lean_array_push(x_4, x_183);
x_3 = x_182;
x_4 = x_184;
goto _start;
}
}
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = l_Lean_mkAppStx___closed__3;
x_187 = lean_string_dec_eq(x_25, x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; lean_object* x_190; 
lean_ctor_set(x_15, 1, x_30);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_12);
lean_ctor_set(x_188, 1, x_17);
x_189 = 1;
lean_inc(x_188);
x_190 = l_Lean_Syntax_isTermId_x3f(x_188, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_188);
x_191 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_add(x_3, x_194);
lean_dec(x_3);
x_196 = l_Lean_mkHole(x_11);
lean_inc(x_192);
x_197 = l_Lean_Elab_Term_mkExplicitBinder(x_192, x_196);
x_198 = lean_array_push(x_4, x_197);
lean_inc(x_5);
x_199 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_195, x_198, x_5, x_193);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = !lean_is_exclusive(x_200);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_200, 1);
x_204 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_201);
lean_dec(x_5);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l_Lean_Elab_Term_getMainModule___rarg(x_205);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_208 = lean_ctor_get(x_206, 0);
lean_dec(x_208);
x_209 = l_Array_empty___closed__1;
x_210 = lean_array_push(x_209, x_192);
x_211 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_212 = lean_array_push(x_210, x_211);
x_213 = l_Lean_mkTermIdFromIdent___closed__2;
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_array_push(x_209, x_214);
x_216 = l_Lean_nullKind___closed__2;
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_219 = lean_array_push(x_218, x_217);
x_220 = lean_array_push(x_219, x_211);
x_221 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_222 = lean_array_push(x_220, x_221);
x_223 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_224 = lean_array_push(x_222, x_223);
lean_inc(x_11);
x_225 = lean_array_push(x_209, x_11);
x_226 = !lean_is_exclusive(x_11);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_227 = lean_ctor_get(x_11, 1);
lean_dec(x_227);
x_228 = lean_ctor_get(x_11, 0);
lean_dec(x_228);
lean_ctor_set(x_11, 1, x_225);
lean_ctor_set(x_11, 0, x_216);
x_229 = lean_array_push(x_209, x_11);
x_230 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_231 = lean_array_push(x_229, x_230);
x_232 = lean_array_push(x_231, x_203);
x_233 = l_Lean_Parser_Term_matchAlt___closed__2;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = lean_array_push(x_209, x_234);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_216);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_array_push(x_224, x_236);
x_238 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_200, 1, x_239);
lean_ctor_set(x_206, 0, x_200);
return x_206;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_11);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_216);
lean_ctor_set(x_240, 1, x_225);
x_241 = lean_array_push(x_209, x_240);
x_242 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_243 = lean_array_push(x_241, x_242);
x_244 = lean_array_push(x_243, x_203);
x_245 = l_Lean_Parser_Term_matchAlt___closed__2;
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = lean_array_push(x_209, x_246);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_216);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_array_push(x_224, x_248);
x_250 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
lean_ctor_set(x_200, 1, x_251);
lean_ctor_set(x_206, 0, x_200);
return x_206;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_252 = lean_ctor_get(x_206, 1);
lean_inc(x_252);
lean_dec(x_206);
x_253 = l_Array_empty___closed__1;
x_254 = lean_array_push(x_253, x_192);
x_255 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_256 = lean_array_push(x_254, x_255);
x_257 = l_Lean_mkTermIdFromIdent___closed__2;
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
x_259 = lean_array_push(x_253, x_258);
x_260 = l_Lean_nullKind___closed__2;
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_263 = lean_array_push(x_262, x_261);
x_264 = lean_array_push(x_263, x_255);
x_265 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_266 = lean_array_push(x_264, x_265);
x_267 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_268 = lean_array_push(x_266, x_267);
lean_inc(x_11);
x_269 = lean_array_push(x_253, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_270 = x_11;
} else {
 lean_dec_ref(x_11);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_array_push(x_253, x_271);
x_273 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_274 = lean_array_push(x_272, x_273);
x_275 = lean_array_push(x_274, x_203);
x_276 = l_Lean_Parser_Term_matchAlt___closed__2;
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = lean_array_push(x_253, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_260);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_array_push(x_268, x_279);
x_281 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
lean_ctor_set(x_200, 1, x_282);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_200);
lean_ctor_set(x_283, 1, x_252);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_284 = lean_ctor_get(x_200, 0);
x_285 = lean_ctor_get(x_200, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_200);
x_286 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_201);
lean_dec(x_5);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_288 = l_Lean_Elab_Term_getMainModule___rarg(x_287);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
x_291 = l_Array_empty___closed__1;
x_292 = lean_array_push(x_291, x_192);
x_293 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_294 = lean_array_push(x_292, x_293);
x_295 = l_Lean_mkTermIdFromIdent___closed__2;
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
x_297 = lean_array_push(x_291, x_296);
x_298 = l_Lean_nullKind___closed__2;
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_301 = lean_array_push(x_300, x_299);
x_302 = lean_array_push(x_301, x_293);
x_303 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_304 = lean_array_push(x_302, x_303);
x_305 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_306 = lean_array_push(x_304, x_305);
lean_inc(x_11);
x_307 = lean_array_push(x_291, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_308 = x_11;
} else {
 lean_dec_ref(x_11);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_298);
lean_ctor_set(x_309, 1, x_307);
x_310 = lean_array_push(x_291, x_309);
x_311 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_312 = lean_array_push(x_310, x_311);
x_313 = lean_array_push(x_312, x_285);
x_314 = l_Lean_Parser_Term_matchAlt___closed__2;
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = lean_array_push(x_291, x_315);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_298);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_array_push(x_306, x_317);
x_319 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_284);
lean_ctor_set(x_321, 1, x_320);
if (lean_is_scalar(x_290)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_290;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_289);
return x_322;
}
}
else
{
uint8_t x_323; 
lean_dec(x_192);
lean_dec(x_11);
lean_dec(x_5);
x_323 = !lean_is_exclusive(x_199);
if (x_323 == 0)
{
return x_199;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_199, 0);
x_325 = lean_ctor_get(x_199, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_199);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_dec(x_11);
x_327 = lean_ctor_get(x_190, 0);
lean_inc(x_327);
lean_dec(x_190);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = l_Lean_Syntax_isNone(x_329);
lean_dec(x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_dec(x_328);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_331 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_332 = l_Lean_Elab_Term_throwError___rarg(x_188, x_331, x_5, x_6);
lean_dec(x_188);
x_333 = !lean_is_exclusive(x_332);
if (x_333 == 0)
{
return x_332;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_332);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_337 = l_Lean_mkHole(x_188);
lean_dec(x_188);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_3, x_338);
lean_dec(x_3);
x_340 = l_Lean_Elab_Term_mkExplicitBinder(x_328, x_337);
x_341 = lean_array_push(x_4, x_340);
x_3 = x_339;
x_4 = x_341;
goto _start;
}
}
}
else
{
lean_object* x_343; uint8_t x_344; 
lean_dec(x_25);
x_343 = l_Lean_mkAppStx___closed__5;
x_344 = lean_string_dec_eq(x_22, x_343);
if (x_344 == 0)
{
lean_object* x_345; uint8_t x_346; lean_object* x_347; 
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_14, 1, x_186);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_12);
lean_ctor_set(x_345, 1, x_17);
x_346 = 1;
lean_inc(x_345);
x_347 = l_Lean_Syntax_isTermId_x3f(x_345, x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_345);
x_348 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_nat_add(x_3, x_351);
lean_dec(x_3);
x_353 = l_Lean_mkHole(x_11);
lean_inc(x_349);
x_354 = l_Lean_Elab_Term_mkExplicitBinder(x_349, x_353);
x_355 = lean_array_push(x_4, x_354);
lean_inc(x_5);
x_356 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_352, x_355, x_5, x_350);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = !lean_is_exclusive(x_357);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_360 = lean_ctor_get(x_357, 1);
x_361 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_358);
lean_dec(x_5);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = l_Lean_Elab_Term_getMainModule___rarg(x_362);
x_364 = !lean_is_exclusive(x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_365 = lean_ctor_get(x_363, 0);
lean_dec(x_365);
x_366 = l_Array_empty___closed__1;
x_367 = lean_array_push(x_366, x_349);
x_368 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_369 = lean_array_push(x_367, x_368);
x_370 = l_Lean_mkTermIdFromIdent___closed__2;
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
x_372 = lean_array_push(x_366, x_371);
x_373 = l_Lean_nullKind___closed__2;
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_376 = lean_array_push(x_375, x_374);
x_377 = lean_array_push(x_376, x_368);
x_378 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_379 = lean_array_push(x_377, x_378);
x_380 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_381 = lean_array_push(x_379, x_380);
lean_inc(x_11);
x_382 = lean_array_push(x_366, x_11);
x_383 = !lean_is_exclusive(x_11);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_384 = lean_ctor_get(x_11, 1);
lean_dec(x_384);
x_385 = lean_ctor_get(x_11, 0);
lean_dec(x_385);
lean_ctor_set(x_11, 1, x_382);
lean_ctor_set(x_11, 0, x_373);
x_386 = lean_array_push(x_366, x_11);
x_387 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_388 = lean_array_push(x_386, x_387);
x_389 = lean_array_push(x_388, x_360);
x_390 = l_Lean_Parser_Term_matchAlt___closed__2;
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_389);
x_392 = lean_array_push(x_366, x_391);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_373);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_array_push(x_381, x_393);
x_395 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
lean_ctor_set(x_357, 1, x_396);
lean_ctor_set(x_363, 0, x_357);
return x_363;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_11);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_373);
lean_ctor_set(x_397, 1, x_382);
x_398 = lean_array_push(x_366, x_397);
x_399 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_400 = lean_array_push(x_398, x_399);
x_401 = lean_array_push(x_400, x_360);
x_402 = l_Lean_Parser_Term_matchAlt___closed__2;
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_401);
x_404 = lean_array_push(x_366, x_403);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_373);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_array_push(x_381, x_405);
x_407 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_406);
lean_ctor_set(x_357, 1, x_408);
lean_ctor_set(x_363, 0, x_357);
return x_363;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_409 = lean_ctor_get(x_363, 1);
lean_inc(x_409);
lean_dec(x_363);
x_410 = l_Array_empty___closed__1;
x_411 = lean_array_push(x_410, x_349);
x_412 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_413 = lean_array_push(x_411, x_412);
x_414 = l_Lean_mkTermIdFromIdent___closed__2;
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
x_416 = lean_array_push(x_410, x_415);
x_417 = l_Lean_nullKind___closed__2;
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_420 = lean_array_push(x_419, x_418);
x_421 = lean_array_push(x_420, x_412);
x_422 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_423 = lean_array_push(x_421, x_422);
x_424 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_425 = lean_array_push(x_423, x_424);
lean_inc(x_11);
x_426 = lean_array_push(x_410, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_427 = x_11;
} else {
 lean_dec_ref(x_11);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_417);
lean_ctor_set(x_428, 1, x_426);
x_429 = lean_array_push(x_410, x_428);
x_430 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_431 = lean_array_push(x_429, x_430);
x_432 = lean_array_push(x_431, x_360);
x_433 = l_Lean_Parser_Term_matchAlt___closed__2;
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
x_435 = lean_array_push(x_410, x_434);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_417);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_array_push(x_425, x_436);
x_438 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_437);
lean_ctor_set(x_357, 1, x_439);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_357);
lean_ctor_set(x_440, 1, x_409);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_441 = lean_ctor_get(x_357, 0);
x_442 = lean_ctor_get(x_357, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_357);
x_443 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_358);
lean_dec(x_5);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
lean_dec(x_443);
x_445 = l_Lean_Elab_Term_getMainModule___rarg(x_444);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_447 = x_445;
} else {
 lean_dec_ref(x_445);
 x_447 = lean_box(0);
}
x_448 = l_Array_empty___closed__1;
x_449 = lean_array_push(x_448, x_349);
x_450 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_451 = lean_array_push(x_449, x_450);
x_452 = l_Lean_mkTermIdFromIdent___closed__2;
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_451);
x_454 = lean_array_push(x_448, x_453);
x_455 = l_Lean_nullKind___closed__2;
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
x_457 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_458 = lean_array_push(x_457, x_456);
x_459 = lean_array_push(x_458, x_450);
x_460 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_461 = lean_array_push(x_459, x_460);
x_462 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_463 = lean_array_push(x_461, x_462);
lean_inc(x_11);
x_464 = lean_array_push(x_448, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_465 = x_11;
} else {
 lean_dec_ref(x_11);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_455);
lean_ctor_set(x_466, 1, x_464);
x_467 = lean_array_push(x_448, x_466);
x_468 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_469 = lean_array_push(x_467, x_468);
x_470 = lean_array_push(x_469, x_442);
x_471 = l_Lean_Parser_Term_matchAlt___closed__2;
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_470);
x_473 = lean_array_push(x_448, x_472);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_455);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_array_push(x_463, x_474);
x_476 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_441);
lean_ctor_set(x_478, 1, x_477);
if (lean_is_scalar(x_447)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_447;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_446);
return x_479;
}
}
else
{
uint8_t x_480; 
lean_dec(x_349);
lean_dec(x_11);
lean_dec(x_5);
x_480 = !lean_is_exclusive(x_356);
if (x_480 == 0)
{
return x_356;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_356, 0);
x_482 = lean_ctor_get(x_356, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_356);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
lean_dec(x_11);
x_484 = lean_ctor_get(x_347, 0);
lean_inc(x_484);
lean_dec(x_347);
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_487 = l_Lean_Syntax_isNone(x_486);
lean_dec(x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; uint8_t x_490; 
lean_dec(x_485);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_488 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_489 = l_Lean_Elab_Term_throwError___rarg(x_345, x_488, x_5, x_6);
lean_dec(x_345);
x_490 = !lean_is_exclusive(x_489);
if (x_490 == 0)
{
return x_489;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_489, 0);
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_489);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_494 = l_Lean_mkHole(x_345);
lean_dec(x_345);
x_495 = lean_unsigned_to_nat(1u);
x_496 = lean_nat_add(x_3, x_495);
lean_dec(x_3);
x_497 = l_Lean_Elab_Term_mkExplicitBinder(x_485, x_494);
x_498 = lean_array_push(x_4, x_497);
x_3 = x_496;
x_4 = x_498;
goto _start;
}
}
}
else
{
lean_object* x_500; uint8_t x_501; 
lean_dec(x_22);
x_500 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_501 = lean_string_dec_eq(x_19, x_500);
if (x_501 == 0)
{
lean_object* x_502; uint8_t x_503; 
x_502 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_503 = lean_string_dec_eq(x_19, x_502);
if (x_503 == 0)
{
lean_object* x_504; uint8_t x_505; 
x_504 = l_Lean_mkHole___closed__1;
x_505 = lean_string_dec_eq(x_19, x_504);
if (x_505 == 0)
{
lean_object* x_506; uint8_t x_507; 
x_506 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_507 = lean_string_dec_eq(x_19, x_506);
if (x_507 == 0)
{
lean_object* x_508; uint8_t x_509; lean_object* x_510; 
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_14, 1, x_186);
lean_ctor_set(x_13, 1, x_343);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_12);
lean_ctor_set(x_508, 1, x_17);
x_509 = 1;
lean_inc(x_508);
x_510 = l_Lean_Syntax_isTermId_x3f(x_508, x_509);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_508);
x_511 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_unsigned_to_nat(1u);
x_515 = lean_nat_add(x_3, x_514);
lean_dec(x_3);
x_516 = l_Lean_mkHole(x_11);
lean_inc(x_512);
x_517 = l_Lean_Elab_Term_mkExplicitBinder(x_512, x_516);
x_518 = lean_array_push(x_4, x_517);
lean_inc(x_5);
x_519 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_515, x_518, x_5, x_513);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = !lean_is_exclusive(x_520);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_523 = lean_ctor_get(x_520, 1);
x_524 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_521);
lean_dec(x_5);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_526 = l_Lean_Elab_Term_getMainModule___rarg(x_525);
x_527 = !lean_is_exclusive(x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
x_528 = lean_ctor_get(x_526, 0);
lean_dec(x_528);
x_529 = l_Array_empty___closed__1;
x_530 = lean_array_push(x_529, x_512);
x_531 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_532 = lean_array_push(x_530, x_531);
x_533 = l_Lean_mkTermIdFromIdent___closed__2;
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_532);
x_535 = lean_array_push(x_529, x_534);
x_536 = l_Lean_nullKind___closed__2;
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_535);
x_538 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_539 = lean_array_push(x_538, x_537);
x_540 = lean_array_push(x_539, x_531);
x_541 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_542 = lean_array_push(x_540, x_541);
x_543 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_544 = lean_array_push(x_542, x_543);
lean_inc(x_11);
x_545 = lean_array_push(x_529, x_11);
x_546 = !lean_is_exclusive(x_11);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_547 = lean_ctor_get(x_11, 1);
lean_dec(x_547);
x_548 = lean_ctor_get(x_11, 0);
lean_dec(x_548);
lean_ctor_set(x_11, 1, x_545);
lean_ctor_set(x_11, 0, x_536);
x_549 = lean_array_push(x_529, x_11);
x_550 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_551 = lean_array_push(x_549, x_550);
x_552 = lean_array_push(x_551, x_523);
x_553 = l_Lean_Parser_Term_matchAlt___closed__2;
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_552);
x_555 = lean_array_push(x_529, x_554);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_536);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_array_push(x_544, x_556);
x_558 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
lean_ctor_set(x_520, 1, x_559);
lean_ctor_set(x_526, 0, x_520);
return x_526;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_11);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_536);
lean_ctor_set(x_560, 1, x_545);
x_561 = lean_array_push(x_529, x_560);
x_562 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_563 = lean_array_push(x_561, x_562);
x_564 = lean_array_push(x_563, x_523);
x_565 = l_Lean_Parser_Term_matchAlt___closed__2;
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_564);
x_567 = lean_array_push(x_529, x_566);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_536);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_array_push(x_544, x_568);
x_570 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
lean_ctor_set(x_520, 1, x_571);
lean_ctor_set(x_526, 0, x_520);
return x_526;
}
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_572 = lean_ctor_get(x_526, 1);
lean_inc(x_572);
lean_dec(x_526);
x_573 = l_Array_empty___closed__1;
x_574 = lean_array_push(x_573, x_512);
x_575 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_576 = lean_array_push(x_574, x_575);
x_577 = l_Lean_mkTermIdFromIdent___closed__2;
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_576);
x_579 = lean_array_push(x_573, x_578);
x_580 = l_Lean_nullKind___closed__2;
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_579);
x_582 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_583 = lean_array_push(x_582, x_581);
x_584 = lean_array_push(x_583, x_575);
x_585 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_586 = lean_array_push(x_584, x_585);
x_587 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_588 = lean_array_push(x_586, x_587);
lean_inc(x_11);
x_589 = lean_array_push(x_573, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_590 = x_11;
} else {
 lean_dec_ref(x_11);
 x_590 = lean_box(0);
}
if (lean_is_scalar(x_590)) {
 x_591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_591 = x_590;
}
lean_ctor_set(x_591, 0, x_580);
lean_ctor_set(x_591, 1, x_589);
x_592 = lean_array_push(x_573, x_591);
x_593 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_594 = lean_array_push(x_592, x_593);
x_595 = lean_array_push(x_594, x_523);
x_596 = l_Lean_Parser_Term_matchAlt___closed__2;
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_595);
x_598 = lean_array_push(x_573, x_597);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_580);
lean_ctor_set(x_599, 1, x_598);
x_600 = lean_array_push(x_588, x_599);
x_601 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_600);
lean_ctor_set(x_520, 1, x_602);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_520);
lean_ctor_set(x_603, 1, x_572);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_604 = lean_ctor_get(x_520, 0);
x_605 = lean_ctor_get(x_520, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_520);
x_606 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_521);
lean_dec(x_5);
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_608 = l_Lean_Elab_Term_getMainModule___rarg(x_607);
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
x_611 = l_Array_empty___closed__1;
x_612 = lean_array_push(x_611, x_512);
x_613 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_614 = lean_array_push(x_612, x_613);
x_615 = l_Lean_mkTermIdFromIdent___closed__2;
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_614);
x_617 = lean_array_push(x_611, x_616);
x_618 = l_Lean_nullKind___closed__2;
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_617);
x_620 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_621 = lean_array_push(x_620, x_619);
x_622 = lean_array_push(x_621, x_613);
x_623 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_624 = lean_array_push(x_622, x_623);
x_625 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_626 = lean_array_push(x_624, x_625);
lean_inc(x_11);
x_627 = lean_array_push(x_611, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_628 = x_11;
} else {
 lean_dec_ref(x_11);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_618);
lean_ctor_set(x_629, 1, x_627);
x_630 = lean_array_push(x_611, x_629);
x_631 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_632 = lean_array_push(x_630, x_631);
x_633 = lean_array_push(x_632, x_605);
x_634 = l_Lean_Parser_Term_matchAlt___closed__2;
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_633);
x_636 = lean_array_push(x_611, x_635);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_618);
lean_ctor_set(x_637, 1, x_636);
x_638 = lean_array_push(x_626, x_637);
x_639 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_638);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_604);
lean_ctor_set(x_641, 1, x_640);
if (lean_is_scalar(x_610)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_610;
}
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_609);
return x_642;
}
}
else
{
uint8_t x_643; 
lean_dec(x_512);
lean_dec(x_11);
lean_dec(x_5);
x_643 = !lean_is_exclusive(x_519);
if (x_643 == 0)
{
return x_519;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_519, 0);
x_645 = lean_ctor_get(x_519, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_519);
x_646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
return x_646;
}
}
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; 
lean_dec(x_11);
x_647 = lean_ctor_get(x_510, 0);
lean_inc(x_647);
lean_dec(x_510);
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = l_Lean_Syntax_isNone(x_649);
lean_dec(x_649);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; uint8_t x_653; 
lean_dec(x_648);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_651 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_652 = l_Lean_Elab_Term_throwError___rarg(x_508, x_651, x_5, x_6);
lean_dec(x_508);
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
return x_652;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_652, 0);
x_655 = lean_ctor_get(x_652, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_652);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_657 = l_Lean_mkHole(x_508);
lean_dec(x_508);
x_658 = lean_unsigned_to_nat(1u);
x_659 = lean_nat_add(x_3, x_658);
lean_dec(x_3);
x_660 = l_Lean_Elab_Term_mkExplicitBinder(x_648, x_657);
x_661 = lean_array_push(x_4, x_660);
x_3 = x_659;
x_4 = x_661;
goto _start;
}
}
}
else
{
lean_object* x_663; lean_object* x_664; uint8_t x_665; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_663 = lean_unsigned_to_nat(1u);
x_664 = l_Lean_Syntax_getArg(x_11, x_663);
x_665 = l_Lean_Syntax_isNone(x_664);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
x_666 = lean_unsigned_to_nat(0u);
x_667 = l_Lean_Syntax_getArg(x_664, x_666);
x_668 = l_Lean_Syntax_getArg(x_664, x_663);
lean_dec(x_664);
x_669 = l_Lean_Syntax_isNone(x_668);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; 
x_670 = l_Lean_Syntax_getArg(x_668, x_666);
lean_dec(x_668);
lean_inc(x_670);
x_671 = l_Lean_Syntax_getKind(x_670);
x_672 = lean_name_mk_string(x_16, x_30);
x_673 = lean_name_mk_string(x_672, x_186);
x_674 = lean_name_mk_string(x_673, x_343);
x_675 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_676 = lean_name_mk_string(x_674, x_675);
x_677 = lean_name_eq(x_671, x_676);
lean_dec(x_676);
lean_dec(x_671);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_670);
lean_dec(x_667);
x_678 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec(x_678);
x_681 = lean_nat_add(x_3, x_663);
lean_dec(x_3);
x_682 = l_Lean_mkHole(x_11);
lean_inc(x_679);
x_683 = l_Lean_Elab_Term_mkExplicitBinder(x_679, x_682);
x_684 = lean_array_push(x_4, x_683);
lean_inc(x_5);
x_685 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_681, x_684, x_5, x_680);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = !lean_is_exclusive(x_686);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_689 = lean_ctor_get(x_686, 1);
x_690 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_687);
lean_dec(x_5);
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
lean_dec(x_690);
x_692 = l_Lean_Elab_Term_getMainModule___rarg(x_691);
x_693 = !lean_is_exclusive(x_692);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; uint8_t x_712; 
x_694 = lean_ctor_get(x_692, 0);
lean_dec(x_694);
x_695 = l_Array_empty___closed__1;
x_696 = lean_array_push(x_695, x_679);
x_697 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_698 = lean_array_push(x_696, x_697);
x_699 = l_Lean_mkTermIdFromIdent___closed__2;
x_700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_701 = lean_array_push(x_695, x_700);
x_702 = l_Lean_nullKind___closed__2;
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
x_704 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_705 = lean_array_push(x_704, x_703);
x_706 = lean_array_push(x_705, x_697);
x_707 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_708 = lean_array_push(x_706, x_707);
x_709 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_710 = lean_array_push(x_708, x_709);
lean_inc(x_11);
x_711 = lean_array_push(x_695, x_11);
x_712 = !lean_is_exclusive(x_11);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_713 = lean_ctor_get(x_11, 1);
lean_dec(x_713);
x_714 = lean_ctor_get(x_11, 0);
lean_dec(x_714);
lean_ctor_set(x_11, 1, x_711);
lean_ctor_set(x_11, 0, x_702);
x_715 = lean_array_push(x_695, x_11);
x_716 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_717 = lean_array_push(x_715, x_716);
x_718 = lean_array_push(x_717, x_689);
x_719 = l_Lean_Parser_Term_matchAlt___closed__2;
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_718);
x_721 = lean_array_push(x_695, x_720);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_702);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_array_push(x_710, x_722);
x_724 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_723);
lean_ctor_set(x_686, 1, x_725);
lean_ctor_set(x_692, 0, x_686);
return x_692;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_11);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_702);
lean_ctor_set(x_726, 1, x_711);
x_727 = lean_array_push(x_695, x_726);
x_728 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_729 = lean_array_push(x_727, x_728);
x_730 = lean_array_push(x_729, x_689);
x_731 = l_Lean_Parser_Term_matchAlt___closed__2;
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_730);
x_733 = lean_array_push(x_695, x_732);
x_734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_734, 0, x_702);
lean_ctor_set(x_734, 1, x_733);
x_735 = lean_array_push(x_710, x_734);
x_736 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_735);
lean_ctor_set(x_686, 1, x_737);
lean_ctor_set(x_692, 0, x_686);
return x_692;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_738 = lean_ctor_get(x_692, 1);
lean_inc(x_738);
lean_dec(x_692);
x_739 = l_Array_empty___closed__1;
x_740 = lean_array_push(x_739, x_679);
x_741 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_742 = lean_array_push(x_740, x_741);
x_743 = l_Lean_mkTermIdFromIdent___closed__2;
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_742);
x_745 = lean_array_push(x_739, x_744);
x_746 = l_Lean_nullKind___closed__2;
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_745);
x_748 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_749 = lean_array_push(x_748, x_747);
x_750 = lean_array_push(x_749, x_741);
x_751 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_752 = lean_array_push(x_750, x_751);
x_753 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_754 = lean_array_push(x_752, x_753);
lean_inc(x_11);
x_755 = lean_array_push(x_739, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_756 = x_11;
} else {
 lean_dec_ref(x_11);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 2, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_746);
lean_ctor_set(x_757, 1, x_755);
x_758 = lean_array_push(x_739, x_757);
x_759 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_760 = lean_array_push(x_758, x_759);
x_761 = lean_array_push(x_760, x_689);
x_762 = l_Lean_Parser_Term_matchAlt___closed__2;
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_761);
x_764 = lean_array_push(x_739, x_763);
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_746);
lean_ctor_set(x_765, 1, x_764);
x_766 = lean_array_push(x_754, x_765);
x_767 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_766);
lean_ctor_set(x_686, 1, x_768);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_686);
lean_ctor_set(x_769, 1, x_738);
return x_769;
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_770 = lean_ctor_get(x_686, 0);
x_771 = lean_ctor_get(x_686, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_686);
x_772 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_687);
lean_dec(x_5);
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
lean_dec(x_772);
x_774 = l_Lean_Elab_Term_getMainModule___rarg(x_773);
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_776 = x_774;
} else {
 lean_dec_ref(x_774);
 x_776 = lean_box(0);
}
x_777 = l_Array_empty___closed__1;
x_778 = lean_array_push(x_777, x_679);
x_779 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_780 = lean_array_push(x_778, x_779);
x_781 = l_Lean_mkTermIdFromIdent___closed__2;
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_780);
x_783 = lean_array_push(x_777, x_782);
x_784 = l_Lean_nullKind___closed__2;
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_783);
x_786 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_787 = lean_array_push(x_786, x_785);
x_788 = lean_array_push(x_787, x_779);
x_789 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_790 = lean_array_push(x_788, x_789);
x_791 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_792 = lean_array_push(x_790, x_791);
lean_inc(x_11);
x_793 = lean_array_push(x_777, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_794 = x_11;
} else {
 lean_dec_ref(x_11);
 x_794 = lean_box(0);
}
if (lean_is_scalar(x_794)) {
 x_795 = lean_alloc_ctor(1, 2, 0);
} else {
 x_795 = x_794;
}
lean_ctor_set(x_795, 0, x_784);
lean_ctor_set(x_795, 1, x_793);
x_796 = lean_array_push(x_777, x_795);
x_797 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_798 = lean_array_push(x_796, x_797);
x_799 = lean_array_push(x_798, x_771);
x_800 = l_Lean_Parser_Term_matchAlt___closed__2;
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_799);
x_802 = lean_array_push(x_777, x_801);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_784);
lean_ctor_set(x_803, 1, x_802);
x_804 = lean_array_push(x_792, x_803);
x_805 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_805);
lean_ctor_set(x_806, 1, x_804);
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_770);
lean_ctor_set(x_807, 1, x_806);
if (lean_is_scalar(x_776)) {
 x_808 = lean_alloc_ctor(0, 2, 0);
} else {
 x_808 = x_776;
}
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_775);
return x_808;
}
}
else
{
uint8_t x_809; 
lean_dec(x_679);
lean_dec(x_11);
lean_dec(x_5);
x_809 = !lean_is_exclusive(x_685);
if (x_809 == 0)
{
return x_685;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_685, 0);
x_811 = lean_ctor_get(x_685, 1);
lean_inc(x_811);
lean_inc(x_810);
lean_dec(x_685);
x_812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_812, 0, x_810);
lean_ctor_set(x_812, 1, x_811);
return x_812;
}
}
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = l_Lean_Syntax_getArg(x_670, x_663);
lean_dec(x_670);
x_814 = l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(x_667, x_5, x_6);
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_813);
x_816 = lean_ctor_get(x_814, 1);
lean_inc(x_816);
lean_dec(x_814);
x_817 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_816);
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
lean_dec(x_817);
x_820 = lean_nat_add(x_3, x_663);
lean_dec(x_3);
x_821 = l_Lean_mkHole(x_11);
lean_inc(x_818);
x_822 = l_Lean_Elab_Term_mkExplicitBinder(x_818, x_821);
x_823 = lean_array_push(x_4, x_822);
lean_inc(x_5);
x_824 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_820, x_823, x_5, x_819);
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_825; lean_object* x_826; uint8_t x_827; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
x_827 = !lean_is_exclusive(x_825);
if (x_827 == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; 
x_828 = lean_ctor_get(x_825, 1);
x_829 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_826);
lean_dec(x_5);
x_830 = lean_ctor_get(x_829, 1);
lean_inc(x_830);
lean_dec(x_829);
x_831 = l_Lean_Elab_Term_getMainModule___rarg(x_830);
x_832 = !lean_is_exclusive(x_831);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; uint8_t x_851; 
x_833 = lean_ctor_get(x_831, 0);
lean_dec(x_833);
x_834 = l_Array_empty___closed__1;
x_835 = lean_array_push(x_834, x_818);
x_836 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_837 = lean_array_push(x_835, x_836);
x_838 = l_Lean_mkTermIdFromIdent___closed__2;
x_839 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_837);
x_840 = lean_array_push(x_834, x_839);
x_841 = l_Lean_nullKind___closed__2;
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_840);
x_843 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_844 = lean_array_push(x_843, x_842);
x_845 = lean_array_push(x_844, x_836);
x_846 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_847 = lean_array_push(x_845, x_846);
x_848 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_849 = lean_array_push(x_847, x_848);
lean_inc(x_11);
x_850 = lean_array_push(x_834, x_11);
x_851 = !lean_is_exclusive(x_11);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_852 = lean_ctor_get(x_11, 1);
lean_dec(x_852);
x_853 = lean_ctor_get(x_11, 0);
lean_dec(x_853);
lean_ctor_set(x_11, 1, x_850);
lean_ctor_set(x_11, 0, x_841);
x_854 = lean_array_push(x_834, x_11);
x_855 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_856 = lean_array_push(x_854, x_855);
x_857 = lean_array_push(x_856, x_828);
x_858 = l_Lean_Parser_Term_matchAlt___closed__2;
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_857);
x_860 = lean_array_push(x_834, x_859);
x_861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_861, 0, x_841);
lean_ctor_set(x_861, 1, x_860);
x_862 = lean_array_push(x_849, x_861);
x_863 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_862);
lean_ctor_set(x_825, 1, x_864);
lean_ctor_set(x_831, 0, x_825);
return x_831;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_11);
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_841);
lean_ctor_set(x_865, 1, x_850);
x_866 = lean_array_push(x_834, x_865);
x_867 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_868 = lean_array_push(x_866, x_867);
x_869 = lean_array_push(x_868, x_828);
x_870 = l_Lean_Parser_Term_matchAlt___closed__2;
x_871 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_869);
x_872 = lean_array_push(x_834, x_871);
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_841);
lean_ctor_set(x_873, 1, x_872);
x_874 = lean_array_push(x_849, x_873);
x_875 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_876, 0, x_875);
lean_ctor_set(x_876, 1, x_874);
lean_ctor_set(x_825, 1, x_876);
lean_ctor_set(x_831, 0, x_825);
return x_831;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_877 = lean_ctor_get(x_831, 1);
lean_inc(x_877);
lean_dec(x_831);
x_878 = l_Array_empty___closed__1;
x_879 = lean_array_push(x_878, x_818);
x_880 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_881 = lean_array_push(x_879, x_880);
x_882 = l_Lean_mkTermIdFromIdent___closed__2;
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_881);
x_884 = lean_array_push(x_878, x_883);
x_885 = l_Lean_nullKind___closed__2;
x_886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_884);
x_887 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_888 = lean_array_push(x_887, x_886);
x_889 = lean_array_push(x_888, x_880);
x_890 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_891 = lean_array_push(x_889, x_890);
x_892 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_893 = lean_array_push(x_891, x_892);
lean_inc(x_11);
x_894 = lean_array_push(x_878, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_895 = x_11;
} else {
 lean_dec_ref(x_11);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_885);
lean_ctor_set(x_896, 1, x_894);
x_897 = lean_array_push(x_878, x_896);
x_898 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_899 = lean_array_push(x_897, x_898);
x_900 = lean_array_push(x_899, x_828);
x_901 = l_Lean_Parser_Term_matchAlt___closed__2;
x_902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_900);
x_903 = lean_array_push(x_878, x_902);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_885);
lean_ctor_set(x_904, 1, x_903);
x_905 = lean_array_push(x_893, x_904);
x_906 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_907 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_905);
lean_ctor_set(x_825, 1, x_907);
x_908 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_908, 0, x_825);
lean_ctor_set(x_908, 1, x_877);
return x_908;
}
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_909 = lean_ctor_get(x_825, 0);
x_910 = lean_ctor_get(x_825, 1);
lean_inc(x_910);
lean_inc(x_909);
lean_dec(x_825);
x_911 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_826);
lean_dec(x_5);
x_912 = lean_ctor_get(x_911, 1);
lean_inc(x_912);
lean_dec(x_911);
x_913 = l_Lean_Elab_Term_getMainModule___rarg(x_912);
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_915 = x_913;
} else {
 lean_dec_ref(x_913);
 x_915 = lean_box(0);
}
x_916 = l_Array_empty___closed__1;
x_917 = lean_array_push(x_916, x_818);
x_918 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_919 = lean_array_push(x_917, x_918);
x_920 = l_Lean_mkTermIdFromIdent___closed__2;
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_919);
x_922 = lean_array_push(x_916, x_921);
x_923 = l_Lean_nullKind___closed__2;
x_924 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_922);
x_925 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_926 = lean_array_push(x_925, x_924);
x_927 = lean_array_push(x_926, x_918);
x_928 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_929 = lean_array_push(x_927, x_928);
x_930 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_931 = lean_array_push(x_929, x_930);
lean_inc(x_11);
x_932 = lean_array_push(x_916, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_933 = x_11;
} else {
 lean_dec_ref(x_11);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_923);
lean_ctor_set(x_934, 1, x_932);
x_935 = lean_array_push(x_916, x_934);
x_936 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_937 = lean_array_push(x_935, x_936);
x_938 = lean_array_push(x_937, x_910);
x_939 = l_Lean_Parser_Term_matchAlt___closed__2;
x_940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_940, 0, x_939);
lean_ctor_set(x_940, 1, x_938);
x_941 = lean_array_push(x_916, x_940);
x_942 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_942, 0, x_923);
lean_ctor_set(x_942, 1, x_941);
x_943 = lean_array_push(x_931, x_942);
x_944 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_945 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_945, 0, x_944);
lean_ctor_set(x_945, 1, x_943);
x_946 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_946, 0, x_909);
lean_ctor_set(x_946, 1, x_945);
if (lean_is_scalar(x_915)) {
 x_947 = lean_alloc_ctor(0, 2, 0);
} else {
 x_947 = x_915;
}
lean_ctor_set(x_947, 0, x_946);
lean_ctor_set(x_947, 1, x_914);
return x_947;
}
}
else
{
uint8_t x_948; 
lean_dec(x_818);
lean_dec(x_11);
lean_dec(x_5);
x_948 = !lean_is_exclusive(x_824);
if (x_948 == 0)
{
return x_824;
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_949 = lean_ctor_get(x_824, 0);
x_950 = lean_ctor_get(x_824, 1);
lean_inc(x_950);
lean_inc(x_949);
lean_dec(x_824);
x_951 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_951, 0, x_949);
lean_ctor_set(x_951, 1, x_950);
return x_951;
}
}
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_11);
x_952 = lean_ctor_get(x_814, 1);
lean_inc(x_952);
lean_dec(x_814);
x_953 = lean_ctor_get(x_815, 0);
lean_inc(x_953);
lean_dec(x_815);
x_954 = lean_nat_add(x_3, x_663);
lean_dec(x_3);
x_955 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(x_813, x_666, x_953);
x_956 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_955, x_955, x_666, x_4);
lean_dec(x_955);
x_3 = x_954;
x_4 = x_956;
x_6 = x_952;
goto _start;
}
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_dec(x_668);
lean_dec(x_667);
x_958 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_nat_add(x_3, x_663);
lean_dec(x_3);
x_962 = l_Lean_mkHole(x_11);
lean_inc(x_959);
x_963 = l_Lean_Elab_Term_mkExplicitBinder(x_959, x_962);
x_964 = lean_array_push(x_4, x_963);
lean_inc(x_5);
x_965 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_961, x_964, x_5, x_960);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; uint8_t x_968; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = !lean_is_exclusive(x_966);
if (x_968 == 0)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; 
x_969 = lean_ctor_get(x_966, 1);
x_970 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_967);
lean_dec(x_5);
x_971 = lean_ctor_get(x_970, 1);
lean_inc(x_971);
lean_dec(x_970);
x_972 = l_Lean_Elab_Term_getMainModule___rarg(x_971);
x_973 = !lean_is_exclusive(x_972);
if (x_973 == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; uint8_t x_992; 
x_974 = lean_ctor_get(x_972, 0);
lean_dec(x_974);
x_975 = l_Array_empty___closed__1;
x_976 = lean_array_push(x_975, x_959);
x_977 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_978 = lean_array_push(x_976, x_977);
x_979 = l_Lean_mkTermIdFromIdent___closed__2;
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_978);
x_981 = lean_array_push(x_975, x_980);
x_982 = l_Lean_nullKind___closed__2;
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_981);
x_984 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_985 = lean_array_push(x_984, x_983);
x_986 = lean_array_push(x_985, x_977);
x_987 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_988 = lean_array_push(x_986, x_987);
x_989 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_990 = lean_array_push(x_988, x_989);
lean_inc(x_11);
x_991 = lean_array_push(x_975, x_11);
x_992 = !lean_is_exclusive(x_11);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_993 = lean_ctor_get(x_11, 1);
lean_dec(x_993);
x_994 = lean_ctor_get(x_11, 0);
lean_dec(x_994);
lean_ctor_set(x_11, 1, x_991);
lean_ctor_set(x_11, 0, x_982);
x_995 = lean_array_push(x_975, x_11);
x_996 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_997 = lean_array_push(x_995, x_996);
x_998 = lean_array_push(x_997, x_969);
x_999 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_998);
x_1001 = lean_array_push(x_975, x_1000);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_982);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_array_push(x_990, x_1002);
x_1004 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_1003);
lean_ctor_set(x_966, 1, x_1005);
lean_ctor_set(x_972, 0, x_966);
return x_972;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
lean_dec(x_11);
x_1006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1006, 0, x_982);
lean_ctor_set(x_1006, 1, x_991);
x_1007 = lean_array_push(x_975, x_1006);
x_1008 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1009 = lean_array_push(x_1007, x_1008);
x_1010 = lean_array_push(x_1009, x_969);
x_1011 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_1010);
x_1013 = lean_array_push(x_975, x_1012);
x_1014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1014, 0, x_982);
lean_ctor_set(x_1014, 1, x_1013);
x_1015 = lean_array_push(x_990, x_1014);
x_1016 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1015);
lean_ctor_set(x_966, 1, x_1017);
lean_ctor_set(x_972, 0, x_966);
return x_972;
}
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1018 = lean_ctor_get(x_972, 1);
lean_inc(x_1018);
lean_dec(x_972);
x_1019 = l_Array_empty___closed__1;
x_1020 = lean_array_push(x_1019, x_959);
x_1021 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1022 = lean_array_push(x_1020, x_1021);
x_1023 = l_Lean_mkTermIdFromIdent___closed__2;
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_1022);
x_1025 = lean_array_push(x_1019, x_1024);
x_1026 = l_Lean_nullKind___closed__2;
x_1027 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1027, 0, x_1026);
lean_ctor_set(x_1027, 1, x_1025);
x_1028 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1029 = lean_array_push(x_1028, x_1027);
x_1030 = lean_array_push(x_1029, x_1021);
x_1031 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1032 = lean_array_push(x_1030, x_1031);
x_1033 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1034 = lean_array_push(x_1032, x_1033);
lean_inc(x_11);
x_1035 = lean_array_push(x_1019, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1036 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1036 = lean_box(0);
}
if (lean_is_scalar(x_1036)) {
 x_1037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1037 = x_1036;
}
lean_ctor_set(x_1037, 0, x_1026);
lean_ctor_set(x_1037, 1, x_1035);
x_1038 = lean_array_push(x_1019, x_1037);
x_1039 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1040 = lean_array_push(x_1038, x_1039);
x_1041 = lean_array_push(x_1040, x_969);
x_1042 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1043 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_1041);
x_1044 = lean_array_push(x_1019, x_1043);
x_1045 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1045, 0, x_1026);
lean_ctor_set(x_1045, 1, x_1044);
x_1046 = lean_array_push(x_1034, x_1045);
x_1047 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1048 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1048, 0, x_1047);
lean_ctor_set(x_1048, 1, x_1046);
lean_ctor_set(x_966, 1, x_1048);
x_1049 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1049, 0, x_966);
lean_ctor_set(x_1049, 1, x_1018);
return x_1049;
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1050 = lean_ctor_get(x_966, 0);
x_1051 = lean_ctor_get(x_966, 1);
lean_inc(x_1051);
lean_inc(x_1050);
lean_dec(x_966);
x_1052 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_967);
lean_dec(x_5);
x_1053 = lean_ctor_get(x_1052, 1);
lean_inc(x_1053);
lean_dec(x_1052);
x_1054 = l_Lean_Elab_Term_getMainModule___rarg(x_1053);
x_1055 = lean_ctor_get(x_1054, 1);
lean_inc(x_1055);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1056 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1056 = lean_box(0);
}
x_1057 = l_Array_empty___closed__1;
x_1058 = lean_array_push(x_1057, x_959);
x_1059 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1060 = lean_array_push(x_1058, x_1059);
x_1061 = l_Lean_mkTermIdFromIdent___closed__2;
x_1062 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_1060);
x_1063 = lean_array_push(x_1057, x_1062);
x_1064 = l_Lean_nullKind___closed__2;
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_1063);
x_1066 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1067 = lean_array_push(x_1066, x_1065);
x_1068 = lean_array_push(x_1067, x_1059);
x_1069 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1070 = lean_array_push(x_1068, x_1069);
x_1071 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1072 = lean_array_push(x_1070, x_1071);
lean_inc(x_11);
x_1073 = lean_array_push(x_1057, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1074 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1074 = lean_box(0);
}
if (lean_is_scalar(x_1074)) {
 x_1075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1075 = x_1074;
}
lean_ctor_set(x_1075, 0, x_1064);
lean_ctor_set(x_1075, 1, x_1073);
x_1076 = lean_array_push(x_1057, x_1075);
x_1077 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1078 = lean_array_push(x_1076, x_1077);
x_1079 = lean_array_push(x_1078, x_1051);
x_1080 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1081 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1081, 0, x_1080);
lean_ctor_set(x_1081, 1, x_1079);
x_1082 = lean_array_push(x_1057, x_1081);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1064);
lean_ctor_set(x_1083, 1, x_1082);
x_1084 = lean_array_push(x_1072, x_1083);
x_1085 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1086 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1086, 0, x_1085);
lean_ctor_set(x_1086, 1, x_1084);
x_1087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1087, 0, x_1050);
lean_ctor_set(x_1087, 1, x_1086);
if (lean_is_scalar(x_1056)) {
 x_1088 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1088 = x_1056;
}
lean_ctor_set(x_1088, 0, x_1087);
lean_ctor_set(x_1088, 1, x_1055);
return x_1088;
}
}
else
{
uint8_t x_1089; 
lean_dec(x_959);
lean_dec(x_11);
lean_dec(x_5);
x_1089 = !lean_is_exclusive(x_965);
if (x_1089 == 0)
{
return x_965;
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1090 = lean_ctor_get(x_965, 0);
x_1091 = lean_ctor_get(x_965, 1);
lean_inc(x_1091);
lean_inc(x_1090);
lean_dec(x_965);
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
return x_1092;
}
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_664);
x_1093 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
lean_dec(x_1093);
x_1096 = lean_nat_add(x_3, x_663);
lean_dec(x_3);
x_1097 = l_Lean_mkHole(x_11);
lean_inc(x_1094);
x_1098 = l_Lean_Elab_Term_mkExplicitBinder(x_1094, x_1097);
x_1099 = lean_array_push(x_4, x_1098);
lean_inc(x_5);
x_1100 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1096, x_1099, x_5, x_1095);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; uint8_t x_1103; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = !lean_is_exclusive(x_1101);
if (x_1103 == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; uint8_t x_1108; 
x_1104 = lean_ctor_get(x_1101, 1);
x_1105 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1102);
lean_dec(x_5);
x_1106 = lean_ctor_get(x_1105, 1);
lean_inc(x_1106);
lean_dec(x_1105);
x_1107 = l_Lean_Elab_Term_getMainModule___rarg(x_1106);
x_1108 = !lean_is_exclusive(x_1107);
if (x_1108 == 0)
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; uint8_t x_1127; 
x_1109 = lean_ctor_get(x_1107, 0);
lean_dec(x_1109);
x_1110 = l_Array_empty___closed__1;
x_1111 = lean_array_push(x_1110, x_1094);
x_1112 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1113 = lean_array_push(x_1111, x_1112);
x_1114 = l_Lean_mkTermIdFromIdent___closed__2;
x_1115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1115, 0, x_1114);
lean_ctor_set(x_1115, 1, x_1113);
x_1116 = lean_array_push(x_1110, x_1115);
x_1117 = l_Lean_nullKind___closed__2;
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_1117);
lean_ctor_set(x_1118, 1, x_1116);
x_1119 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1120 = lean_array_push(x_1119, x_1118);
x_1121 = lean_array_push(x_1120, x_1112);
x_1122 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1123 = lean_array_push(x_1121, x_1122);
x_1124 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1125 = lean_array_push(x_1123, x_1124);
lean_inc(x_11);
x_1126 = lean_array_push(x_1110, x_11);
x_1127 = !lean_is_exclusive(x_11);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1128 = lean_ctor_get(x_11, 1);
lean_dec(x_1128);
x_1129 = lean_ctor_get(x_11, 0);
lean_dec(x_1129);
lean_ctor_set(x_11, 1, x_1126);
lean_ctor_set(x_11, 0, x_1117);
x_1130 = lean_array_push(x_1110, x_11);
x_1131 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1132 = lean_array_push(x_1130, x_1131);
x_1133 = lean_array_push(x_1132, x_1104);
x_1134 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1135, 0, x_1134);
lean_ctor_set(x_1135, 1, x_1133);
x_1136 = lean_array_push(x_1110, x_1135);
x_1137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1137, 0, x_1117);
lean_ctor_set(x_1137, 1, x_1136);
x_1138 = lean_array_push(x_1125, x_1137);
x_1139 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1139);
lean_ctor_set(x_1140, 1, x_1138);
lean_ctor_set(x_1101, 1, x_1140);
lean_ctor_set(x_1107, 0, x_1101);
return x_1107;
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_11);
x_1141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1141, 0, x_1117);
lean_ctor_set(x_1141, 1, x_1126);
x_1142 = lean_array_push(x_1110, x_1141);
x_1143 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1144 = lean_array_push(x_1142, x_1143);
x_1145 = lean_array_push(x_1144, x_1104);
x_1146 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1147, 0, x_1146);
lean_ctor_set(x_1147, 1, x_1145);
x_1148 = lean_array_push(x_1110, x_1147);
x_1149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1149, 0, x_1117);
lean_ctor_set(x_1149, 1, x_1148);
x_1150 = lean_array_push(x_1125, x_1149);
x_1151 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1152, 0, x_1151);
lean_ctor_set(x_1152, 1, x_1150);
lean_ctor_set(x_1101, 1, x_1152);
lean_ctor_set(x_1107, 0, x_1101);
return x_1107;
}
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
x_1153 = lean_ctor_get(x_1107, 1);
lean_inc(x_1153);
lean_dec(x_1107);
x_1154 = l_Array_empty___closed__1;
x_1155 = lean_array_push(x_1154, x_1094);
x_1156 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1157 = lean_array_push(x_1155, x_1156);
x_1158 = l_Lean_mkTermIdFromIdent___closed__2;
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1158);
lean_ctor_set(x_1159, 1, x_1157);
x_1160 = lean_array_push(x_1154, x_1159);
x_1161 = l_Lean_nullKind___closed__2;
x_1162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1162, 0, x_1161);
lean_ctor_set(x_1162, 1, x_1160);
x_1163 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1164 = lean_array_push(x_1163, x_1162);
x_1165 = lean_array_push(x_1164, x_1156);
x_1166 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1167 = lean_array_push(x_1165, x_1166);
x_1168 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1169 = lean_array_push(x_1167, x_1168);
lean_inc(x_11);
x_1170 = lean_array_push(x_1154, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1171 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1161);
lean_ctor_set(x_1172, 1, x_1170);
x_1173 = lean_array_push(x_1154, x_1172);
x_1174 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1175 = lean_array_push(x_1173, x_1174);
x_1176 = lean_array_push(x_1175, x_1104);
x_1177 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1176);
x_1179 = lean_array_push(x_1154, x_1178);
x_1180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1180, 0, x_1161);
lean_ctor_set(x_1180, 1, x_1179);
x_1181 = lean_array_push(x_1169, x_1180);
x_1182 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1182);
lean_ctor_set(x_1183, 1, x_1181);
lean_ctor_set(x_1101, 1, x_1183);
x_1184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1184, 0, x_1101);
lean_ctor_set(x_1184, 1, x_1153);
return x_1184;
}
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
x_1185 = lean_ctor_get(x_1101, 0);
x_1186 = lean_ctor_get(x_1101, 1);
lean_inc(x_1186);
lean_inc(x_1185);
lean_dec(x_1101);
x_1187 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1102);
lean_dec(x_5);
x_1188 = lean_ctor_get(x_1187, 1);
lean_inc(x_1188);
lean_dec(x_1187);
x_1189 = l_Lean_Elab_Term_getMainModule___rarg(x_1188);
x_1190 = lean_ctor_get(x_1189, 1);
lean_inc(x_1190);
if (lean_is_exclusive(x_1189)) {
 lean_ctor_release(x_1189, 0);
 lean_ctor_release(x_1189, 1);
 x_1191 = x_1189;
} else {
 lean_dec_ref(x_1189);
 x_1191 = lean_box(0);
}
x_1192 = l_Array_empty___closed__1;
x_1193 = lean_array_push(x_1192, x_1094);
x_1194 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1195 = lean_array_push(x_1193, x_1194);
x_1196 = l_Lean_mkTermIdFromIdent___closed__2;
x_1197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1197, 0, x_1196);
lean_ctor_set(x_1197, 1, x_1195);
x_1198 = lean_array_push(x_1192, x_1197);
x_1199 = l_Lean_nullKind___closed__2;
x_1200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1200, 0, x_1199);
lean_ctor_set(x_1200, 1, x_1198);
x_1201 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1202 = lean_array_push(x_1201, x_1200);
x_1203 = lean_array_push(x_1202, x_1194);
x_1204 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1205 = lean_array_push(x_1203, x_1204);
x_1206 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1207 = lean_array_push(x_1205, x_1206);
lean_inc(x_11);
x_1208 = lean_array_push(x_1192, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1209 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1209 = lean_box(0);
}
if (lean_is_scalar(x_1209)) {
 x_1210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1210 = x_1209;
}
lean_ctor_set(x_1210, 0, x_1199);
lean_ctor_set(x_1210, 1, x_1208);
x_1211 = lean_array_push(x_1192, x_1210);
x_1212 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1213 = lean_array_push(x_1211, x_1212);
x_1214 = lean_array_push(x_1213, x_1186);
x_1215 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1216, 0, x_1215);
lean_ctor_set(x_1216, 1, x_1214);
x_1217 = lean_array_push(x_1192, x_1216);
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1199);
lean_ctor_set(x_1218, 1, x_1217);
x_1219 = lean_array_push(x_1207, x_1218);
x_1220 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1222, 0, x_1185);
lean_ctor_set(x_1222, 1, x_1221);
if (lean_is_scalar(x_1191)) {
 x_1223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1223 = x_1191;
}
lean_ctor_set(x_1223, 0, x_1222);
lean_ctor_set(x_1223, 1, x_1190);
return x_1223;
}
}
else
{
uint8_t x_1224; 
lean_dec(x_1094);
lean_dec(x_11);
lean_dec(x_5);
x_1224 = !lean_is_exclusive(x_1100);
if (x_1224 == 0)
{
return x_1100;
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1225 = lean_ctor_get(x_1100, 0);
x_1226 = lean_ctor_get(x_1100, 1);
lean_inc(x_1226);
lean_inc(x_1225);
lean_dec(x_1100);
x_1227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1227, 0, x_1225);
lean_ctor_set(x_1227, 1, x_1226);
return x_1227;
}
}
}
}
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1228 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1229 = lean_ctor_get(x_1228, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1228, 1);
lean_inc(x_1230);
lean_dec(x_1228);
x_1231 = lean_unsigned_to_nat(1u);
x_1232 = lean_nat_add(x_3, x_1231);
lean_dec(x_3);
x_1233 = l_Lean_Elab_Term_mkExplicitBinder(x_1229, x_11);
x_1234 = lean_array_push(x_4, x_1233);
x_3 = x_1232;
x_4 = x_1234;
x_6 = x_1230;
goto _start;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1236 = lean_unsigned_to_nat(1u);
x_1237 = lean_nat_add(x_3, x_1236);
lean_dec(x_3);
x_1238 = lean_array_push(x_4, x_11);
x_3 = x_1237;
x_4 = x_1238;
goto _start;
}
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1240 = lean_unsigned_to_nat(1u);
x_1241 = lean_nat_add(x_3, x_1240);
lean_dec(x_3);
x_1242 = lean_array_push(x_4, x_11);
x_3 = x_1241;
x_4 = x_1242;
goto _start;
}
}
}
}
}
else
{
lean_object* x_1244; size_t x_1245; lean_object* x_1246; uint8_t x_1247; 
x_1244 = lean_ctor_get(x_15, 1);
x_1245 = lean_ctor_get_usize(x_15, 2);
lean_inc(x_1244);
lean_dec(x_15);
x_1246 = l_Lean_mkAppStx___closed__1;
x_1247 = lean_string_dec_eq(x_1244, x_1246);
lean_dec(x_1244);
if (x_1247 == 0)
{
uint8_t x_1248; lean_object* x_1249; 
lean_free_object(x_14);
lean_dec(x_25);
lean_free_object(x_13);
lean_dec(x_22);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1248 = 1;
lean_inc(x_11);
x_1249 = l_Lean_Syntax_isTermId_x3f(x_11, x_1248);
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
x_1250 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1251 = lean_ctor_get(x_1250, 0);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1250, 1);
lean_inc(x_1252);
lean_dec(x_1250);
x_1253 = lean_unsigned_to_nat(1u);
x_1254 = lean_nat_add(x_3, x_1253);
lean_dec(x_3);
x_1255 = l_Lean_mkHole(x_11);
lean_inc(x_1251);
x_1256 = l_Lean_Elab_Term_mkExplicitBinder(x_1251, x_1255);
x_1257 = lean_array_push(x_4, x_1256);
lean_inc(x_5);
x_1258 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1254, x_1257, x_5, x_1252);
if (lean_obj_tag(x_1258) == 0)
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
x_1259 = lean_ctor_get(x_1258, 0);
lean_inc(x_1259);
x_1260 = lean_ctor_get(x_1258, 1);
lean_inc(x_1260);
lean_dec(x_1258);
x_1261 = lean_ctor_get(x_1259, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1259, 1);
lean_inc(x_1262);
if (lean_is_exclusive(x_1259)) {
 lean_ctor_release(x_1259, 0);
 lean_ctor_release(x_1259, 1);
 x_1263 = x_1259;
} else {
 lean_dec_ref(x_1259);
 x_1263 = lean_box(0);
}
x_1264 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1260);
lean_dec(x_5);
x_1265 = lean_ctor_get(x_1264, 1);
lean_inc(x_1265);
lean_dec(x_1264);
x_1266 = l_Lean_Elab_Term_getMainModule___rarg(x_1265);
x_1267 = lean_ctor_get(x_1266, 1);
lean_inc(x_1267);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 lean_ctor_release(x_1266, 1);
 x_1268 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1268 = lean_box(0);
}
x_1269 = l_Array_empty___closed__1;
x_1270 = lean_array_push(x_1269, x_1251);
x_1271 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1272 = lean_array_push(x_1270, x_1271);
x_1273 = l_Lean_mkTermIdFromIdent___closed__2;
x_1274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1274, 0, x_1273);
lean_ctor_set(x_1274, 1, x_1272);
x_1275 = lean_array_push(x_1269, x_1274);
x_1276 = l_Lean_nullKind___closed__2;
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1276);
lean_ctor_set(x_1277, 1, x_1275);
x_1278 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1279 = lean_array_push(x_1278, x_1277);
x_1280 = lean_array_push(x_1279, x_1271);
x_1281 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1282 = lean_array_push(x_1280, x_1281);
x_1283 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1284 = lean_array_push(x_1282, x_1283);
lean_inc(x_11);
x_1285 = lean_array_push(x_1269, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1286 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1286 = lean_box(0);
}
if (lean_is_scalar(x_1286)) {
 x_1287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1287 = x_1286;
}
lean_ctor_set(x_1287, 0, x_1276);
lean_ctor_set(x_1287, 1, x_1285);
x_1288 = lean_array_push(x_1269, x_1287);
x_1289 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1290 = lean_array_push(x_1288, x_1289);
x_1291 = lean_array_push(x_1290, x_1262);
x_1292 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1293, 0, x_1292);
lean_ctor_set(x_1293, 1, x_1291);
x_1294 = lean_array_push(x_1269, x_1293);
x_1295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1295, 0, x_1276);
lean_ctor_set(x_1295, 1, x_1294);
x_1296 = lean_array_push(x_1284, x_1295);
x_1297 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1298, 0, x_1297);
lean_ctor_set(x_1298, 1, x_1296);
if (lean_is_scalar(x_1263)) {
 x_1299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1299 = x_1263;
}
lean_ctor_set(x_1299, 0, x_1261);
lean_ctor_set(x_1299, 1, x_1298);
if (lean_is_scalar(x_1268)) {
 x_1300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1300 = x_1268;
}
lean_ctor_set(x_1300, 0, x_1299);
lean_ctor_set(x_1300, 1, x_1267);
return x_1300;
}
else
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
lean_dec(x_1251);
lean_dec(x_11);
lean_dec(x_5);
x_1301 = lean_ctor_get(x_1258, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1258, 1);
lean_inc(x_1302);
if (lean_is_exclusive(x_1258)) {
 lean_ctor_release(x_1258, 0);
 lean_ctor_release(x_1258, 1);
 x_1303 = x_1258;
} else {
 lean_dec_ref(x_1258);
 x_1303 = lean_box(0);
}
if (lean_is_scalar(x_1303)) {
 x_1304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1304 = x_1303;
}
lean_ctor_set(x_1304, 0, x_1301);
lean_ctor_set(x_1304, 1, x_1302);
return x_1304;
}
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; 
x_1305 = lean_ctor_get(x_1249, 0);
lean_inc(x_1305);
lean_dec(x_1249);
x_1306 = lean_ctor_get(x_1305, 0);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1305, 1);
lean_inc(x_1307);
lean_dec(x_1305);
x_1308 = l_Lean_Syntax_isNone(x_1307);
lean_dec(x_1307);
if (x_1308 == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1306);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1309 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_1310 = l_Lean_Elab_Term_throwError___rarg(x_11, x_1309, x_5, x_6);
lean_dec(x_11);
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1310, 1);
lean_inc(x_1312);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 lean_ctor_release(x_1310, 1);
 x_1313 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1313)) {
 x_1314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1314 = x_1313;
}
lean_ctor_set(x_1314, 0, x_1311);
lean_ctor_set(x_1314, 1, x_1312);
return x_1314;
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1315 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_1316 = lean_unsigned_to_nat(1u);
x_1317 = lean_nat_add(x_3, x_1316);
lean_dec(x_3);
x_1318 = l_Lean_Elab_Term_mkExplicitBinder(x_1306, x_1315);
x_1319 = lean_array_push(x_4, x_1318);
x_3 = x_1317;
x_4 = x_1319;
goto _start;
}
}
}
else
{
lean_object* x_1321; uint8_t x_1322; 
x_1321 = l_Lean_mkAppStx___closed__3;
x_1322 = lean_string_dec_eq(x_25, x_1321);
if (x_1322 == 0)
{
lean_object* x_1323; lean_object* x_1324; uint8_t x_1325; lean_object* x_1326; 
x_1323 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1323, 0, x_16);
lean_ctor_set(x_1323, 1, x_1246);
lean_ctor_set_usize(x_1323, 2, x_1245);
lean_ctor_set(x_14, 0, x_1323);
x_1324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1324, 0, x_12);
lean_ctor_set(x_1324, 1, x_17);
x_1325 = 1;
lean_inc(x_1324);
x_1326 = l_Lean_Syntax_isTermId_x3f(x_1324, x_1325);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
lean_dec(x_1324);
x_1327 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1328 = lean_ctor_get(x_1327, 0);
lean_inc(x_1328);
x_1329 = lean_ctor_get(x_1327, 1);
lean_inc(x_1329);
lean_dec(x_1327);
x_1330 = lean_unsigned_to_nat(1u);
x_1331 = lean_nat_add(x_3, x_1330);
lean_dec(x_3);
x_1332 = l_Lean_mkHole(x_11);
lean_inc(x_1328);
x_1333 = l_Lean_Elab_Term_mkExplicitBinder(x_1328, x_1332);
x_1334 = lean_array_push(x_4, x_1333);
lean_inc(x_5);
x_1335 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1331, x_1334, x_5, x_1329);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1335, 1);
lean_inc(x_1337);
lean_dec(x_1335);
x_1338 = lean_ctor_get(x_1336, 0);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1336, 1);
lean_inc(x_1339);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1340 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1340 = lean_box(0);
}
x_1341 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1337);
lean_dec(x_5);
x_1342 = lean_ctor_get(x_1341, 1);
lean_inc(x_1342);
lean_dec(x_1341);
x_1343 = l_Lean_Elab_Term_getMainModule___rarg(x_1342);
x_1344 = lean_ctor_get(x_1343, 1);
lean_inc(x_1344);
if (lean_is_exclusive(x_1343)) {
 lean_ctor_release(x_1343, 0);
 lean_ctor_release(x_1343, 1);
 x_1345 = x_1343;
} else {
 lean_dec_ref(x_1343);
 x_1345 = lean_box(0);
}
x_1346 = l_Array_empty___closed__1;
x_1347 = lean_array_push(x_1346, x_1328);
x_1348 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1349 = lean_array_push(x_1347, x_1348);
x_1350 = l_Lean_mkTermIdFromIdent___closed__2;
x_1351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1351, 0, x_1350);
lean_ctor_set(x_1351, 1, x_1349);
x_1352 = lean_array_push(x_1346, x_1351);
x_1353 = l_Lean_nullKind___closed__2;
x_1354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1354, 0, x_1353);
lean_ctor_set(x_1354, 1, x_1352);
x_1355 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1356 = lean_array_push(x_1355, x_1354);
x_1357 = lean_array_push(x_1356, x_1348);
x_1358 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1359 = lean_array_push(x_1357, x_1358);
x_1360 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1361 = lean_array_push(x_1359, x_1360);
lean_inc(x_11);
x_1362 = lean_array_push(x_1346, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1363 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1363 = lean_box(0);
}
if (lean_is_scalar(x_1363)) {
 x_1364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1364 = x_1363;
}
lean_ctor_set(x_1364, 0, x_1353);
lean_ctor_set(x_1364, 1, x_1362);
x_1365 = lean_array_push(x_1346, x_1364);
x_1366 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1367 = lean_array_push(x_1365, x_1366);
x_1368 = lean_array_push(x_1367, x_1339);
x_1369 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1370, 0, x_1369);
lean_ctor_set(x_1370, 1, x_1368);
x_1371 = lean_array_push(x_1346, x_1370);
x_1372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1372, 0, x_1353);
lean_ctor_set(x_1372, 1, x_1371);
x_1373 = lean_array_push(x_1361, x_1372);
x_1374 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1375, 0, x_1374);
lean_ctor_set(x_1375, 1, x_1373);
if (lean_is_scalar(x_1340)) {
 x_1376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1376 = x_1340;
}
lean_ctor_set(x_1376, 0, x_1338);
lean_ctor_set(x_1376, 1, x_1375);
if (lean_is_scalar(x_1345)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1345;
}
lean_ctor_set(x_1377, 0, x_1376);
lean_ctor_set(x_1377, 1, x_1344);
return x_1377;
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1328);
lean_dec(x_11);
lean_dec(x_5);
x_1378 = lean_ctor_get(x_1335, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1335, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 x_1380 = x_1335;
} else {
 lean_dec_ref(x_1335);
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
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; uint8_t x_1385; 
lean_dec(x_11);
x_1382 = lean_ctor_get(x_1326, 0);
lean_inc(x_1382);
lean_dec(x_1326);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
lean_dec(x_1382);
x_1385 = l_Lean_Syntax_isNone(x_1384);
lean_dec(x_1384);
if (x_1385 == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
lean_dec(x_1383);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1386 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_1387 = l_Lean_Elab_Term_throwError___rarg(x_1324, x_1386, x_5, x_6);
lean_dec(x_1324);
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
if (lean_is_scalar(x_1390)) {
 x_1391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1391 = x_1390;
}
lean_ctor_set(x_1391, 0, x_1388);
lean_ctor_set(x_1391, 1, x_1389);
return x_1391;
}
else
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
x_1392 = l_Lean_mkHole(x_1324);
lean_dec(x_1324);
x_1393 = lean_unsigned_to_nat(1u);
x_1394 = lean_nat_add(x_3, x_1393);
lean_dec(x_3);
x_1395 = l_Lean_Elab_Term_mkExplicitBinder(x_1383, x_1392);
x_1396 = lean_array_push(x_4, x_1395);
x_3 = x_1394;
x_4 = x_1396;
goto _start;
}
}
}
else
{
lean_object* x_1398; uint8_t x_1399; 
lean_dec(x_25);
x_1398 = l_Lean_mkAppStx___closed__5;
x_1399 = lean_string_dec_eq(x_22, x_1398);
if (x_1399 == 0)
{
lean_object* x_1400; lean_object* x_1401; uint8_t x_1402; lean_object* x_1403; 
x_1400 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1400, 0, x_16);
lean_ctor_set(x_1400, 1, x_1246);
lean_ctor_set_usize(x_1400, 2, x_1245);
lean_ctor_set(x_14, 1, x_1321);
lean_ctor_set(x_14, 0, x_1400);
x_1401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1401, 0, x_12);
lean_ctor_set(x_1401, 1, x_17);
x_1402 = 1;
lean_inc(x_1401);
x_1403 = l_Lean_Syntax_isTermId_x3f(x_1401, x_1402);
if (lean_obj_tag(x_1403) == 0)
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
lean_dec(x_1401);
x_1404 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1405 = lean_ctor_get(x_1404, 0);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1404, 1);
lean_inc(x_1406);
lean_dec(x_1404);
x_1407 = lean_unsigned_to_nat(1u);
x_1408 = lean_nat_add(x_3, x_1407);
lean_dec(x_3);
x_1409 = l_Lean_mkHole(x_11);
lean_inc(x_1405);
x_1410 = l_Lean_Elab_Term_mkExplicitBinder(x_1405, x_1409);
x_1411 = lean_array_push(x_4, x_1410);
lean_inc(x_5);
x_1412 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1408, x_1411, x_5, x_1406);
if (lean_obj_tag(x_1412) == 0)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
x_1413 = lean_ctor_get(x_1412, 0);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1412, 1);
lean_inc(x_1414);
lean_dec(x_1412);
x_1415 = lean_ctor_get(x_1413, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1413, 1);
lean_inc(x_1416);
if (lean_is_exclusive(x_1413)) {
 lean_ctor_release(x_1413, 0);
 lean_ctor_release(x_1413, 1);
 x_1417 = x_1413;
} else {
 lean_dec_ref(x_1413);
 x_1417 = lean_box(0);
}
x_1418 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1414);
lean_dec(x_5);
x_1419 = lean_ctor_get(x_1418, 1);
lean_inc(x_1419);
lean_dec(x_1418);
x_1420 = l_Lean_Elab_Term_getMainModule___rarg(x_1419);
x_1421 = lean_ctor_get(x_1420, 1);
lean_inc(x_1421);
if (lean_is_exclusive(x_1420)) {
 lean_ctor_release(x_1420, 0);
 lean_ctor_release(x_1420, 1);
 x_1422 = x_1420;
} else {
 lean_dec_ref(x_1420);
 x_1422 = lean_box(0);
}
x_1423 = l_Array_empty___closed__1;
x_1424 = lean_array_push(x_1423, x_1405);
x_1425 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1426 = lean_array_push(x_1424, x_1425);
x_1427 = l_Lean_mkTermIdFromIdent___closed__2;
x_1428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1428, 0, x_1427);
lean_ctor_set(x_1428, 1, x_1426);
x_1429 = lean_array_push(x_1423, x_1428);
x_1430 = l_Lean_nullKind___closed__2;
x_1431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1431, 0, x_1430);
lean_ctor_set(x_1431, 1, x_1429);
x_1432 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1433 = lean_array_push(x_1432, x_1431);
x_1434 = lean_array_push(x_1433, x_1425);
x_1435 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1436 = lean_array_push(x_1434, x_1435);
x_1437 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1438 = lean_array_push(x_1436, x_1437);
lean_inc(x_11);
x_1439 = lean_array_push(x_1423, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1440 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1440 = lean_box(0);
}
if (lean_is_scalar(x_1440)) {
 x_1441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1441 = x_1440;
}
lean_ctor_set(x_1441, 0, x_1430);
lean_ctor_set(x_1441, 1, x_1439);
x_1442 = lean_array_push(x_1423, x_1441);
x_1443 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1444 = lean_array_push(x_1442, x_1443);
x_1445 = lean_array_push(x_1444, x_1416);
x_1446 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_1445);
x_1448 = lean_array_push(x_1423, x_1447);
x_1449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1449, 0, x_1430);
lean_ctor_set(x_1449, 1, x_1448);
x_1450 = lean_array_push(x_1438, x_1449);
x_1451 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1452, 0, x_1451);
lean_ctor_set(x_1452, 1, x_1450);
if (lean_is_scalar(x_1417)) {
 x_1453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1453 = x_1417;
}
lean_ctor_set(x_1453, 0, x_1415);
lean_ctor_set(x_1453, 1, x_1452);
if (lean_is_scalar(x_1422)) {
 x_1454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1454 = x_1422;
}
lean_ctor_set(x_1454, 0, x_1453);
lean_ctor_set(x_1454, 1, x_1421);
return x_1454;
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
lean_dec(x_1405);
lean_dec(x_11);
lean_dec(x_5);
x_1455 = lean_ctor_get(x_1412, 0);
lean_inc(x_1455);
x_1456 = lean_ctor_get(x_1412, 1);
lean_inc(x_1456);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 lean_ctor_release(x_1412, 1);
 x_1457 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1457 = lean_box(0);
}
if (lean_is_scalar(x_1457)) {
 x_1458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1458 = x_1457;
}
lean_ctor_set(x_1458, 0, x_1455);
lean_ctor_set(x_1458, 1, x_1456);
return x_1458;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; uint8_t x_1462; 
lean_dec(x_11);
x_1459 = lean_ctor_get(x_1403, 0);
lean_inc(x_1459);
lean_dec(x_1403);
x_1460 = lean_ctor_get(x_1459, 0);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1459, 1);
lean_inc(x_1461);
lean_dec(x_1459);
x_1462 = l_Lean_Syntax_isNone(x_1461);
lean_dec(x_1461);
if (x_1462 == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; 
lean_dec(x_1460);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1463 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_1464 = l_Lean_Elab_Term_throwError___rarg(x_1401, x_1463, x_5, x_6);
lean_dec(x_1401);
x_1465 = lean_ctor_get(x_1464, 0);
lean_inc(x_1465);
x_1466 = lean_ctor_get(x_1464, 1);
lean_inc(x_1466);
if (lean_is_exclusive(x_1464)) {
 lean_ctor_release(x_1464, 0);
 lean_ctor_release(x_1464, 1);
 x_1467 = x_1464;
} else {
 lean_dec_ref(x_1464);
 x_1467 = lean_box(0);
}
if (lean_is_scalar(x_1467)) {
 x_1468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1468 = x_1467;
}
lean_ctor_set(x_1468, 0, x_1465);
lean_ctor_set(x_1468, 1, x_1466);
return x_1468;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
x_1469 = l_Lean_mkHole(x_1401);
lean_dec(x_1401);
x_1470 = lean_unsigned_to_nat(1u);
x_1471 = lean_nat_add(x_3, x_1470);
lean_dec(x_3);
x_1472 = l_Lean_Elab_Term_mkExplicitBinder(x_1460, x_1469);
x_1473 = lean_array_push(x_4, x_1472);
x_3 = x_1471;
x_4 = x_1473;
goto _start;
}
}
}
else
{
lean_object* x_1475; uint8_t x_1476; 
lean_dec(x_22);
x_1475 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_1476 = lean_string_dec_eq(x_19, x_1475);
if (x_1476 == 0)
{
lean_object* x_1477; uint8_t x_1478; 
x_1477 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_1478 = lean_string_dec_eq(x_19, x_1477);
if (x_1478 == 0)
{
lean_object* x_1479; uint8_t x_1480; 
x_1479 = l_Lean_mkHole___closed__1;
x_1480 = lean_string_dec_eq(x_19, x_1479);
if (x_1480 == 0)
{
lean_object* x_1481; uint8_t x_1482; 
x_1481 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_1482 = lean_string_dec_eq(x_19, x_1481);
if (x_1482 == 0)
{
lean_object* x_1483; lean_object* x_1484; uint8_t x_1485; lean_object* x_1486; 
x_1483 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1483, 0, x_16);
lean_ctor_set(x_1483, 1, x_1246);
lean_ctor_set_usize(x_1483, 2, x_1245);
lean_ctor_set(x_14, 1, x_1321);
lean_ctor_set(x_14, 0, x_1483);
lean_ctor_set(x_13, 1, x_1398);
x_1484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1484, 0, x_12);
lean_ctor_set(x_1484, 1, x_17);
x_1485 = 1;
lean_inc(x_1484);
x_1486 = l_Lean_Syntax_isTermId_x3f(x_1484, x_1485);
if (lean_obj_tag(x_1486) == 0)
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
lean_dec(x_1484);
x_1487 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1487, 1);
lean_inc(x_1489);
lean_dec(x_1487);
x_1490 = lean_unsigned_to_nat(1u);
x_1491 = lean_nat_add(x_3, x_1490);
lean_dec(x_3);
x_1492 = l_Lean_mkHole(x_11);
lean_inc(x_1488);
x_1493 = l_Lean_Elab_Term_mkExplicitBinder(x_1488, x_1492);
x_1494 = lean_array_push(x_4, x_1493);
lean_inc(x_5);
x_1495 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1491, x_1494, x_5, x_1489);
if (lean_obj_tag(x_1495) == 0)
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; 
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1495, 1);
lean_inc(x_1497);
lean_dec(x_1495);
x_1498 = lean_ctor_get(x_1496, 0);
lean_inc(x_1498);
x_1499 = lean_ctor_get(x_1496, 1);
lean_inc(x_1499);
if (lean_is_exclusive(x_1496)) {
 lean_ctor_release(x_1496, 0);
 lean_ctor_release(x_1496, 1);
 x_1500 = x_1496;
} else {
 lean_dec_ref(x_1496);
 x_1500 = lean_box(0);
}
x_1501 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1497);
lean_dec(x_5);
x_1502 = lean_ctor_get(x_1501, 1);
lean_inc(x_1502);
lean_dec(x_1501);
x_1503 = l_Lean_Elab_Term_getMainModule___rarg(x_1502);
x_1504 = lean_ctor_get(x_1503, 1);
lean_inc(x_1504);
if (lean_is_exclusive(x_1503)) {
 lean_ctor_release(x_1503, 0);
 lean_ctor_release(x_1503, 1);
 x_1505 = x_1503;
} else {
 lean_dec_ref(x_1503);
 x_1505 = lean_box(0);
}
x_1506 = l_Array_empty___closed__1;
x_1507 = lean_array_push(x_1506, x_1488);
x_1508 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1509 = lean_array_push(x_1507, x_1508);
x_1510 = l_Lean_mkTermIdFromIdent___closed__2;
x_1511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1511, 0, x_1510);
lean_ctor_set(x_1511, 1, x_1509);
x_1512 = lean_array_push(x_1506, x_1511);
x_1513 = l_Lean_nullKind___closed__2;
x_1514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1514, 0, x_1513);
lean_ctor_set(x_1514, 1, x_1512);
x_1515 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1516 = lean_array_push(x_1515, x_1514);
x_1517 = lean_array_push(x_1516, x_1508);
x_1518 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1519 = lean_array_push(x_1517, x_1518);
x_1520 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1521 = lean_array_push(x_1519, x_1520);
lean_inc(x_11);
x_1522 = lean_array_push(x_1506, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1523 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1523 = lean_box(0);
}
if (lean_is_scalar(x_1523)) {
 x_1524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1524 = x_1523;
}
lean_ctor_set(x_1524, 0, x_1513);
lean_ctor_set(x_1524, 1, x_1522);
x_1525 = lean_array_push(x_1506, x_1524);
x_1526 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1527 = lean_array_push(x_1525, x_1526);
x_1528 = lean_array_push(x_1527, x_1499);
x_1529 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1530, 0, x_1529);
lean_ctor_set(x_1530, 1, x_1528);
x_1531 = lean_array_push(x_1506, x_1530);
x_1532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1532, 0, x_1513);
lean_ctor_set(x_1532, 1, x_1531);
x_1533 = lean_array_push(x_1521, x_1532);
x_1534 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1535, 0, x_1534);
lean_ctor_set(x_1535, 1, x_1533);
if (lean_is_scalar(x_1500)) {
 x_1536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1536 = x_1500;
}
lean_ctor_set(x_1536, 0, x_1498);
lean_ctor_set(x_1536, 1, x_1535);
if (lean_is_scalar(x_1505)) {
 x_1537 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1537 = x_1505;
}
lean_ctor_set(x_1537, 0, x_1536);
lean_ctor_set(x_1537, 1, x_1504);
return x_1537;
}
else
{
lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
lean_dec(x_1488);
lean_dec(x_11);
lean_dec(x_5);
x_1538 = lean_ctor_get(x_1495, 0);
lean_inc(x_1538);
x_1539 = lean_ctor_get(x_1495, 1);
lean_inc(x_1539);
if (lean_is_exclusive(x_1495)) {
 lean_ctor_release(x_1495, 0);
 lean_ctor_release(x_1495, 1);
 x_1540 = x_1495;
} else {
 lean_dec_ref(x_1495);
 x_1540 = lean_box(0);
}
if (lean_is_scalar(x_1540)) {
 x_1541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1541 = x_1540;
}
lean_ctor_set(x_1541, 0, x_1538);
lean_ctor_set(x_1541, 1, x_1539);
return x_1541;
}
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; uint8_t x_1545; 
lean_dec(x_11);
x_1542 = lean_ctor_get(x_1486, 0);
lean_inc(x_1542);
lean_dec(x_1486);
x_1543 = lean_ctor_get(x_1542, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1542, 1);
lean_inc(x_1544);
lean_dec(x_1542);
x_1545 = l_Lean_Syntax_isNone(x_1544);
lean_dec(x_1544);
if (x_1545 == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; 
lean_dec(x_1543);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1546 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_1547 = l_Lean_Elab_Term_throwError___rarg(x_1484, x_1546, x_5, x_6);
lean_dec(x_1484);
x_1548 = lean_ctor_get(x_1547, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1547, 1);
lean_inc(x_1549);
if (lean_is_exclusive(x_1547)) {
 lean_ctor_release(x_1547, 0);
 lean_ctor_release(x_1547, 1);
 x_1550 = x_1547;
} else {
 lean_dec_ref(x_1547);
 x_1550 = lean_box(0);
}
if (lean_is_scalar(x_1550)) {
 x_1551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1551 = x_1550;
}
lean_ctor_set(x_1551, 0, x_1548);
lean_ctor_set(x_1551, 1, x_1549);
return x_1551;
}
else
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; 
x_1552 = l_Lean_mkHole(x_1484);
lean_dec(x_1484);
x_1553 = lean_unsigned_to_nat(1u);
x_1554 = lean_nat_add(x_3, x_1553);
lean_dec(x_3);
x_1555 = l_Lean_Elab_Term_mkExplicitBinder(x_1543, x_1552);
x_1556 = lean_array_push(x_4, x_1555);
x_3 = x_1554;
x_4 = x_1556;
goto _start;
}
}
}
else
{
lean_object* x_1558; lean_object* x_1559; uint8_t x_1560; 
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1558 = lean_unsigned_to_nat(1u);
x_1559 = l_Lean_Syntax_getArg(x_11, x_1558);
x_1560 = l_Lean_Syntax_isNone(x_1559);
if (x_1560 == 0)
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; uint8_t x_1564; 
x_1561 = lean_unsigned_to_nat(0u);
x_1562 = l_Lean_Syntax_getArg(x_1559, x_1561);
x_1563 = l_Lean_Syntax_getArg(x_1559, x_1558);
lean_dec(x_1559);
x_1564 = l_Lean_Syntax_isNone(x_1563);
if (x_1564 == 0)
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; uint8_t x_1572; 
x_1565 = l_Lean_Syntax_getArg(x_1563, x_1561);
lean_dec(x_1563);
lean_inc(x_1565);
x_1566 = l_Lean_Syntax_getKind(x_1565);
x_1567 = lean_name_mk_string(x_16, x_1246);
x_1568 = lean_name_mk_string(x_1567, x_1321);
x_1569 = lean_name_mk_string(x_1568, x_1398);
x_1570 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_1571 = lean_name_mk_string(x_1569, x_1570);
x_1572 = lean_name_eq(x_1566, x_1571);
lean_dec(x_1571);
lean_dec(x_1566);
if (x_1572 == 0)
{
lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; 
lean_dec(x_1565);
lean_dec(x_1562);
x_1573 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1574 = lean_ctor_get(x_1573, 0);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1573, 1);
lean_inc(x_1575);
lean_dec(x_1573);
x_1576 = lean_nat_add(x_3, x_1558);
lean_dec(x_3);
x_1577 = l_Lean_mkHole(x_11);
lean_inc(x_1574);
x_1578 = l_Lean_Elab_Term_mkExplicitBinder(x_1574, x_1577);
x_1579 = lean_array_push(x_4, x_1578);
lean_inc(x_5);
x_1580 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1576, x_1579, x_5, x_1575);
if (lean_obj_tag(x_1580) == 0)
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1581 = lean_ctor_get(x_1580, 0);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_1580, 1);
lean_inc(x_1582);
lean_dec(x_1580);
x_1583 = lean_ctor_get(x_1581, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1581, 1);
lean_inc(x_1584);
if (lean_is_exclusive(x_1581)) {
 lean_ctor_release(x_1581, 0);
 lean_ctor_release(x_1581, 1);
 x_1585 = x_1581;
} else {
 lean_dec_ref(x_1581);
 x_1585 = lean_box(0);
}
x_1586 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1582);
lean_dec(x_5);
x_1587 = lean_ctor_get(x_1586, 1);
lean_inc(x_1587);
lean_dec(x_1586);
x_1588 = l_Lean_Elab_Term_getMainModule___rarg(x_1587);
x_1589 = lean_ctor_get(x_1588, 1);
lean_inc(x_1589);
if (lean_is_exclusive(x_1588)) {
 lean_ctor_release(x_1588, 0);
 lean_ctor_release(x_1588, 1);
 x_1590 = x_1588;
} else {
 lean_dec_ref(x_1588);
 x_1590 = lean_box(0);
}
x_1591 = l_Array_empty___closed__1;
x_1592 = lean_array_push(x_1591, x_1574);
x_1593 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1594 = lean_array_push(x_1592, x_1593);
x_1595 = l_Lean_mkTermIdFromIdent___closed__2;
x_1596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1596, 0, x_1595);
lean_ctor_set(x_1596, 1, x_1594);
x_1597 = lean_array_push(x_1591, x_1596);
x_1598 = l_Lean_nullKind___closed__2;
x_1599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1599, 0, x_1598);
lean_ctor_set(x_1599, 1, x_1597);
x_1600 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1601 = lean_array_push(x_1600, x_1599);
x_1602 = lean_array_push(x_1601, x_1593);
x_1603 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1604 = lean_array_push(x_1602, x_1603);
x_1605 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1606 = lean_array_push(x_1604, x_1605);
lean_inc(x_11);
x_1607 = lean_array_push(x_1591, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1608 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1608 = lean_box(0);
}
if (lean_is_scalar(x_1608)) {
 x_1609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1609 = x_1608;
}
lean_ctor_set(x_1609, 0, x_1598);
lean_ctor_set(x_1609, 1, x_1607);
x_1610 = lean_array_push(x_1591, x_1609);
x_1611 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1612 = lean_array_push(x_1610, x_1611);
x_1613 = lean_array_push(x_1612, x_1584);
x_1614 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1615, 0, x_1614);
lean_ctor_set(x_1615, 1, x_1613);
x_1616 = lean_array_push(x_1591, x_1615);
x_1617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1617, 0, x_1598);
lean_ctor_set(x_1617, 1, x_1616);
x_1618 = lean_array_push(x_1606, x_1617);
x_1619 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1620, 0, x_1619);
lean_ctor_set(x_1620, 1, x_1618);
if (lean_is_scalar(x_1585)) {
 x_1621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1621 = x_1585;
}
lean_ctor_set(x_1621, 0, x_1583);
lean_ctor_set(x_1621, 1, x_1620);
if (lean_is_scalar(x_1590)) {
 x_1622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1622 = x_1590;
}
lean_ctor_set(x_1622, 0, x_1621);
lean_ctor_set(x_1622, 1, x_1589);
return x_1622;
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; 
lean_dec(x_1574);
lean_dec(x_11);
lean_dec(x_5);
x_1623 = lean_ctor_get(x_1580, 0);
lean_inc(x_1623);
x_1624 = lean_ctor_get(x_1580, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1580)) {
 lean_ctor_release(x_1580, 0);
 lean_ctor_release(x_1580, 1);
 x_1625 = x_1580;
} else {
 lean_dec_ref(x_1580);
 x_1625 = lean_box(0);
}
if (lean_is_scalar(x_1625)) {
 x_1626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1626 = x_1625;
}
lean_ctor_set(x_1626, 0, x_1623);
lean_ctor_set(x_1626, 1, x_1624);
return x_1626;
}
}
else
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1627 = l_Lean_Syntax_getArg(x_1565, x_1558);
lean_dec(x_1565);
x_1628 = l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(x_1562, x_5, x_6);
x_1629 = lean_ctor_get(x_1628, 0);
lean_inc(x_1629);
if (lean_obj_tag(x_1629) == 0)
{
lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
lean_dec(x_1627);
x_1630 = lean_ctor_get(x_1628, 1);
lean_inc(x_1630);
lean_dec(x_1628);
x_1631 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_1630);
x_1632 = lean_ctor_get(x_1631, 0);
lean_inc(x_1632);
x_1633 = lean_ctor_get(x_1631, 1);
lean_inc(x_1633);
lean_dec(x_1631);
x_1634 = lean_nat_add(x_3, x_1558);
lean_dec(x_3);
x_1635 = l_Lean_mkHole(x_11);
lean_inc(x_1632);
x_1636 = l_Lean_Elab_Term_mkExplicitBinder(x_1632, x_1635);
x_1637 = lean_array_push(x_4, x_1636);
lean_inc(x_5);
x_1638 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1634, x_1637, x_5, x_1633);
if (lean_obj_tag(x_1638) == 0)
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; 
x_1639 = lean_ctor_get(x_1638, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1638, 1);
lean_inc(x_1640);
lean_dec(x_1638);
x_1641 = lean_ctor_get(x_1639, 0);
lean_inc(x_1641);
x_1642 = lean_ctor_get(x_1639, 1);
lean_inc(x_1642);
if (lean_is_exclusive(x_1639)) {
 lean_ctor_release(x_1639, 0);
 lean_ctor_release(x_1639, 1);
 x_1643 = x_1639;
} else {
 lean_dec_ref(x_1639);
 x_1643 = lean_box(0);
}
x_1644 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1640);
lean_dec(x_5);
x_1645 = lean_ctor_get(x_1644, 1);
lean_inc(x_1645);
lean_dec(x_1644);
x_1646 = l_Lean_Elab_Term_getMainModule___rarg(x_1645);
x_1647 = lean_ctor_get(x_1646, 1);
lean_inc(x_1647);
if (lean_is_exclusive(x_1646)) {
 lean_ctor_release(x_1646, 0);
 lean_ctor_release(x_1646, 1);
 x_1648 = x_1646;
} else {
 lean_dec_ref(x_1646);
 x_1648 = lean_box(0);
}
x_1649 = l_Array_empty___closed__1;
x_1650 = lean_array_push(x_1649, x_1632);
x_1651 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1652 = lean_array_push(x_1650, x_1651);
x_1653 = l_Lean_mkTermIdFromIdent___closed__2;
x_1654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1654, 0, x_1653);
lean_ctor_set(x_1654, 1, x_1652);
x_1655 = lean_array_push(x_1649, x_1654);
x_1656 = l_Lean_nullKind___closed__2;
x_1657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1657, 0, x_1656);
lean_ctor_set(x_1657, 1, x_1655);
x_1658 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1659 = lean_array_push(x_1658, x_1657);
x_1660 = lean_array_push(x_1659, x_1651);
x_1661 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1662 = lean_array_push(x_1660, x_1661);
x_1663 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1664 = lean_array_push(x_1662, x_1663);
lean_inc(x_11);
x_1665 = lean_array_push(x_1649, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1666 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1666 = lean_box(0);
}
if (lean_is_scalar(x_1666)) {
 x_1667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1667 = x_1666;
}
lean_ctor_set(x_1667, 0, x_1656);
lean_ctor_set(x_1667, 1, x_1665);
x_1668 = lean_array_push(x_1649, x_1667);
x_1669 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1670 = lean_array_push(x_1668, x_1669);
x_1671 = lean_array_push(x_1670, x_1642);
x_1672 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1673, 0, x_1672);
lean_ctor_set(x_1673, 1, x_1671);
x_1674 = lean_array_push(x_1649, x_1673);
x_1675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1675, 0, x_1656);
lean_ctor_set(x_1675, 1, x_1674);
x_1676 = lean_array_push(x_1664, x_1675);
x_1677 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1678, 0, x_1677);
lean_ctor_set(x_1678, 1, x_1676);
if (lean_is_scalar(x_1643)) {
 x_1679 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1679 = x_1643;
}
lean_ctor_set(x_1679, 0, x_1641);
lean_ctor_set(x_1679, 1, x_1678);
if (lean_is_scalar(x_1648)) {
 x_1680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1680 = x_1648;
}
lean_ctor_set(x_1680, 0, x_1679);
lean_ctor_set(x_1680, 1, x_1647);
return x_1680;
}
else
{
lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
lean_dec(x_1632);
lean_dec(x_11);
lean_dec(x_5);
x_1681 = lean_ctor_get(x_1638, 0);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_1638, 1);
lean_inc(x_1682);
if (lean_is_exclusive(x_1638)) {
 lean_ctor_release(x_1638, 0);
 lean_ctor_release(x_1638, 1);
 x_1683 = x_1638;
} else {
 lean_dec_ref(x_1638);
 x_1683 = lean_box(0);
}
if (lean_is_scalar(x_1683)) {
 x_1684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1684 = x_1683;
}
lean_ctor_set(x_1684, 0, x_1681);
lean_ctor_set(x_1684, 1, x_1682);
return x_1684;
}
}
else
{
lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
lean_dec(x_11);
x_1685 = lean_ctor_get(x_1628, 1);
lean_inc(x_1685);
lean_dec(x_1628);
x_1686 = lean_ctor_get(x_1629, 0);
lean_inc(x_1686);
lean_dec(x_1629);
x_1687 = lean_nat_add(x_3, x_1558);
lean_dec(x_3);
x_1688 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(x_1627, x_1561, x_1686);
x_1689 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1688, x_1688, x_1561, x_4);
lean_dec(x_1688);
x_3 = x_1687;
x_4 = x_1689;
x_6 = x_1685;
goto _start;
}
}
}
else
{
lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; 
lean_dec(x_1563);
lean_dec(x_1562);
x_1691 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1692 = lean_ctor_get(x_1691, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1691, 1);
lean_inc(x_1693);
lean_dec(x_1691);
x_1694 = lean_nat_add(x_3, x_1558);
lean_dec(x_3);
x_1695 = l_Lean_mkHole(x_11);
lean_inc(x_1692);
x_1696 = l_Lean_Elab_Term_mkExplicitBinder(x_1692, x_1695);
x_1697 = lean_array_push(x_4, x_1696);
lean_inc(x_5);
x_1698 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1694, x_1697, x_5, x_1693);
if (lean_obj_tag(x_1698) == 0)
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; 
x_1699 = lean_ctor_get(x_1698, 0);
lean_inc(x_1699);
x_1700 = lean_ctor_get(x_1698, 1);
lean_inc(x_1700);
lean_dec(x_1698);
x_1701 = lean_ctor_get(x_1699, 0);
lean_inc(x_1701);
x_1702 = lean_ctor_get(x_1699, 1);
lean_inc(x_1702);
if (lean_is_exclusive(x_1699)) {
 lean_ctor_release(x_1699, 0);
 lean_ctor_release(x_1699, 1);
 x_1703 = x_1699;
} else {
 lean_dec_ref(x_1699);
 x_1703 = lean_box(0);
}
x_1704 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1700);
lean_dec(x_5);
x_1705 = lean_ctor_get(x_1704, 1);
lean_inc(x_1705);
lean_dec(x_1704);
x_1706 = l_Lean_Elab_Term_getMainModule___rarg(x_1705);
x_1707 = lean_ctor_get(x_1706, 1);
lean_inc(x_1707);
if (lean_is_exclusive(x_1706)) {
 lean_ctor_release(x_1706, 0);
 lean_ctor_release(x_1706, 1);
 x_1708 = x_1706;
} else {
 lean_dec_ref(x_1706);
 x_1708 = lean_box(0);
}
x_1709 = l_Array_empty___closed__1;
x_1710 = lean_array_push(x_1709, x_1692);
x_1711 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1712 = lean_array_push(x_1710, x_1711);
x_1713 = l_Lean_mkTermIdFromIdent___closed__2;
x_1714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1714, 0, x_1713);
lean_ctor_set(x_1714, 1, x_1712);
x_1715 = lean_array_push(x_1709, x_1714);
x_1716 = l_Lean_nullKind___closed__2;
x_1717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1717, 0, x_1716);
lean_ctor_set(x_1717, 1, x_1715);
x_1718 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1719 = lean_array_push(x_1718, x_1717);
x_1720 = lean_array_push(x_1719, x_1711);
x_1721 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1722 = lean_array_push(x_1720, x_1721);
x_1723 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1724 = lean_array_push(x_1722, x_1723);
lean_inc(x_11);
x_1725 = lean_array_push(x_1709, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1726 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1726 = lean_box(0);
}
if (lean_is_scalar(x_1726)) {
 x_1727 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1727 = x_1726;
}
lean_ctor_set(x_1727, 0, x_1716);
lean_ctor_set(x_1727, 1, x_1725);
x_1728 = lean_array_push(x_1709, x_1727);
x_1729 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1730 = lean_array_push(x_1728, x_1729);
x_1731 = lean_array_push(x_1730, x_1702);
x_1732 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1733, 0, x_1732);
lean_ctor_set(x_1733, 1, x_1731);
x_1734 = lean_array_push(x_1709, x_1733);
x_1735 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1735, 0, x_1716);
lean_ctor_set(x_1735, 1, x_1734);
x_1736 = lean_array_push(x_1724, x_1735);
x_1737 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1738, 0, x_1737);
lean_ctor_set(x_1738, 1, x_1736);
if (lean_is_scalar(x_1703)) {
 x_1739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1739 = x_1703;
}
lean_ctor_set(x_1739, 0, x_1701);
lean_ctor_set(x_1739, 1, x_1738);
if (lean_is_scalar(x_1708)) {
 x_1740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1740 = x_1708;
}
lean_ctor_set(x_1740, 0, x_1739);
lean_ctor_set(x_1740, 1, x_1707);
return x_1740;
}
else
{
lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; 
lean_dec(x_1692);
lean_dec(x_11);
lean_dec(x_5);
x_1741 = lean_ctor_get(x_1698, 0);
lean_inc(x_1741);
x_1742 = lean_ctor_get(x_1698, 1);
lean_inc(x_1742);
if (lean_is_exclusive(x_1698)) {
 lean_ctor_release(x_1698, 0);
 lean_ctor_release(x_1698, 1);
 x_1743 = x_1698;
} else {
 lean_dec_ref(x_1698);
 x_1743 = lean_box(0);
}
if (lean_is_scalar(x_1743)) {
 x_1744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1744 = x_1743;
}
lean_ctor_set(x_1744, 0, x_1741);
lean_ctor_set(x_1744, 1, x_1742);
return x_1744;
}
}
}
else
{
lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; 
lean_dec(x_1559);
x_1745 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1746 = lean_ctor_get(x_1745, 0);
lean_inc(x_1746);
x_1747 = lean_ctor_get(x_1745, 1);
lean_inc(x_1747);
lean_dec(x_1745);
x_1748 = lean_nat_add(x_3, x_1558);
lean_dec(x_3);
x_1749 = l_Lean_mkHole(x_11);
lean_inc(x_1746);
x_1750 = l_Lean_Elab_Term_mkExplicitBinder(x_1746, x_1749);
x_1751 = lean_array_push(x_4, x_1750);
lean_inc(x_5);
x_1752 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1748, x_1751, x_5, x_1747);
if (lean_obj_tag(x_1752) == 0)
{
lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; 
x_1753 = lean_ctor_get(x_1752, 0);
lean_inc(x_1753);
x_1754 = lean_ctor_get(x_1752, 1);
lean_inc(x_1754);
lean_dec(x_1752);
x_1755 = lean_ctor_get(x_1753, 0);
lean_inc(x_1755);
x_1756 = lean_ctor_get(x_1753, 1);
lean_inc(x_1756);
if (lean_is_exclusive(x_1753)) {
 lean_ctor_release(x_1753, 0);
 lean_ctor_release(x_1753, 1);
 x_1757 = x_1753;
} else {
 lean_dec_ref(x_1753);
 x_1757 = lean_box(0);
}
x_1758 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1754);
lean_dec(x_5);
x_1759 = lean_ctor_get(x_1758, 1);
lean_inc(x_1759);
lean_dec(x_1758);
x_1760 = l_Lean_Elab_Term_getMainModule___rarg(x_1759);
x_1761 = lean_ctor_get(x_1760, 1);
lean_inc(x_1761);
if (lean_is_exclusive(x_1760)) {
 lean_ctor_release(x_1760, 0);
 lean_ctor_release(x_1760, 1);
 x_1762 = x_1760;
} else {
 lean_dec_ref(x_1760);
 x_1762 = lean_box(0);
}
x_1763 = l_Array_empty___closed__1;
x_1764 = lean_array_push(x_1763, x_1746);
x_1765 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1766 = lean_array_push(x_1764, x_1765);
x_1767 = l_Lean_mkTermIdFromIdent___closed__2;
x_1768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1768, 0, x_1767);
lean_ctor_set(x_1768, 1, x_1766);
x_1769 = lean_array_push(x_1763, x_1768);
x_1770 = l_Lean_nullKind___closed__2;
x_1771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1771, 0, x_1770);
lean_ctor_set(x_1771, 1, x_1769);
x_1772 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1773 = lean_array_push(x_1772, x_1771);
x_1774 = lean_array_push(x_1773, x_1765);
x_1775 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1776 = lean_array_push(x_1774, x_1775);
x_1777 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1778 = lean_array_push(x_1776, x_1777);
lean_inc(x_11);
x_1779 = lean_array_push(x_1763, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1780 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1780 = lean_box(0);
}
if (lean_is_scalar(x_1780)) {
 x_1781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1781 = x_1780;
}
lean_ctor_set(x_1781, 0, x_1770);
lean_ctor_set(x_1781, 1, x_1779);
x_1782 = lean_array_push(x_1763, x_1781);
x_1783 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1784 = lean_array_push(x_1782, x_1783);
x_1785 = lean_array_push(x_1784, x_1756);
x_1786 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1787, 0, x_1786);
lean_ctor_set(x_1787, 1, x_1785);
x_1788 = lean_array_push(x_1763, x_1787);
x_1789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1789, 0, x_1770);
lean_ctor_set(x_1789, 1, x_1788);
x_1790 = lean_array_push(x_1778, x_1789);
x_1791 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1792, 0, x_1791);
lean_ctor_set(x_1792, 1, x_1790);
if (lean_is_scalar(x_1757)) {
 x_1793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1793 = x_1757;
}
lean_ctor_set(x_1793, 0, x_1755);
lean_ctor_set(x_1793, 1, x_1792);
if (lean_is_scalar(x_1762)) {
 x_1794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1794 = x_1762;
}
lean_ctor_set(x_1794, 0, x_1793);
lean_ctor_set(x_1794, 1, x_1761);
return x_1794;
}
else
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; 
lean_dec(x_1746);
lean_dec(x_11);
lean_dec(x_5);
x_1795 = lean_ctor_get(x_1752, 0);
lean_inc(x_1795);
x_1796 = lean_ctor_get(x_1752, 1);
lean_inc(x_1796);
if (lean_is_exclusive(x_1752)) {
 lean_ctor_release(x_1752, 0);
 lean_ctor_release(x_1752, 1);
 x_1797 = x_1752;
} else {
 lean_dec_ref(x_1752);
 x_1797 = lean_box(0);
}
if (lean_is_scalar(x_1797)) {
 x_1798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1798 = x_1797;
}
lean_ctor_set(x_1798, 0, x_1795);
lean_ctor_set(x_1798, 1, x_1796);
return x_1798;
}
}
}
}
else
{
lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; 
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1799 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1800 = lean_ctor_get(x_1799, 0);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1799, 1);
lean_inc(x_1801);
lean_dec(x_1799);
x_1802 = lean_unsigned_to_nat(1u);
x_1803 = lean_nat_add(x_3, x_1802);
lean_dec(x_3);
x_1804 = l_Lean_Elab_Term_mkExplicitBinder(x_1800, x_11);
x_1805 = lean_array_push(x_4, x_1804);
x_3 = x_1803;
x_4 = x_1805;
x_6 = x_1801;
goto _start;
}
}
else
{
lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; 
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1807 = lean_unsigned_to_nat(1u);
x_1808 = lean_nat_add(x_3, x_1807);
lean_dec(x_3);
x_1809 = lean_array_push(x_4, x_11);
x_3 = x_1808;
x_4 = x_1809;
goto _start;
}
}
else
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; 
lean_free_object(x_14);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1811 = lean_unsigned_to_nat(1u);
x_1812 = lean_nat_add(x_3, x_1811);
lean_dec(x_3);
x_1813 = lean_array_push(x_4, x_11);
x_3 = x_1812;
x_4 = x_1813;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_1815; size_t x_1816; lean_object* x_1817; size_t x_1818; lean_object* x_1819; lean_object* x_1820; uint8_t x_1821; 
x_1815 = lean_ctor_get(x_14, 1);
x_1816 = lean_ctor_get_usize(x_14, 2);
lean_inc(x_1815);
lean_dec(x_14);
x_1817 = lean_ctor_get(x_15, 1);
lean_inc(x_1817);
x_1818 = lean_ctor_get_usize(x_15, 2);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_1819 = x_15;
} else {
 lean_dec_ref(x_15);
 x_1819 = lean_box(0);
}
x_1820 = l_Lean_mkAppStx___closed__1;
x_1821 = lean_string_dec_eq(x_1817, x_1820);
lean_dec(x_1817);
if (x_1821 == 0)
{
uint8_t x_1822; lean_object* x_1823; 
lean_dec(x_1819);
lean_dec(x_1815);
lean_free_object(x_13);
lean_dec(x_22);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_1822 = 1;
lean_inc(x_11);
x_1823 = l_Lean_Syntax_isTermId_x3f(x_11, x_1822);
if (lean_obj_tag(x_1823) == 0)
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
x_1824 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1825 = lean_ctor_get(x_1824, 0);
lean_inc(x_1825);
x_1826 = lean_ctor_get(x_1824, 1);
lean_inc(x_1826);
lean_dec(x_1824);
x_1827 = lean_unsigned_to_nat(1u);
x_1828 = lean_nat_add(x_3, x_1827);
lean_dec(x_3);
x_1829 = l_Lean_mkHole(x_11);
lean_inc(x_1825);
x_1830 = l_Lean_Elab_Term_mkExplicitBinder(x_1825, x_1829);
x_1831 = lean_array_push(x_4, x_1830);
lean_inc(x_5);
x_1832 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1828, x_1831, x_5, x_1826);
if (lean_obj_tag(x_1832) == 0)
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1833 = lean_ctor_get(x_1832, 0);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1832, 1);
lean_inc(x_1834);
lean_dec(x_1832);
x_1835 = lean_ctor_get(x_1833, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1833, 1);
lean_inc(x_1836);
if (lean_is_exclusive(x_1833)) {
 lean_ctor_release(x_1833, 0);
 lean_ctor_release(x_1833, 1);
 x_1837 = x_1833;
} else {
 lean_dec_ref(x_1833);
 x_1837 = lean_box(0);
}
x_1838 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1834);
lean_dec(x_5);
x_1839 = lean_ctor_get(x_1838, 1);
lean_inc(x_1839);
lean_dec(x_1838);
x_1840 = l_Lean_Elab_Term_getMainModule___rarg(x_1839);
x_1841 = lean_ctor_get(x_1840, 1);
lean_inc(x_1841);
if (lean_is_exclusive(x_1840)) {
 lean_ctor_release(x_1840, 0);
 lean_ctor_release(x_1840, 1);
 x_1842 = x_1840;
} else {
 lean_dec_ref(x_1840);
 x_1842 = lean_box(0);
}
x_1843 = l_Array_empty___closed__1;
x_1844 = lean_array_push(x_1843, x_1825);
x_1845 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1846 = lean_array_push(x_1844, x_1845);
x_1847 = l_Lean_mkTermIdFromIdent___closed__2;
x_1848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1848, 0, x_1847);
lean_ctor_set(x_1848, 1, x_1846);
x_1849 = lean_array_push(x_1843, x_1848);
x_1850 = l_Lean_nullKind___closed__2;
x_1851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1851, 0, x_1850);
lean_ctor_set(x_1851, 1, x_1849);
x_1852 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1853 = lean_array_push(x_1852, x_1851);
x_1854 = lean_array_push(x_1853, x_1845);
x_1855 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1856 = lean_array_push(x_1854, x_1855);
x_1857 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1858 = lean_array_push(x_1856, x_1857);
lean_inc(x_11);
x_1859 = lean_array_push(x_1843, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1860 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1860 = lean_box(0);
}
if (lean_is_scalar(x_1860)) {
 x_1861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1861 = x_1860;
}
lean_ctor_set(x_1861, 0, x_1850);
lean_ctor_set(x_1861, 1, x_1859);
x_1862 = lean_array_push(x_1843, x_1861);
x_1863 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1864 = lean_array_push(x_1862, x_1863);
x_1865 = lean_array_push(x_1864, x_1836);
x_1866 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1867, 0, x_1866);
lean_ctor_set(x_1867, 1, x_1865);
x_1868 = lean_array_push(x_1843, x_1867);
x_1869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1869, 0, x_1850);
lean_ctor_set(x_1869, 1, x_1868);
x_1870 = lean_array_push(x_1858, x_1869);
x_1871 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1872, 0, x_1871);
lean_ctor_set(x_1872, 1, x_1870);
if (lean_is_scalar(x_1837)) {
 x_1873 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1873 = x_1837;
}
lean_ctor_set(x_1873, 0, x_1835);
lean_ctor_set(x_1873, 1, x_1872);
if (lean_is_scalar(x_1842)) {
 x_1874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1874 = x_1842;
}
lean_ctor_set(x_1874, 0, x_1873);
lean_ctor_set(x_1874, 1, x_1841);
return x_1874;
}
else
{
lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; 
lean_dec(x_1825);
lean_dec(x_11);
lean_dec(x_5);
x_1875 = lean_ctor_get(x_1832, 0);
lean_inc(x_1875);
x_1876 = lean_ctor_get(x_1832, 1);
lean_inc(x_1876);
if (lean_is_exclusive(x_1832)) {
 lean_ctor_release(x_1832, 0);
 lean_ctor_release(x_1832, 1);
 x_1877 = x_1832;
} else {
 lean_dec_ref(x_1832);
 x_1877 = lean_box(0);
}
if (lean_is_scalar(x_1877)) {
 x_1878 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1878 = x_1877;
}
lean_ctor_set(x_1878, 0, x_1875);
lean_ctor_set(x_1878, 1, x_1876);
return x_1878;
}
}
else
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; uint8_t x_1882; 
x_1879 = lean_ctor_get(x_1823, 0);
lean_inc(x_1879);
lean_dec(x_1823);
x_1880 = lean_ctor_get(x_1879, 0);
lean_inc(x_1880);
x_1881 = lean_ctor_get(x_1879, 1);
lean_inc(x_1881);
lean_dec(x_1879);
x_1882 = l_Lean_Syntax_isNone(x_1881);
lean_dec(x_1881);
if (x_1882 == 0)
{
lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; 
lean_dec(x_1880);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1883 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_1884 = l_Lean_Elab_Term_throwError___rarg(x_11, x_1883, x_5, x_6);
lean_dec(x_11);
x_1885 = lean_ctor_get(x_1884, 0);
lean_inc(x_1885);
x_1886 = lean_ctor_get(x_1884, 1);
lean_inc(x_1886);
if (lean_is_exclusive(x_1884)) {
 lean_ctor_release(x_1884, 0);
 lean_ctor_release(x_1884, 1);
 x_1887 = x_1884;
} else {
 lean_dec_ref(x_1884);
 x_1887 = lean_box(0);
}
if (lean_is_scalar(x_1887)) {
 x_1888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1888 = x_1887;
}
lean_ctor_set(x_1888, 0, x_1885);
lean_ctor_set(x_1888, 1, x_1886);
return x_1888;
}
else
{
lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; 
x_1889 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_1890 = lean_unsigned_to_nat(1u);
x_1891 = lean_nat_add(x_3, x_1890);
lean_dec(x_3);
x_1892 = l_Lean_Elab_Term_mkExplicitBinder(x_1880, x_1889);
x_1893 = lean_array_push(x_4, x_1892);
x_3 = x_1891;
x_4 = x_1893;
goto _start;
}
}
}
else
{
lean_object* x_1895; uint8_t x_1896; 
x_1895 = l_Lean_mkAppStx___closed__3;
x_1896 = lean_string_dec_eq(x_1815, x_1895);
if (x_1896 == 0)
{
lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; uint8_t x_1900; lean_object* x_1901; 
if (lean_is_scalar(x_1819)) {
 x_1897 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_1897 = x_1819;
}
lean_ctor_set(x_1897, 0, x_16);
lean_ctor_set(x_1897, 1, x_1820);
lean_ctor_set_usize(x_1897, 2, x_1818);
x_1898 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1898, 0, x_1897);
lean_ctor_set(x_1898, 1, x_1815);
lean_ctor_set_usize(x_1898, 2, x_1816);
lean_ctor_set(x_13, 0, x_1898);
x_1899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1899, 0, x_12);
lean_ctor_set(x_1899, 1, x_17);
x_1900 = 1;
lean_inc(x_1899);
x_1901 = l_Lean_Syntax_isTermId_x3f(x_1899, x_1900);
if (lean_obj_tag(x_1901) == 0)
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; 
lean_dec(x_1899);
x_1902 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1903 = lean_ctor_get(x_1902, 0);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1902, 1);
lean_inc(x_1904);
lean_dec(x_1902);
x_1905 = lean_unsigned_to_nat(1u);
x_1906 = lean_nat_add(x_3, x_1905);
lean_dec(x_3);
x_1907 = l_Lean_mkHole(x_11);
lean_inc(x_1903);
x_1908 = l_Lean_Elab_Term_mkExplicitBinder(x_1903, x_1907);
x_1909 = lean_array_push(x_4, x_1908);
lean_inc(x_5);
x_1910 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1906, x_1909, x_5, x_1904);
if (lean_obj_tag(x_1910) == 0)
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
x_1911 = lean_ctor_get(x_1910, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1910, 1);
lean_inc(x_1912);
lean_dec(x_1910);
x_1913 = lean_ctor_get(x_1911, 0);
lean_inc(x_1913);
x_1914 = lean_ctor_get(x_1911, 1);
lean_inc(x_1914);
if (lean_is_exclusive(x_1911)) {
 lean_ctor_release(x_1911, 0);
 lean_ctor_release(x_1911, 1);
 x_1915 = x_1911;
} else {
 lean_dec_ref(x_1911);
 x_1915 = lean_box(0);
}
x_1916 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1912);
lean_dec(x_5);
x_1917 = lean_ctor_get(x_1916, 1);
lean_inc(x_1917);
lean_dec(x_1916);
x_1918 = l_Lean_Elab_Term_getMainModule___rarg(x_1917);
x_1919 = lean_ctor_get(x_1918, 1);
lean_inc(x_1919);
if (lean_is_exclusive(x_1918)) {
 lean_ctor_release(x_1918, 0);
 lean_ctor_release(x_1918, 1);
 x_1920 = x_1918;
} else {
 lean_dec_ref(x_1918);
 x_1920 = lean_box(0);
}
x_1921 = l_Array_empty___closed__1;
x_1922 = lean_array_push(x_1921, x_1903);
x_1923 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1924 = lean_array_push(x_1922, x_1923);
x_1925 = l_Lean_mkTermIdFromIdent___closed__2;
x_1926 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1926, 0, x_1925);
lean_ctor_set(x_1926, 1, x_1924);
x_1927 = lean_array_push(x_1921, x_1926);
x_1928 = l_Lean_nullKind___closed__2;
x_1929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1929, 0, x_1928);
lean_ctor_set(x_1929, 1, x_1927);
x_1930 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_1931 = lean_array_push(x_1930, x_1929);
x_1932 = lean_array_push(x_1931, x_1923);
x_1933 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_1934 = lean_array_push(x_1932, x_1933);
x_1935 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_1936 = lean_array_push(x_1934, x_1935);
lean_inc(x_11);
x_1937 = lean_array_push(x_1921, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1938 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1938 = lean_box(0);
}
if (lean_is_scalar(x_1938)) {
 x_1939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1939 = x_1938;
}
lean_ctor_set(x_1939, 0, x_1928);
lean_ctor_set(x_1939, 1, x_1937);
x_1940 = lean_array_push(x_1921, x_1939);
x_1941 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1942 = lean_array_push(x_1940, x_1941);
x_1943 = lean_array_push(x_1942, x_1914);
x_1944 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1945 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1945, 0, x_1944);
lean_ctor_set(x_1945, 1, x_1943);
x_1946 = lean_array_push(x_1921, x_1945);
x_1947 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1947, 0, x_1928);
lean_ctor_set(x_1947, 1, x_1946);
x_1948 = lean_array_push(x_1936, x_1947);
x_1949 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1950 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1950, 0, x_1949);
lean_ctor_set(x_1950, 1, x_1948);
if (lean_is_scalar(x_1915)) {
 x_1951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1951 = x_1915;
}
lean_ctor_set(x_1951, 0, x_1913);
lean_ctor_set(x_1951, 1, x_1950);
if (lean_is_scalar(x_1920)) {
 x_1952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1952 = x_1920;
}
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_1919);
return x_1952;
}
else
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; 
lean_dec(x_1903);
lean_dec(x_11);
lean_dec(x_5);
x_1953 = lean_ctor_get(x_1910, 0);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1910, 1);
lean_inc(x_1954);
if (lean_is_exclusive(x_1910)) {
 lean_ctor_release(x_1910, 0);
 lean_ctor_release(x_1910, 1);
 x_1955 = x_1910;
} else {
 lean_dec_ref(x_1910);
 x_1955 = lean_box(0);
}
if (lean_is_scalar(x_1955)) {
 x_1956 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1956 = x_1955;
}
lean_ctor_set(x_1956, 0, x_1953);
lean_ctor_set(x_1956, 1, x_1954);
return x_1956;
}
}
else
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; uint8_t x_1960; 
lean_dec(x_11);
x_1957 = lean_ctor_get(x_1901, 0);
lean_inc(x_1957);
lean_dec(x_1901);
x_1958 = lean_ctor_get(x_1957, 0);
lean_inc(x_1958);
x_1959 = lean_ctor_get(x_1957, 1);
lean_inc(x_1959);
lean_dec(x_1957);
x_1960 = l_Lean_Syntax_isNone(x_1959);
lean_dec(x_1959);
if (x_1960 == 0)
{
lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; 
lean_dec(x_1958);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1961 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_1962 = l_Lean_Elab_Term_throwError___rarg(x_1899, x_1961, x_5, x_6);
lean_dec(x_1899);
x_1963 = lean_ctor_get(x_1962, 0);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1962, 1);
lean_inc(x_1964);
if (lean_is_exclusive(x_1962)) {
 lean_ctor_release(x_1962, 0);
 lean_ctor_release(x_1962, 1);
 x_1965 = x_1962;
} else {
 lean_dec_ref(x_1962);
 x_1965 = lean_box(0);
}
if (lean_is_scalar(x_1965)) {
 x_1966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1966 = x_1965;
}
lean_ctor_set(x_1966, 0, x_1963);
lean_ctor_set(x_1966, 1, x_1964);
return x_1966;
}
else
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; 
x_1967 = l_Lean_mkHole(x_1899);
lean_dec(x_1899);
x_1968 = lean_unsigned_to_nat(1u);
x_1969 = lean_nat_add(x_3, x_1968);
lean_dec(x_3);
x_1970 = l_Lean_Elab_Term_mkExplicitBinder(x_1958, x_1967);
x_1971 = lean_array_push(x_4, x_1970);
x_3 = x_1969;
x_4 = x_1971;
goto _start;
}
}
}
else
{
lean_object* x_1973; uint8_t x_1974; 
lean_dec(x_1815);
x_1973 = l_Lean_mkAppStx___closed__5;
x_1974 = lean_string_dec_eq(x_22, x_1973);
if (x_1974 == 0)
{
lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; uint8_t x_1978; lean_object* x_1979; 
if (lean_is_scalar(x_1819)) {
 x_1975 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_1975 = x_1819;
}
lean_ctor_set(x_1975, 0, x_16);
lean_ctor_set(x_1975, 1, x_1820);
lean_ctor_set_usize(x_1975, 2, x_1818);
x_1976 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1976, 0, x_1975);
lean_ctor_set(x_1976, 1, x_1895);
lean_ctor_set_usize(x_1976, 2, x_1816);
lean_ctor_set(x_13, 0, x_1976);
x_1977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1977, 0, x_12);
lean_ctor_set(x_1977, 1, x_17);
x_1978 = 1;
lean_inc(x_1977);
x_1979 = l_Lean_Syntax_isTermId_x3f(x_1977, x_1978);
if (lean_obj_tag(x_1979) == 0)
{
lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
lean_dec(x_1977);
x_1980 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_1981 = lean_ctor_get(x_1980, 0);
lean_inc(x_1981);
x_1982 = lean_ctor_get(x_1980, 1);
lean_inc(x_1982);
lean_dec(x_1980);
x_1983 = lean_unsigned_to_nat(1u);
x_1984 = lean_nat_add(x_3, x_1983);
lean_dec(x_3);
x_1985 = l_Lean_mkHole(x_11);
lean_inc(x_1981);
x_1986 = l_Lean_Elab_Term_mkExplicitBinder(x_1981, x_1985);
x_1987 = lean_array_push(x_4, x_1986);
lean_inc(x_5);
x_1988 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_1984, x_1987, x_5, x_1982);
if (lean_obj_tag(x_1988) == 0)
{
lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; 
x_1989 = lean_ctor_get(x_1988, 0);
lean_inc(x_1989);
x_1990 = lean_ctor_get(x_1988, 1);
lean_inc(x_1990);
lean_dec(x_1988);
x_1991 = lean_ctor_get(x_1989, 0);
lean_inc(x_1991);
x_1992 = lean_ctor_get(x_1989, 1);
lean_inc(x_1992);
if (lean_is_exclusive(x_1989)) {
 lean_ctor_release(x_1989, 0);
 lean_ctor_release(x_1989, 1);
 x_1993 = x_1989;
} else {
 lean_dec_ref(x_1989);
 x_1993 = lean_box(0);
}
x_1994 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1990);
lean_dec(x_5);
x_1995 = lean_ctor_get(x_1994, 1);
lean_inc(x_1995);
lean_dec(x_1994);
x_1996 = l_Lean_Elab_Term_getMainModule___rarg(x_1995);
x_1997 = lean_ctor_get(x_1996, 1);
lean_inc(x_1997);
if (lean_is_exclusive(x_1996)) {
 lean_ctor_release(x_1996, 0);
 lean_ctor_release(x_1996, 1);
 x_1998 = x_1996;
} else {
 lean_dec_ref(x_1996);
 x_1998 = lean_box(0);
}
x_1999 = l_Array_empty___closed__1;
x_2000 = lean_array_push(x_1999, x_1981);
x_2001 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2002 = lean_array_push(x_2000, x_2001);
x_2003 = l_Lean_mkTermIdFromIdent___closed__2;
x_2004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2004, 0, x_2003);
lean_ctor_set(x_2004, 1, x_2002);
x_2005 = lean_array_push(x_1999, x_2004);
x_2006 = l_Lean_nullKind___closed__2;
x_2007 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2007, 0, x_2006);
lean_ctor_set(x_2007, 1, x_2005);
x_2008 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2009 = lean_array_push(x_2008, x_2007);
x_2010 = lean_array_push(x_2009, x_2001);
x_2011 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2012 = lean_array_push(x_2010, x_2011);
x_2013 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2014 = lean_array_push(x_2012, x_2013);
lean_inc(x_11);
x_2015 = lean_array_push(x_1999, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2016 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2016 = lean_box(0);
}
if (lean_is_scalar(x_2016)) {
 x_2017 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2017 = x_2016;
}
lean_ctor_set(x_2017, 0, x_2006);
lean_ctor_set(x_2017, 1, x_2015);
x_2018 = lean_array_push(x_1999, x_2017);
x_2019 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2020 = lean_array_push(x_2018, x_2019);
x_2021 = lean_array_push(x_2020, x_1992);
x_2022 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2023, 0, x_2022);
lean_ctor_set(x_2023, 1, x_2021);
x_2024 = lean_array_push(x_1999, x_2023);
x_2025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2025, 0, x_2006);
lean_ctor_set(x_2025, 1, x_2024);
x_2026 = lean_array_push(x_2014, x_2025);
x_2027 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2028, 0, x_2027);
lean_ctor_set(x_2028, 1, x_2026);
if (lean_is_scalar(x_1993)) {
 x_2029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2029 = x_1993;
}
lean_ctor_set(x_2029, 0, x_1991);
lean_ctor_set(x_2029, 1, x_2028);
if (lean_is_scalar(x_1998)) {
 x_2030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2030 = x_1998;
}
lean_ctor_set(x_2030, 0, x_2029);
lean_ctor_set(x_2030, 1, x_1997);
return x_2030;
}
else
{
lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; 
lean_dec(x_1981);
lean_dec(x_11);
lean_dec(x_5);
x_2031 = lean_ctor_get(x_1988, 0);
lean_inc(x_2031);
x_2032 = lean_ctor_get(x_1988, 1);
lean_inc(x_2032);
if (lean_is_exclusive(x_1988)) {
 lean_ctor_release(x_1988, 0);
 lean_ctor_release(x_1988, 1);
 x_2033 = x_1988;
} else {
 lean_dec_ref(x_1988);
 x_2033 = lean_box(0);
}
if (lean_is_scalar(x_2033)) {
 x_2034 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2034 = x_2033;
}
lean_ctor_set(x_2034, 0, x_2031);
lean_ctor_set(x_2034, 1, x_2032);
return x_2034;
}
}
else
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; uint8_t x_2038; 
lean_dec(x_11);
x_2035 = lean_ctor_get(x_1979, 0);
lean_inc(x_2035);
lean_dec(x_1979);
x_2036 = lean_ctor_get(x_2035, 0);
lean_inc(x_2036);
x_2037 = lean_ctor_get(x_2035, 1);
lean_inc(x_2037);
lean_dec(x_2035);
x_2038 = l_Lean_Syntax_isNone(x_2037);
lean_dec(x_2037);
if (x_2038 == 0)
{
lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; 
lean_dec(x_2036);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2039 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_2040 = l_Lean_Elab_Term_throwError___rarg(x_1977, x_2039, x_5, x_6);
lean_dec(x_1977);
x_2041 = lean_ctor_get(x_2040, 0);
lean_inc(x_2041);
x_2042 = lean_ctor_get(x_2040, 1);
lean_inc(x_2042);
if (lean_is_exclusive(x_2040)) {
 lean_ctor_release(x_2040, 0);
 lean_ctor_release(x_2040, 1);
 x_2043 = x_2040;
} else {
 lean_dec_ref(x_2040);
 x_2043 = lean_box(0);
}
if (lean_is_scalar(x_2043)) {
 x_2044 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2044 = x_2043;
}
lean_ctor_set(x_2044, 0, x_2041);
lean_ctor_set(x_2044, 1, x_2042);
return x_2044;
}
else
{
lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; 
x_2045 = l_Lean_mkHole(x_1977);
lean_dec(x_1977);
x_2046 = lean_unsigned_to_nat(1u);
x_2047 = lean_nat_add(x_3, x_2046);
lean_dec(x_3);
x_2048 = l_Lean_Elab_Term_mkExplicitBinder(x_2036, x_2045);
x_2049 = lean_array_push(x_4, x_2048);
x_3 = x_2047;
x_4 = x_2049;
goto _start;
}
}
}
else
{
lean_object* x_2051; uint8_t x_2052; 
lean_dec(x_22);
x_2051 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_2052 = lean_string_dec_eq(x_19, x_2051);
if (x_2052 == 0)
{
lean_object* x_2053; uint8_t x_2054; 
x_2053 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_2054 = lean_string_dec_eq(x_19, x_2053);
if (x_2054 == 0)
{
lean_object* x_2055; uint8_t x_2056; 
x_2055 = l_Lean_mkHole___closed__1;
x_2056 = lean_string_dec_eq(x_19, x_2055);
if (x_2056 == 0)
{
lean_object* x_2057; uint8_t x_2058; 
x_2057 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_2058 = lean_string_dec_eq(x_19, x_2057);
if (x_2058 == 0)
{
lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; uint8_t x_2062; lean_object* x_2063; 
if (lean_is_scalar(x_1819)) {
 x_2059 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2059 = x_1819;
}
lean_ctor_set(x_2059, 0, x_16);
lean_ctor_set(x_2059, 1, x_1820);
lean_ctor_set_usize(x_2059, 2, x_1818);
x_2060 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2060, 0, x_2059);
lean_ctor_set(x_2060, 1, x_1895);
lean_ctor_set_usize(x_2060, 2, x_1816);
lean_ctor_set(x_13, 1, x_1973);
lean_ctor_set(x_13, 0, x_2060);
x_2061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2061, 0, x_12);
lean_ctor_set(x_2061, 1, x_17);
x_2062 = 1;
lean_inc(x_2061);
x_2063 = l_Lean_Syntax_isTermId_x3f(x_2061, x_2062);
if (lean_obj_tag(x_2063) == 0)
{
lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; 
lean_dec(x_2061);
x_2064 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2065 = lean_ctor_get(x_2064, 0);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_2064, 1);
lean_inc(x_2066);
lean_dec(x_2064);
x_2067 = lean_unsigned_to_nat(1u);
x_2068 = lean_nat_add(x_3, x_2067);
lean_dec(x_3);
x_2069 = l_Lean_mkHole(x_11);
lean_inc(x_2065);
x_2070 = l_Lean_Elab_Term_mkExplicitBinder(x_2065, x_2069);
x_2071 = lean_array_push(x_4, x_2070);
lean_inc(x_5);
x_2072 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2068, x_2071, x_5, x_2066);
if (lean_obj_tag(x_2072) == 0)
{
lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; 
x_2073 = lean_ctor_get(x_2072, 0);
lean_inc(x_2073);
x_2074 = lean_ctor_get(x_2072, 1);
lean_inc(x_2074);
lean_dec(x_2072);
x_2075 = lean_ctor_get(x_2073, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2073, 1);
lean_inc(x_2076);
if (lean_is_exclusive(x_2073)) {
 lean_ctor_release(x_2073, 0);
 lean_ctor_release(x_2073, 1);
 x_2077 = x_2073;
} else {
 lean_dec_ref(x_2073);
 x_2077 = lean_box(0);
}
x_2078 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2074);
lean_dec(x_5);
x_2079 = lean_ctor_get(x_2078, 1);
lean_inc(x_2079);
lean_dec(x_2078);
x_2080 = l_Lean_Elab_Term_getMainModule___rarg(x_2079);
x_2081 = lean_ctor_get(x_2080, 1);
lean_inc(x_2081);
if (lean_is_exclusive(x_2080)) {
 lean_ctor_release(x_2080, 0);
 lean_ctor_release(x_2080, 1);
 x_2082 = x_2080;
} else {
 lean_dec_ref(x_2080);
 x_2082 = lean_box(0);
}
x_2083 = l_Array_empty___closed__1;
x_2084 = lean_array_push(x_2083, x_2065);
x_2085 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2086 = lean_array_push(x_2084, x_2085);
x_2087 = l_Lean_mkTermIdFromIdent___closed__2;
x_2088 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2088, 0, x_2087);
lean_ctor_set(x_2088, 1, x_2086);
x_2089 = lean_array_push(x_2083, x_2088);
x_2090 = l_Lean_nullKind___closed__2;
x_2091 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2091, 0, x_2090);
lean_ctor_set(x_2091, 1, x_2089);
x_2092 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2093 = lean_array_push(x_2092, x_2091);
x_2094 = lean_array_push(x_2093, x_2085);
x_2095 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2096 = lean_array_push(x_2094, x_2095);
x_2097 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2098 = lean_array_push(x_2096, x_2097);
lean_inc(x_11);
x_2099 = lean_array_push(x_2083, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2100 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2100 = lean_box(0);
}
if (lean_is_scalar(x_2100)) {
 x_2101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2101 = x_2100;
}
lean_ctor_set(x_2101, 0, x_2090);
lean_ctor_set(x_2101, 1, x_2099);
x_2102 = lean_array_push(x_2083, x_2101);
x_2103 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2104 = lean_array_push(x_2102, x_2103);
x_2105 = lean_array_push(x_2104, x_2076);
x_2106 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2107, 0, x_2106);
lean_ctor_set(x_2107, 1, x_2105);
x_2108 = lean_array_push(x_2083, x_2107);
x_2109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2109, 0, x_2090);
lean_ctor_set(x_2109, 1, x_2108);
x_2110 = lean_array_push(x_2098, x_2109);
x_2111 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2112, 0, x_2111);
lean_ctor_set(x_2112, 1, x_2110);
if (lean_is_scalar(x_2077)) {
 x_2113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2113 = x_2077;
}
lean_ctor_set(x_2113, 0, x_2075);
lean_ctor_set(x_2113, 1, x_2112);
if (lean_is_scalar(x_2082)) {
 x_2114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2114 = x_2082;
}
lean_ctor_set(x_2114, 0, x_2113);
lean_ctor_set(x_2114, 1, x_2081);
return x_2114;
}
else
{
lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; 
lean_dec(x_2065);
lean_dec(x_11);
lean_dec(x_5);
x_2115 = lean_ctor_get(x_2072, 0);
lean_inc(x_2115);
x_2116 = lean_ctor_get(x_2072, 1);
lean_inc(x_2116);
if (lean_is_exclusive(x_2072)) {
 lean_ctor_release(x_2072, 0);
 lean_ctor_release(x_2072, 1);
 x_2117 = x_2072;
} else {
 lean_dec_ref(x_2072);
 x_2117 = lean_box(0);
}
if (lean_is_scalar(x_2117)) {
 x_2118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2118 = x_2117;
}
lean_ctor_set(x_2118, 0, x_2115);
lean_ctor_set(x_2118, 1, x_2116);
return x_2118;
}
}
else
{
lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; uint8_t x_2122; 
lean_dec(x_11);
x_2119 = lean_ctor_get(x_2063, 0);
lean_inc(x_2119);
lean_dec(x_2063);
x_2120 = lean_ctor_get(x_2119, 0);
lean_inc(x_2120);
x_2121 = lean_ctor_get(x_2119, 1);
lean_inc(x_2121);
lean_dec(x_2119);
x_2122 = l_Lean_Syntax_isNone(x_2121);
lean_dec(x_2121);
if (x_2122 == 0)
{
lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; 
lean_dec(x_2120);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2123 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_2124 = l_Lean_Elab_Term_throwError___rarg(x_2061, x_2123, x_5, x_6);
lean_dec(x_2061);
x_2125 = lean_ctor_get(x_2124, 0);
lean_inc(x_2125);
x_2126 = lean_ctor_get(x_2124, 1);
lean_inc(x_2126);
if (lean_is_exclusive(x_2124)) {
 lean_ctor_release(x_2124, 0);
 lean_ctor_release(x_2124, 1);
 x_2127 = x_2124;
} else {
 lean_dec_ref(x_2124);
 x_2127 = lean_box(0);
}
if (lean_is_scalar(x_2127)) {
 x_2128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2128 = x_2127;
}
lean_ctor_set(x_2128, 0, x_2125);
lean_ctor_set(x_2128, 1, x_2126);
return x_2128;
}
else
{
lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; 
x_2129 = l_Lean_mkHole(x_2061);
lean_dec(x_2061);
x_2130 = lean_unsigned_to_nat(1u);
x_2131 = lean_nat_add(x_3, x_2130);
lean_dec(x_3);
x_2132 = l_Lean_Elab_Term_mkExplicitBinder(x_2120, x_2129);
x_2133 = lean_array_push(x_4, x_2132);
x_3 = x_2131;
x_4 = x_2133;
goto _start;
}
}
}
else
{
lean_object* x_2135; lean_object* x_2136; uint8_t x_2137; 
lean_dec(x_1819);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2135 = lean_unsigned_to_nat(1u);
x_2136 = l_Lean_Syntax_getArg(x_11, x_2135);
x_2137 = l_Lean_Syntax_isNone(x_2136);
if (x_2137 == 0)
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; uint8_t x_2141; 
x_2138 = lean_unsigned_to_nat(0u);
x_2139 = l_Lean_Syntax_getArg(x_2136, x_2138);
x_2140 = l_Lean_Syntax_getArg(x_2136, x_2135);
lean_dec(x_2136);
x_2141 = l_Lean_Syntax_isNone(x_2140);
if (x_2141 == 0)
{
lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; uint8_t x_2149; 
x_2142 = l_Lean_Syntax_getArg(x_2140, x_2138);
lean_dec(x_2140);
lean_inc(x_2142);
x_2143 = l_Lean_Syntax_getKind(x_2142);
x_2144 = lean_name_mk_string(x_16, x_1820);
x_2145 = lean_name_mk_string(x_2144, x_1895);
x_2146 = lean_name_mk_string(x_2145, x_1973);
x_2147 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_2148 = lean_name_mk_string(x_2146, x_2147);
x_2149 = lean_name_eq(x_2143, x_2148);
lean_dec(x_2148);
lean_dec(x_2143);
if (x_2149 == 0)
{
lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; 
lean_dec(x_2142);
lean_dec(x_2139);
x_2150 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2151 = lean_ctor_get(x_2150, 0);
lean_inc(x_2151);
x_2152 = lean_ctor_get(x_2150, 1);
lean_inc(x_2152);
lean_dec(x_2150);
x_2153 = lean_nat_add(x_3, x_2135);
lean_dec(x_3);
x_2154 = l_Lean_mkHole(x_11);
lean_inc(x_2151);
x_2155 = l_Lean_Elab_Term_mkExplicitBinder(x_2151, x_2154);
x_2156 = lean_array_push(x_4, x_2155);
lean_inc(x_5);
x_2157 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2153, x_2156, x_5, x_2152);
if (lean_obj_tag(x_2157) == 0)
{
lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; 
x_2158 = lean_ctor_get(x_2157, 0);
lean_inc(x_2158);
x_2159 = lean_ctor_get(x_2157, 1);
lean_inc(x_2159);
lean_dec(x_2157);
x_2160 = lean_ctor_get(x_2158, 0);
lean_inc(x_2160);
x_2161 = lean_ctor_get(x_2158, 1);
lean_inc(x_2161);
if (lean_is_exclusive(x_2158)) {
 lean_ctor_release(x_2158, 0);
 lean_ctor_release(x_2158, 1);
 x_2162 = x_2158;
} else {
 lean_dec_ref(x_2158);
 x_2162 = lean_box(0);
}
x_2163 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2159);
lean_dec(x_5);
x_2164 = lean_ctor_get(x_2163, 1);
lean_inc(x_2164);
lean_dec(x_2163);
x_2165 = l_Lean_Elab_Term_getMainModule___rarg(x_2164);
x_2166 = lean_ctor_get(x_2165, 1);
lean_inc(x_2166);
if (lean_is_exclusive(x_2165)) {
 lean_ctor_release(x_2165, 0);
 lean_ctor_release(x_2165, 1);
 x_2167 = x_2165;
} else {
 lean_dec_ref(x_2165);
 x_2167 = lean_box(0);
}
x_2168 = l_Array_empty___closed__1;
x_2169 = lean_array_push(x_2168, x_2151);
x_2170 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2171 = lean_array_push(x_2169, x_2170);
x_2172 = l_Lean_mkTermIdFromIdent___closed__2;
x_2173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2173, 0, x_2172);
lean_ctor_set(x_2173, 1, x_2171);
x_2174 = lean_array_push(x_2168, x_2173);
x_2175 = l_Lean_nullKind___closed__2;
x_2176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2176, 0, x_2175);
lean_ctor_set(x_2176, 1, x_2174);
x_2177 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2178 = lean_array_push(x_2177, x_2176);
x_2179 = lean_array_push(x_2178, x_2170);
x_2180 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2181 = lean_array_push(x_2179, x_2180);
x_2182 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2183 = lean_array_push(x_2181, x_2182);
lean_inc(x_11);
x_2184 = lean_array_push(x_2168, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2185 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2185 = lean_box(0);
}
if (lean_is_scalar(x_2185)) {
 x_2186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2186 = x_2185;
}
lean_ctor_set(x_2186, 0, x_2175);
lean_ctor_set(x_2186, 1, x_2184);
x_2187 = lean_array_push(x_2168, x_2186);
x_2188 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2189 = lean_array_push(x_2187, x_2188);
x_2190 = lean_array_push(x_2189, x_2161);
x_2191 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2192, 0, x_2191);
lean_ctor_set(x_2192, 1, x_2190);
x_2193 = lean_array_push(x_2168, x_2192);
x_2194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2194, 0, x_2175);
lean_ctor_set(x_2194, 1, x_2193);
x_2195 = lean_array_push(x_2183, x_2194);
x_2196 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2197, 0, x_2196);
lean_ctor_set(x_2197, 1, x_2195);
if (lean_is_scalar(x_2162)) {
 x_2198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2198 = x_2162;
}
lean_ctor_set(x_2198, 0, x_2160);
lean_ctor_set(x_2198, 1, x_2197);
if (lean_is_scalar(x_2167)) {
 x_2199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2199 = x_2167;
}
lean_ctor_set(x_2199, 0, x_2198);
lean_ctor_set(x_2199, 1, x_2166);
return x_2199;
}
else
{
lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; 
lean_dec(x_2151);
lean_dec(x_11);
lean_dec(x_5);
x_2200 = lean_ctor_get(x_2157, 0);
lean_inc(x_2200);
x_2201 = lean_ctor_get(x_2157, 1);
lean_inc(x_2201);
if (lean_is_exclusive(x_2157)) {
 lean_ctor_release(x_2157, 0);
 lean_ctor_release(x_2157, 1);
 x_2202 = x_2157;
} else {
 lean_dec_ref(x_2157);
 x_2202 = lean_box(0);
}
if (lean_is_scalar(x_2202)) {
 x_2203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2203 = x_2202;
}
lean_ctor_set(x_2203, 0, x_2200);
lean_ctor_set(x_2203, 1, x_2201);
return x_2203;
}
}
else
{
lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; 
x_2204 = l_Lean_Syntax_getArg(x_2142, x_2135);
lean_dec(x_2142);
x_2205 = l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(x_2139, x_5, x_6);
x_2206 = lean_ctor_get(x_2205, 0);
lean_inc(x_2206);
if (lean_obj_tag(x_2206) == 0)
{
lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; 
lean_dec(x_2204);
x_2207 = lean_ctor_get(x_2205, 1);
lean_inc(x_2207);
lean_dec(x_2205);
x_2208 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_2207);
x_2209 = lean_ctor_get(x_2208, 0);
lean_inc(x_2209);
x_2210 = lean_ctor_get(x_2208, 1);
lean_inc(x_2210);
lean_dec(x_2208);
x_2211 = lean_nat_add(x_3, x_2135);
lean_dec(x_3);
x_2212 = l_Lean_mkHole(x_11);
lean_inc(x_2209);
x_2213 = l_Lean_Elab_Term_mkExplicitBinder(x_2209, x_2212);
x_2214 = lean_array_push(x_4, x_2213);
lean_inc(x_5);
x_2215 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2211, x_2214, x_5, x_2210);
if (lean_obj_tag(x_2215) == 0)
{
lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
x_2216 = lean_ctor_get(x_2215, 0);
lean_inc(x_2216);
x_2217 = lean_ctor_get(x_2215, 1);
lean_inc(x_2217);
lean_dec(x_2215);
x_2218 = lean_ctor_get(x_2216, 0);
lean_inc(x_2218);
x_2219 = lean_ctor_get(x_2216, 1);
lean_inc(x_2219);
if (lean_is_exclusive(x_2216)) {
 lean_ctor_release(x_2216, 0);
 lean_ctor_release(x_2216, 1);
 x_2220 = x_2216;
} else {
 lean_dec_ref(x_2216);
 x_2220 = lean_box(0);
}
x_2221 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2217);
lean_dec(x_5);
x_2222 = lean_ctor_get(x_2221, 1);
lean_inc(x_2222);
lean_dec(x_2221);
x_2223 = l_Lean_Elab_Term_getMainModule___rarg(x_2222);
x_2224 = lean_ctor_get(x_2223, 1);
lean_inc(x_2224);
if (lean_is_exclusive(x_2223)) {
 lean_ctor_release(x_2223, 0);
 lean_ctor_release(x_2223, 1);
 x_2225 = x_2223;
} else {
 lean_dec_ref(x_2223);
 x_2225 = lean_box(0);
}
x_2226 = l_Array_empty___closed__1;
x_2227 = lean_array_push(x_2226, x_2209);
x_2228 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2229 = lean_array_push(x_2227, x_2228);
x_2230 = l_Lean_mkTermIdFromIdent___closed__2;
x_2231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2231, 0, x_2230);
lean_ctor_set(x_2231, 1, x_2229);
x_2232 = lean_array_push(x_2226, x_2231);
x_2233 = l_Lean_nullKind___closed__2;
x_2234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2234, 0, x_2233);
lean_ctor_set(x_2234, 1, x_2232);
x_2235 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2236 = lean_array_push(x_2235, x_2234);
x_2237 = lean_array_push(x_2236, x_2228);
x_2238 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2239 = lean_array_push(x_2237, x_2238);
x_2240 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2241 = lean_array_push(x_2239, x_2240);
lean_inc(x_11);
x_2242 = lean_array_push(x_2226, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2243 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2243 = lean_box(0);
}
if (lean_is_scalar(x_2243)) {
 x_2244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2244 = x_2243;
}
lean_ctor_set(x_2244, 0, x_2233);
lean_ctor_set(x_2244, 1, x_2242);
x_2245 = lean_array_push(x_2226, x_2244);
x_2246 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2247 = lean_array_push(x_2245, x_2246);
x_2248 = lean_array_push(x_2247, x_2219);
x_2249 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2250, 0, x_2249);
lean_ctor_set(x_2250, 1, x_2248);
x_2251 = lean_array_push(x_2226, x_2250);
x_2252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2252, 0, x_2233);
lean_ctor_set(x_2252, 1, x_2251);
x_2253 = lean_array_push(x_2241, x_2252);
x_2254 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2255, 0, x_2254);
lean_ctor_set(x_2255, 1, x_2253);
if (lean_is_scalar(x_2220)) {
 x_2256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2256 = x_2220;
}
lean_ctor_set(x_2256, 0, x_2218);
lean_ctor_set(x_2256, 1, x_2255);
if (lean_is_scalar(x_2225)) {
 x_2257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2257 = x_2225;
}
lean_ctor_set(x_2257, 0, x_2256);
lean_ctor_set(x_2257, 1, x_2224);
return x_2257;
}
else
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; 
lean_dec(x_2209);
lean_dec(x_11);
lean_dec(x_5);
x_2258 = lean_ctor_get(x_2215, 0);
lean_inc(x_2258);
x_2259 = lean_ctor_get(x_2215, 1);
lean_inc(x_2259);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2260 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2260 = lean_box(0);
}
if (lean_is_scalar(x_2260)) {
 x_2261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2261 = x_2260;
}
lean_ctor_set(x_2261, 0, x_2258);
lean_ctor_set(x_2261, 1, x_2259);
return x_2261;
}
}
else
{
lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; 
lean_dec(x_11);
x_2262 = lean_ctor_get(x_2205, 1);
lean_inc(x_2262);
lean_dec(x_2205);
x_2263 = lean_ctor_get(x_2206, 0);
lean_inc(x_2263);
lean_dec(x_2206);
x_2264 = lean_nat_add(x_3, x_2135);
lean_dec(x_3);
x_2265 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(x_2204, x_2138, x_2263);
x_2266 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2265, x_2265, x_2138, x_4);
lean_dec(x_2265);
x_3 = x_2264;
x_4 = x_2266;
x_6 = x_2262;
goto _start;
}
}
}
else
{
lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; 
lean_dec(x_2140);
lean_dec(x_2139);
x_2268 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2269 = lean_ctor_get(x_2268, 0);
lean_inc(x_2269);
x_2270 = lean_ctor_get(x_2268, 1);
lean_inc(x_2270);
lean_dec(x_2268);
x_2271 = lean_nat_add(x_3, x_2135);
lean_dec(x_3);
x_2272 = l_Lean_mkHole(x_11);
lean_inc(x_2269);
x_2273 = l_Lean_Elab_Term_mkExplicitBinder(x_2269, x_2272);
x_2274 = lean_array_push(x_4, x_2273);
lean_inc(x_5);
x_2275 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2271, x_2274, x_5, x_2270);
if (lean_obj_tag(x_2275) == 0)
{
lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; 
x_2276 = lean_ctor_get(x_2275, 0);
lean_inc(x_2276);
x_2277 = lean_ctor_get(x_2275, 1);
lean_inc(x_2277);
lean_dec(x_2275);
x_2278 = lean_ctor_get(x_2276, 0);
lean_inc(x_2278);
x_2279 = lean_ctor_get(x_2276, 1);
lean_inc(x_2279);
if (lean_is_exclusive(x_2276)) {
 lean_ctor_release(x_2276, 0);
 lean_ctor_release(x_2276, 1);
 x_2280 = x_2276;
} else {
 lean_dec_ref(x_2276);
 x_2280 = lean_box(0);
}
x_2281 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2277);
lean_dec(x_5);
x_2282 = lean_ctor_get(x_2281, 1);
lean_inc(x_2282);
lean_dec(x_2281);
x_2283 = l_Lean_Elab_Term_getMainModule___rarg(x_2282);
x_2284 = lean_ctor_get(x_2283, 1);
lean_inc(x_2284);
if (lean_is_exclusive(x_2283)) {
 lean_ctor_release(x_2283, 0);
 lean_ctor_release(x_2283, 1);
 x_2285 = x_2283;
} else {
 lean_dec_ref(x_2283);
 x_2285 = lean_box(0);
}
x_2286 = l_Array_empty___closed__1;
x_2287 = lean_array_push(x_2286, x_2269);
x_2288 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2289 = lean_array_push(x_2287, x_2288);
x_2290 = l_Lean_mkTermIdFromIdent___closed__2;
x_2291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2291, 0, x_2290);
lean_ctor_set(x_2291, 1, x_2289);
x_2292 = lean_array_push(x_2286, x_2291);
x_2293 = l_Lean_nullKind___closed__2;
x_2294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2294, 0, x_2293);
lean_ctor_set(x_2294, 1, x_2292);
x_2295 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2296 = lean_array_push(x_2295, x_2294);
x_2297 = lean_array_push(x_2296, x_2288);
x_2298 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2299 = lean_array_push(x_2297, x_2298);
x_2300 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2301 = lean_array_push(x_2299, x_2300);
lean_inc(x_11);
x_2302 = lean_array_push(x_2286, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2303 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2303 = lean_box(0);
}
if (lean_is_scalar(x_2303)) {
 x_2304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2304 = x_2303;
}
lean_ctor_set(x_2304, 0, x_2293);
lean_ctor_set(x_2304, 1, x_2302);
x_2305 = lean_array_push(x_2286, x_2304);
x_2306 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2307 = lean_array_push(x_2305, x_2306);
x_2308 = lean_array_push(x_2307, x_2279);
x_2309 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2310, 0, x_2309);
lean_ctor_set(x_2310, 1, x_2308);
x_2311 = lean_array_push(x_2286, x_2310);
x_2312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2312, 0, x_2293);
lean_ctor_set(x_2312, 1, x_2311);
x_2313 = lean_array_push(x_2301, x_2312);
x_2314 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2315, 0, x_2314);
lean_ctor_set(x_2315, 1, x_2313);
if (lean_is_scalar(x_2280)) {
 x_2316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2316 = x_2280;
}
lean_ctor_set(x_2316, 0, x_2278);
lean_ctor_set(x_2316, 1, x_2315);
if (lean_is_scalar(x_2285)) {
 x_2317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2317 = x_2285;
}
lean_ctor_set(x_2317, 0, x_2316);
lean_ctor_set(x_2317, 1, x_2284);
return x_2317;
}
else
{
lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; 
lean_dec(x_2269);
lean_dec(x_11);
lean_dec(x_5);
x_2318 = lean_ctor_get(x_2275, 0);
lean_inc(x_2318);
x_2319 = lean_ctor_get(x_2275, 1);
lean_inc(x_2319);
if (lean_is_exclusive(x_2275)) {
 lean_ctor_release(x_2275, 0);
 lean_ctor_release(x_2275, 1);
 x_2320 = x_2275;
} else {
 lean_dec_ref(x_2275);
 x_2320 = lean_box(0);
}
if (lean_is_scalar(x_2320)) {
 x_2321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2321 = x_2320;
}
lean_ctor_set(x_2321, 0, x_2318);
lean_ctor_set(x_2321, 1, x_2319);
return x_2321;
}
}
}
else
{
lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; 
lean_dec(x_2136);
x_2322 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2323 = lean_ctor_get(x_2322, 0);
lean_inc(x_2323);
x_2324 = lean_ctor_get(x_2322, 1);
lean_inc(x_2324);
lean_dec(x_2322);
x_2325 = lean_nat_add(x_3, x_2135);
lean_dec(x_3);
x_2326 = l_Lean_mkHole(x_11);
lean_inc(x_2323);
x_2327 = l_Lean_Elab_Term_mkExplicitBinder(x_2323, x_2326);
x_2328 = lean_array_push(x_4, x_2327);
lean_inc(x_5);
x_2329 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2325, x_2328, x_5, x_2324);
if (lean_obj_tag(x_2329) == 0)
{
lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; 
x_2330 = lean_ctor_get(x_2329, 0);
lean_inc(x_2330);
x_2331 = lean_ctor_get(x_2329, 1);
lean_inc(x_2331);
lean_dec(x_2329);
x_2332 = lean_ctor_get(x_2330, 0);
lean_inc(x_2332);
x_2333 = lean_ctor_get(x_2330, 1);
lean_inc(x_2333);
if (lean_is_exclusive(x_2330)) {
 lean_ctor_release(x_2330, 0);
 lean_ctor_release(x_2330, 1);
 x_2334 = x_2330;
} else {
 lean_dec_ref(x_2330);
 x_2334 = lean_box(0);
}
x_2335 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2331);
lean_dec(x_5);
x_2336 = lean_ctor_get(x_2335, 1);
lean_inc(x_2336);
lean_dec(x_2335);
x_2337 = l_Lean_Elab_Term_getMainModule___rarg(x_2336);
x_2338 = lean_ctor_get(x_2337, 1);
lean_inc(x_2338);
if (lean_is_exclusive(x_2337)) {
 lean_ctor_release(x_2337, 0);
 lean_ctor_release(x_2337, 1);
 x_2339 = x_2337;
} else {
 lean_dec_ref(x_2337);
 x_2339 = lean_box(0);
}
x_2340 = l_Array_empty___closed__1;
x_2341 = lean_array_push(x_2340, x_2323);
x_2342 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2343 = lean_array_push(x_2341, x_2342);
x_2344 = l_Lean_mkTermIdFromIdent___closed__2;
x_2345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2345, 0, x_2344);
lean_ctor_set(x_2345, 1, x_2343);
x_2346 = lean_array_push(x_2340, x_2345);
x_2347 = l_Lean_nullKind___closed__2;
x_2348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2348, 0, x_2347);
lean_ctor_set(x_2348, 1, x_2346);
x_2349 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2350 = lean_array_push(x_2349, x_2348);
x_2351 = lean_array_push(x_2350, x_2342);
x_2352 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2353 = lean_array_push(x_2351, x_2352);
x_2354 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2355 = lean_array_push(x_2353, x_2354);
lean_inc(x_11);
x_2356 = lean_array_push(x_2340, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2357 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2357 = lean_box(0);
}
if (lean_is_scalar(x_2357)) {
 x_2358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2358 = x_2357;
}
lean_ctor_set(x_2358, 0, x_2347);
lean_ctor_set(x_2358, 1, x_2356);
x_2359 = lean_array_push(x_2340, x_2358);
x_2360 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2361 = lean_array_push(x_2359, x_2360);
x_2362 = lean_array_push(x_2361, x_2333);
x_2363 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2364, 0, x_2363);
lean_ctor_set(x_2364, 1, x_2362);
x_2365 = lean_array_push(x_2340, x_2364);
x_2366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2366, 0, x_2347);
lean_ctor_set(x_2366, 1, x_2365);
x_2367 = lean_array_push(x_2355, x_2366);
x_2368 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2369, 0, x_2368);
lean_ctor_set(x_2369, 1, x_2367);
if (lean_is_scalar(x_2334)) {
 x_2370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2370 = x_2334;
}
lean_ctor_set(x_2370, 0, x_2332);
lean_ctor_set(x_2370, 1, x_2369);
if (lean_is_scalar(x_2339)) {
 x_2371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2371 = x_2339;
}
lean_ctor_set(x_2371, 0, x_2370);
lean_ctor_set(x_2371, 1, x_2338);
return x_2371;
}
else
{
lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; 
lean_dec(x_2323);
lean_dec(x_11);
lean_dec(x_5);
x_2372 = lean_ctor_get(x_2329, 0);
lean_inc(x_2372);
x_2373 = lean_ctor_get(x_2329, 1);
lean_inc(x_2373);
if (lean_is_exclusive(x_2329)) {
 lean_ctor_release(x_2329, 0);
 lean_ctor_release(x_2329, 1);
 x_2374 = x_2329;
} else {
 lean_dec_ref(x_2329);
 x_2374 = lean_box(0);
}
if (lean_is_scalar(x_2374)) {
 x_2375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2375 = x_2374;
}
lean_ctor_set(x_2375, 0, x_2372);
lean_ctor_set(x_2375, 1, x_2373);
return x_2375;
}
}
}
}
else
{
lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; 
lean_dec(x_1819);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2376 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2377 = lean_ctor_get(x_2376, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2376, 1);
lean_inc(x_2378);
lean_dec(x_2376);
x_2379 = lean_unsigned_to_nat(1u);
x_2380 = lean_nat_add(x_3, x_2379);
lean_dec(x_3);
x_2381 = l_Lean_Elab_Term_mkExplicitBinder(x_2377, x_11);
x_2382 = lean_array_push(x_4, x_2381);
x_3 = x_2380;
x_4 = x_2382;
x_6 = x_2378;
goto _start;
}
}
else
{
lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; 
lean_dec(x_1819);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2384 = lean_unsigned_to_nat(1u);
x_2385 = lean_nat_add(x_3, x_2384);
lean_dec(x_3);
x_2386 = lean_array_push(x_4, x_11);
x_3 = x_2385;
x_4 = x_2386;
goto _start;
}
}
else
{
lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; 
lean_dec(x_1819);
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2388 = lean_unsigned_to_nat(1u);
x_2389 = lean_nat_add(x_3, x_2388);
lean_dec(x_3);
x_2390 = lean_array_push(x_4, x_11);
x_3 = x_2389;
x_4 = x_2390;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_2392; size_t x_2393; lean_object* x_2394; size_t x_2395; lean_object* x_2396; lean_object* x_2397; size_t x_2398; lean_object* x_2399; lean_object* x_2400; uint8_t x_2401; 
x_2392 = lean_ctor_get(x_13, 1);
x_2393 = lean_ctor_get_usize(x_13, 2);
lean_inc(x_2392);
lean_dec(x_13);
x_2394 = lean_ctor_get(x_14, 1);
lean_inc(x_2394);
x_2395 = lean_ctor_get_usize(x_14, 2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2396 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2396 = lean_box(0);
}
x_2397 = lean_ctor_get(x_15, 1);
lean_inc(x_2397);
x_2398 = lean_ctor_get_usize(x_15, 2);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_2399 = x_15;
} else {
 lean_dec_ref(x_15);
 x_2399 = lean_box(0);
}
x_2400 = l_Lean_mkAppStx___closed__1;
x_2401 = lean_string_dec_eq(x_2397, x_2400);
lean_dec(x_2397);
if (x_2401 == 0)
{
uint8_t x_2402; lean_object* x_2403; 
lean_dec(x_2399);
lean_dec(x_2396);
lean_dec(x_2394);
lean_dec(x_2392);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2402 = 1;
lean_inc(x_11);
x_2403 = l_Lean_Syntax_isTermId_x3f(x_11, x_2402);
if (lean_obj_tag(x_2403) == 0)
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; 
x_2404 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2405 = lean_ctor_get(x_2404, 0);
lean_inc(x_2405);
x_2406 = lean_ctor_get(x_2404, 1);
lean_inc(x_2406);
lean_dec(x_2404);
x_2407 = lean_unsigned_to_nat(1u);
x_2408 = lean_nat_add(x_3, x_2407);
lean_dec(x_3);
x_2409 = l_Lean_mkHole(x_11);
lean_inc(x_2405);
x_2410 = l_Lean_Elab_Term_mkExplicitBinder(x_2405, x_2409);
x_2411 = lean_array_push(x_4, x_2410);
lean_inc(x_5);
x_2412 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2408, x_2411, x_5, x_2406);
if (lean_obj_tag(x_2412) == 0)
{
lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; lean_object* x_2454; 
x_2413 = lean_ctor_get(x_2412, 0);
lean_inc(x_2413);
x_2414 = lean_ctor_get(x_2412, 1);
lean_inc(x_2414);
lean_dec(x_2412);
x_2415 = lean_ctor_get(x_2413, 0);
lean_inc(x_2415);
x_2416 = lean_ctor_get(x_2413, 1);
lean_inc(x_2416);
if (lean_is_exclusive(x_2413)) {
 lean_ctor_release(x_2413, 0);
 lean_ctor_release(x_2413, 1);
 x_2417 = x_2413;
} else {
 lean_dec_ref(x_2413);
 x_2417 = lean_box(0);
}
x_2418 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2414);
lean_dec(x_5);
x_2419 = lean_ctor_get(x_2418, 1);
lean_inc(x_2419);
lean_dec(x_2418);
x_2420 = l_Lean_Elab_Term_getMainModule___rarg(x_2419);
x_2421 = lean_ctor_get(x_2420, 1);
lean_inc(x_2421);
if (lean_is_exclusive(x_2420)) {
 lean_ctor_release(x_2420, 0);
 lean_ctor_release(x_2420, 1);
 x_2422 = x_2420;
} else {
 lean_dec_ref(x_2420);
 x_2422 = lean_box(0);
}
x_2423 = l_Array_empty___closed__1;
x_2424 = lean_array_push(x_2423, x_2405);
x_2425 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2426 = lean_array_push(x_2424, x_2425);
x_2427 = l_Lean_mkTermIdFromIdent___closed__2;
x_2428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2428, 0, x_2427);
lean_ctor_set(x_2428, 1, x_2426);
x_2429 = lean_array_push(x_2423, x_2428);
x_2430 = l_Lean_nullKind___closed__2;
x_2431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2431, 0, x_2430);
lean_ctor_set(x_2431, 1, x_2429);
x_2432 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2433 = lean_array_push(x_2432, x_2431);
x_2434 = lean_array_push(x_2433, x_2425);
x_2435 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2436 = lean_array_push(x_2434, x_2435);
x_2437 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2438 = lean_array_push(x_2436, x_2437);
lean_inc(x_11);
x_2439 = lean_array_push(x_2423, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2440 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2440 = lean_box(0);
}
if (lean_is_scalar(x_2440)) {
 x_2441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2441 = x_2440;
}
lean_ctor_set(x_2441, 0, x_2430);
lean_ctor_set(x_2441, 1, x_2439);
x_2442 = lean_array_push(x_2423, x_2441);
x_2443 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2444 = lean_array_push(x_2442, x_2443);
x_2445 = lean_array_push(x_2444, x_2416);
x_2446 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2447, 0, x_2446);
lean_ctor_set(x_2447, 1, x_2445);
x_2448 = lean_array_push(x_2423, x_2447);
x_2449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2449, 0, x_2430);
lean_ctor_set(x_2449, 1, x_2448);
x_2450 = lean_array_push(x_2438, x_2449);
x_2451 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2452, 0, x_2451);
lean_ctor_set(x_2452, 1, x_2450);
if (lean_is_scalar(x_2417)) {
 x_2453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2453 = x_2417;
}
lean_ctor_set(x_2453, 0, x_2415);
lean_ctor_set(x_2453, 1, x_2452);
if (lean_is_scalar(x_2422)) {
 x_2454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2454 = x_2422;
}
lean_ctor_set(x_2454, 0, x_2453);
lean_ctor_set(x_2454, 1, x_2421);
return x_2454;
}
else
{
lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; 
lean_dec(x_2405);
lean_dec(x_11);
lean_dec(x_5);
x_2455 = lean_ctor_get(x_2412, 0);
lean_inc(x_2455);
x_2456 = lean_ctor_get(x_2412, 1);
lean_inc(x_2456);
if (lean_is_exclusive(x_2412)) {
 lean_ctor_release(x_2412, 0);
 lean_ctor_release(x_2412, 1);
 x_2457 = x_2412;
} else {
 lean_dec_ref(x_2412);
 x_2457 = lean_box(0);
}
if (lean_is_scalar(x_2457)) {
 x_2458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2458 = x_2457;
}
lean_ctor_set(x_2458, 0, x_2455);
lean_ctor_set(x_2458, 1, x_2456);
return x_2458;
}
}
else
{
lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; uint8_t x_2462; 
x_2459 = lean_ctor_get(x_2403, 0);
lean_inc(x_2459);
lean_dec(x_2403);
x_2460 = lean_ctor_get(x_2459, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2459, 1);
lean_inc(x_2461);
lean_dec(x_2459);
x_2462 = l_Lean_Syntax_isNone(x_2461);
lean_dec(x_2461);
if (x_2462 == 0)
{
lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; 
lean_dec(x_2460);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2463 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_2464 = l_Lean_Elab_Term_throwError___rarg(x_11, x_2463, x_5, x_6);
lean_dec(x_11);
x_2465 = lean_ctor_get(x_2464, 0);
lean_inc(x_2465);
x_2466 = lean_ctor_get(x_2464, 1);
lean_inc(x_2466);
if (lean_is_exclusive(x_2464)) {
 lean_ctor_release(x_2464, 0);
 lean_ctor_release(x_2464, 1);
 x_2467 = x_2464;
} else {
 lean_dec_ref(x_2464);
 x_2467 = lean_box(0);
}
if (lean_is_scalar(x_2467)) {
 x_2468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2468 = x_2467;
}
lean_ctor_set(x_2468, 0, x_2465);
lean_ctor_set(x_2468, 1, x_2466);
return x_2468;
}
else
{
lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; 
x_2469 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_2470 = lean_unsigned_to_nat(1u);
x_2471 = lean_nat_add(x_3, x_2470);
lean_dec(x_3);
x_2472 = l_Lean_Elab_Term_mkExplicitBinder(x_2460, x_2469);
x_2473 = lean_array_push(x_4, x_2472);
x_3 = x_2471;
x_4 = x_2473;
goto _start;
}
}
}
else
{
lean_object* x_2475; uint8_t x_2476; 
x_2475 = l_Lean_mkAppStx___closed__3;
x_2476 = lean_string_dec_eq(x_2394, x_2475);
if (x_2476 == 0)
{
lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; uint8_t x_2481; lean_object* x_2482; 
if (lean_is_scalar(x_2399)) {
 x_2477 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2477 = x_2399;
}
lean_ctor_set(x_2477, 0, x_16);
lean_ctor_set(x_2477, 1, x_2400);
lean_ctor_set_usize(x_2477, 2, x_2398);
if (lean_is_scalar(x_2396)) {
 x_2478 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2478 = x_2396;
}
lean_ctor_set(x_2478, 0, x_2477);
lean_ctor_set(x_2478, 1, x_2394);
lean_ctor_set_usize(x_2478, 2, x_2395);
x_2479 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2479, 0, x_2478);
lean_ctor_set(x_2479, 1, x_2392);
lean_ctor_set_usize(x_2479, 2, x_2393);
lean_ctor_set(x_12, 0, x_2479);
x_2480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2480, 0, x_12);
lean_ctor_set(x_2480, 1, x_17);
x_2481 = 1;
lean_inc(x_2480);
x_2482 = l_Lean_Syntax_isTermId_x3f(x_2480, x_2481);
if (lean_obj_tag(x_2482) == 0)
{
lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; 
lean_dec(x_2480);
x_2483 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2484 = lean_ctor_get(x_2483, 0);
lean_inc(x_2484);
x_2485 = lean_ctor_get(x_2483, 1);
lean_inc(x_2485);
lean_dec(x_2483);
x_2486 = lean_unsigned_to_nat(1u);
x_2487 = lean_nat_add(x_3, x_2486);
lean_dec(x_3);
x_2488 = l_Lean_mkHole(x_11);
lean_inc(x_2484);
x_2489 = l_Lean_Elab_Term_mkExplicitBinder(x_2484, x_2488);
x_2490 = lean_array_push(x_4, x_2489);
lean_inc(x_5);
x_2491 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2487, x_2490, x_5, x_2485);
if (lean_obj_tag(x_2491) == 0)
{
lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; 
x_2492 = lean_ctor_get(x_2491, 0);
lean_inc(x_2492);
x_2493 = lean_ctor_get(x_2491, 1);
lean_inc(x_2493);
lean_dec(x_2491);
x_2494 = lean_ctor_get(x_2492, 0);
lean_inc(x_2494);
x_2495 = lean_ctor_get(x_2492, 1);
lean_inc(x_2495);
if (lean_is_exclusive(x_2492)) {
 lean_ctor_release(x_2492, 0);
 lean_ctor_release(x_2492, 1);
 x_2496 = x_2492;
} else {
 lean_dec_ref(x_2492);
 x_2496 = lean_box(0);
}
x_2497 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2493);
lean_dec(x_5);
x_2498 = lean_ctor_get(x_2497, 1);
lean_inc(x_2498);
lean_dec(x_2497);
x_2499 = l_Lean_Elab_Term_getMainModule___rarg(x_2498);
x_2500 = lean_ctor_get(x_2499, 1);
lean_inc(x_2500);
if (lean_is_exclusive(x_2499)) {
 lean_ctor_release(x_2499, 0);
 lean_ctor_release(x_2499, 1);
 x_2501 = x_2499;
} else {
 lean_dec_ref(x_2499);
 x_2501 = lean_box(0);
}
x_2502 = l_Array_empty___closed__1;
x_2503 = lean_array_push(x_2502, x_2484);
x_2504 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2505 = lean_array_push(x_2503, x_2504);
x_2506 = l_Lean_mkTermIdFromIdent___closed__2;
x_2507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2507, 0, x_2506);
lean_ctor_set(x_2507, 1, x_2505);
x_2508 = lean_array_push(x_2502, x_2507);
x_2509 = l_Lean_nullKind___closed__2;
x_2510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2510, 0, x_2509);
lean_ctor_set(x_2510, 1, x_2508);
x_2511 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2512 = lean_array_push(x_2511, x_2510);
x_2513 = lean_array_push(x_2512, x_2504);
x_2514 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2515 = lean_array_push(x_2513, x_2514);
x_2516 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2517 = lean_array_push(x_2515, x_2516);
lean_inc(x_11);
x_2518 = lean_array_push(x_2502, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2519 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2519 = lean_box(0);
}
if (lean_is_scalar(x_2519)) {
 x_2520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2520 = x_2519;
}
lean_ctor_set(x_2520, 0, x_2509);
lean_ctor_set(x_2520, 1, x_2518);
x_2521 = lean_array_push(x_2502, x_2520);
x_2522 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2523 = lean_array_push(x_2521, x_2522);
x_2524 = lean_array_push(x_2523, x_2495);
x_2525 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2526, 0, x_2525);
lean_ctor_set(x_2526, 1, x_2524);
x_2527 = lean_array_push(x_2502, x_2526);
x_2528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2528, 0, x_2509);
lean_ctor_set(x_2528, 1, x_2527);
x_2529 = lean_array_push(x_2517, x_2528);
x_2530 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2531, 0, x_2530);
lean_ctor_set(x_2531, 1, x_2529);
if (lean_is_scalar(x_2496)) {
 x_2532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2532 = x_2496;
}
lean_ctor_set(x_2532, 0, x_2494);
lean_ctor_set(x_2532, 1, x_2531);
if (lean_is_scalar(x_2501)) {
 x_2533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2533 = x_2501;
}
lean_ctor_set(x_2533, 0, x_2532);
lean_ctor_set(x_2533, 1, x_2500);
return x_2533;
}
else
{
lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; 
lean_dec(x_2484);
lean_dec(x_11);
lean_dec(x_5);
x_2534 = lean_ctor_get(x_2491, 0);
lean_inc(x_2534);
x_2535 = lean_ctor_get(x_2491, 1);
lean_inc(x_2535);
if (lean_is_exclusive(x_2491)) {
 lean_ctor_release(x_2491, 0);
 lean_ctor_release(x_2491, 1);
 x_2536 = x_2491;
} else {
 lean_dec_ref(x_2491);
 x_2536 = lean_box(0);
}
if (lean_is_scalar(x_2536)) {
 x_2537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2537 = x_2536;
}
lean_ctor_set(x_2537, 0, x_2534);
lean_ctor_set(x_2537, 1, x_2535);
return x_2537;
}
}
else
{
lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; uint8_t x_2541; 
lean_dec(x_11);
x_2538 = lean_ctor_get(x_2482, 0);
lean_inc(x_2538);
lean_dec(x_2482);
x_2539 = lean_ctor_get(x_2538, 0);
lean_inc(x_2539);
x_2540 = lean_ctor_get(x_2538, 1);
lean_inc(x_2540);
lean_dec(x_2538);
x_2541 = l_Lean_Syntax_isNone(x_2540);
lean_dec(x_2540);
if (x_2541 == 0)
{
lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; 
lean_dec(x_2539);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2542 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_2543 = l_Lean_Elab_Term_throwError___rarg(x_2480, x_2542, x_5, x_6);
lean_dec(x_2480);
x_2544 = lean_ctor_get(x_2543, 0);
lean_inc(x_2544);
x_2545 = lean_ctor_get(x_2543, 1);
lean_inc(x_2545);
if (lean_is_exclusive(x_2543)) {
 lean_ctor_release(x_2543, 0);
 lean_ctor_release(x_2543, 1);
 x_2546 = x_2543;
} else {
 lean_dec_ref(x_2543);
 x_2546 = lean_box(0);
}
if (lean_is_scalar(x_2546)) {
 x_2547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2547 = x_2546;
}
lean_ctor_set(x_2547, 0, x_2544);
lean_ctor_set(x_2547, 1, x_2545);
return x_2547;
}
else
{
lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; 
x_2548 = l_Lean_mkHole(x_2480);
lean_dec(x_2480);
x_2549 = lean_unsigned_to_nat(1u);
x_2550 = lean_nat_add(x_3, x_2549);
lean_dec(x_3);
x_2551 = l_Lean_Elab_Term_mkExplicitBinder(x_2539, x_2548);
x_2552 = lean_array_push(x_4, x_2551);
x_3 = x_2550;
x_4 = x_2552;
goto _start;
}
}
}
else
{
lean_object* x_2554; uint8_t x_2555; 
lean_dec(x_2394);
x_2554 = l_Lean_mkAppStx___closed__5;
x_2555 = lean_string_dec_eq(x_2392, x_2554);
if (x_2555 == 0)
{
lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; uint8_t x_2560; lean_object* x_2561; 
if (lean_is_scalar(x_2399)) {
 x_2556 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2556 = x_2399;
}
lean_ctor_set(x_2556, 0, x_16);
lean_ctor_set(x_2556, 1, x_2400);
lean_ctor_set_usize(x_2556, 2, x_2398);
if (lean_is_scalar(x_2396)) {
 x_2557 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2557 = x_2396;
}
lean_ctor_set(x_2557, 0, x_2556);
lean_ctor_set(x_2557, 1, x_2475);
lean_ctor_set_usize(x_2557, 2, x_2395);
x_2558 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2558, 0, x_2557);
lean_ctor_set(x_2558, 1, x_2392);
lean_ctor_set_usize(x_2558, 2, x_2393);
lean_ctor_set(x_12, 0, x_2558);
x_2559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2559, 0, x_12);
lean_ctor_set(x_2559, 1, x_17);
x_2560 = 1;
lean_inc(x_2559);
x_2561 = l_Lean_Syntax_isTermId_x3f(x_2559, x_2560);
if (lean_obj_tag(x_2561) == 0)
{
lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; 
lean_dec(x_2559);
x_2562 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2563 = lean_ctor_get(x_2562, 0);
lean_inc(x_2563);
x_2564 = lean_ctor_get(x_2562, 1);
lean_inc(x_2564);
lean_dec(x_2562);
x_2565 = lean_unsigned_to_nat(1u);
x_2566 = lean_nat_add(x_3, x_2565);
lean_dec(x_3);
x_2567 = l_Lean_mkHole(x_11);
lean_inc(x_2563);
x_2568 = l_Lean_Elab_Term_mkExplicitBinder(x_2563, x_2567);
x_2569 = lean_array_push(x_4, x_2568);
lean_inc(x_5);
x_2570 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2566, x_2569, x_5, x_2564);
if (lean_obj_tag(x_2570) == 0)
{
lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; 
x_2571 = lean_ctor_get(x_2570, 0);
lean_inc(x_2571);
x_2572 = lean_ctor_get(x_2570, 1);
lean_inc(x_2572);
lean_dec(x_2570);
x_2573 = lean_ctor_get(x_2571, 0);
lean_inc(x_2573);
x_2574 = lean_ctor_get(x_2571, 1);
lean_inc(x_2574);
if (lean_is_exclusive(x_2571)) {
 lean_ctor_release(x_2571, 0);
 lean_ctor_release(x_2571, 1);
 x_2575 = x_2571;
} else {
 lean_dec_ref(x_2571);
 x_2575 = lean_box(0);
}
x_2576 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2572);
lean_dec(x_5);
x_2577 = lean_ctor_get(x_2576, 1);
lean_inc(x_2577);
lean_dec(x_2576);
x_2578 = l_Lean_Elab_Term_getMainModule___rarg(x_2577);
x_2579 = lean_ctor_get(x_2578, 1);
lean_inc(x_2579);
if (lean_is_exclusive(x_2578)) {
 lean_ctor_release(x_2578, 0);
 lean_ctor_release(x_2578, 1);
 x_2580 = x_2578;
} else {
 lean_dec_ref(x_2578);
 x_2580 = lean_box(0);
}
x_2581 = l_Array_empty___closed__1;
x_2582 = lean_array_push(x_2581, x_2563);
x_2583 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2584 = lean_array_push(x_2582, x_2583);
x_2585 = l_Lean_mkTermIdFromIdent___closed__2;
x_2586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2586, 0, x_2585);
lean_ctor_set(x_2586, 1, x_2584);
x_2587 = lean_array_push(x_2581, x_2586);
x_2588 = l_Lean_nullKind___closed__2;
x_2589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2589, 0, x_2588);
lean_ctor_set(x_2589, 1, x_2587);
x_2590 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2591 = lean_array_push(x_2590, x_2589);
x_2592 = lean_array_push(x_2591, x_2583);
x_2593 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2594 = lean_array_push(x_2592, x_2593);
x_2595 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2596 = lean_array_push(x_2594, x_2595);
lean_inc(x_11);
x_2597 = lean_array_push(x_2581, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2598 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2598 = lean_box(0);
}
if (lean_is_scalar(x_2598)) {
 x_2599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2599 = x_2598;
}
lean_ctor_set(x_2599, 0, x_2588);
lean_ctor_set(x_2599, 1, x_2597);
x_2600 = lean_array_push(x_2581, x_2599);
x_2601 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2602 = lean_array_push(x_2600, x_2601);
x_2603 = lean_array_push(x_2602, x_2574);
x_2604 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2605, 0, x_2604);
lean_ctor_set(x_2605, 1, x_2603);
x_2606 = lean_array_push(x_2581, x_2605);
x_2607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2607, 0, x_2588);
lean_ctor_set(x_2607, 1, x_2606);
x_2608 = lean_array_push(x_2596, x_2607);
x_2609 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2610, 0, x_2609);
lean_ctor_set(x_2610, 1, x_2608);
if (lean_is_scalar(x_2575)) {
 x_2611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2611 = x_2575;
}
lean_ctor_set(x_2611, 0, x_2573);
lean_ctor_set(x_2611, 1, x_2610);
if (lean_is_scalar(x_2580)) {
 x_2612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2612 = x_2580;
}
lean_ctor_set(x_2612, 0, x_2611);
lean_ctor_set(x_2612, 1, x_2579);
return x_2612;
}
else
{
lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; 
lean_dec(x_2563);
lean_dec(x_11);
lean_dec(x_5);
x_2613 = lean_ctor_get(x_2570, 0);
lean_inc(x_2613);
x_2614 = lean_ctor_get(x_2570, 1);
lean_inc(x_2614);
if (lean_is_exclusive(x_2570)) {
 lean_ctor_release(x_2570, 0);
 lean_ctor_release(x_2570, 1);
 x_2615 = x_2570;
} else {
 lean_dec_ref(x_2570);
 x_2615 = lean_box(0);
}
if (lean_is_scalar(x_2615)) {
 x_2616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2616 = x_2615;
}
lean_ctor_set(x_2616, 0, x_2613);
lean_ctor_set(x_2616, 1, x_2614);
return x_2616;
}
}
else
{
lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; uint8_t x_2620; 
lean_dec(x_11);
x_2617 = lean_ctor_get(x_2561, 0);
lean_inc(x_2617);
lean_dec(x_2561);
x_2618 = lean_ctor_get(x_2617, 0);
lean_inc(x_2618);
x_2619 = lean_ctor_get(x_2617, 1);
lean_inc(x_2619);
lean_dec(x_2617);
x_2620 = l_Lean_Syntax_isNone(x_2619);
lean_dec(x_2619);
if (x_2620 == 0)
{
lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; 
lean_dec(x_2618);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2621 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_2622 = l_Lean_Elab_Term_throwError___rarg(x_2559, x_2621, x_5, x_6);
lean_dec(x_2559);
x_2623 = lean_ctor_get(x_2622, 0);
lean_inc(x_2623);
x_2624 = lean_ctor_get(x_2622, 1);
lean_inc(x_2624);
if (lean_is_exclusive(x_2622)) {
 lean_ctor_release(x_2622, 0);
 lean_ctor_release(x_2622, 1);
 x_2625 = x_2622;
} else {
 lean_dec_ref(x_2622);
 x_2625 = lean_box(0);
}
if (lean_is_scalar(x_2625)) {
 x_2626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2626 = x_2625;
}
lean_ctor_set(x_2626, 0, x_2623);
lean_ctor_set(x_2626, 1, x_2624);
return x_2626;
}
else
{
lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; 
x_2627 = l_Lean_mkHole(x_2559);
lean_dec(x_2559);
x_2628 = lean_unsigned_to_nat(1u);
x_2629 = lean_nat_add(x_3, x_2628);
lean_dec(x_3);
x_2630 = l_Lean_Elab_Term_mkExplicitBinder(x_2618, x_2627);
x_2631 = lean_array_push(x_4, x_2630);
x_3 = x_2629;
x_4 = x_2631;
goto _start;
}
}
}
else
{
lean_object* x_2633; uint8_t x_2634; 
lean_dec(x_2392);
x_2633 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_2634 = lean_string_dec_eq(x_19, x_2633);
if (x_2634 == 0)
{
lean_object* x_2635; uint8_t x_2636; 
x_2635 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_2636 = lean_string_dec_eq(x_19, x_2635);
if (x_2636 == 0)
{
lean_object* x_2637; uint8_t x_2638; 
x_2637 = l_Lean_mkHole___closed__1;
x_2638 = lean_string_dec_eq(x_19, x_2637);
if (x_2638 == 0)
{
lean_object* x_2639; uint8_t x_2640; 
x_2639 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_2640 = lean_string_dec_eq(x_19, x_2639);
if (x_2640 == 0)
{
lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; uint8_t x_2645; lean_object* x_2646; 
if (lean_is_scalar(x_2399)) {
 x_2641 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2641 = x_2399;
}
lean_ctor_set(x_2641, 0, x_16);
lean_ctor_set(x_2641, 1, x_2400);
lean_ctor_set_usize(x_2641, 2, x_2398);
if (lean_is_scalar(x_2396)) {
 x_2642 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2642 = x_2396;
}
lean_ctor_set(x_2642, 0, x_2641);
lean_ctor_set(x_2642, 1, x_2475);
lean_ctor_set_usize(x_2642, 2, x_2395);
x_2643 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2643, 0, x_2642);
lean_ctor_set(x_2643, 1, x_2554);
lean_ctor_set_usize(x_2643, 2, x_2393);
lean_ctor_set(x_12, 0, x_2643);
x_2644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2644, 0, x_12);
lean_ctor_set(x_2644, 1, x_17);
x_2645 = 1;
lean_inc(x_2644);
x_2646 = l_Lean_Syntax_isTermId_x3f(x_2644, x_2645);
if (lean_obj_tag(x_2646) == 0)
{
lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; 
lean_dec(x_2644);
x_2647 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2648 = lean_ctor_get(x_2647, 0);
lean_inc(x_2648);
x_2649 = lean_ctor_get(x_2647, 1);
lean_inc(x_2649);
lean_dec(x_2647);
x_2650 = lean_unsigned_to_nat(1u);
x_2651 = lean_nat_add(x_3, x_2650);
lean_dec(x_3);
x_2652 = l_Lean_mkHole(x_11);
lean_inc(x_2648);
x_2653 = l_Lean_Elab_Term_mkExplicitBinder(x_2648, x_2652);
x_2654 = lean_array_push(x_4, x_2653);
lean_inc(x_5);
x_2655 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2651, x_2654, x_5, x_2649);
if (lean_obj_tag(x_2655) == 0)
{
lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; 
x_2656 = lean_ctor_get(x_2655, 0);
lean_inc(x_2656);
x_2657 = lean_ctor_get(x_2655, 1);
lean_inc(x_2657);
lean_dec(x_2655);
x_2658 = lean_ctor_get(x_2656, 0);
lean_inc(x_2658);
x_2659 = lean_ctor_get(x_2656, 1);
lean_inc(x_2659);
if (lean_is_exclusive(x_2656)) {
 lean_ctor_release(x_2656, 0);
 lean_ctor_release(x_2656, 1);
 x_2660 = x_2656;
} else {
 lean_dec_ref(x_2656);
 x_2660 = lean_box(0);
}
x_2661 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2657);
lean_dec(x_5);
x_2662 = lean_ctor_get(x_2661, 1);
lean_inc(x_2662);
lean_dec(x_2661);
x_2663 = l_Lean_Elab_Term_getMainModule___rarg(x_2662);
x_2664 = lean_ctor_get(x_2663, 1);
lean_inc(x_2664);
if (lean_is_exclusive(x_2663)) {
 lean_ctor_release(x_2663, 0);
 lean_ctor_release(x_2663, 1);
 x_2665 = x_2663;
} else {
 lean_dec_ref(x_2663);
 x_2665 = lean_box(0);
}
x_2666 = l_Array_empty___closed__1;
x_2667 = lean_array_push(x_2666, x_2648);
x_2668 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2669 = lean_array_push(x_2667, x_2668);
x_2670 = l_Lean_mkTermIdFromIdent___closed__2;
x_2671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2671, 0, x_2670);
lean_ctor_set(x_2671, 1, x_2669);
x_2672 = lean_array_push(x_2666, x_2671);
x_2673 = l_Lean_nullKind___closed__2;
x_2674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2674, 0, x_2673);
lean_ctor_set(x_2674, 1, x_2672);
x_2675 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2676 = lean_array_push(x_2675, x_2674);
x_2677 = lean_array_push(x_2676, x_2668);
x_2678 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2679 = lean_array_push(x_2677, x_2678);
x_2680 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2681 = lean_array_push(x_2679, x_2680);
lean_inc(x_11);
x_2682 = lean_array_push(x_2666, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2683 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2683 = lean_box(0);
}
if (lean_is_scalar(x_2683)) {
 x_2684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2684 = x_2683;
}
lean_ctor_set(x_2684, 0, x_2673);
lean_ctor_set(x_2684, 1, x_2682);
x_2685 = lean_array_push(x_2666, x_2684);
x_2686 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2687 = lean_array_push(x_2685, x_2686);
x_2688 = lean_array_push(x_2687, x_2659);
x_2689 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2690, 0, x_2689);
lean_ctor_set(x_2690, 1, x_2688);
x_2691 = lean_array_push(x_2666, x_2690);
x_2692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2692, 0, x_2673);
lean_ctor_set(x_2692, 1, x_2691);
x_2693 = lean_array_push(x_2681, x_2692);
x_2694 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2695, 0, x_2694);
lean_ctor_set(x_2695, 1, x_2693);
if (lean_is_scalar(x_2660)) {
 x_2696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2696 = x_2660;
}
lean_ctor_set(x_2696, 0, x_2658);
lean_ctor_set(x_2696, 1, x_2695);
if (lean_is_scalar(x_2665)) {
 x_2697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2697 = x_2665;
}
lean_ctor_set(x_2697, 0, x_2696);
lean_ctor_set(x_2697, 1, x_2664);
return x_2697;
}
else
{
lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; 
lean_dec(x_2648);
lean_dec(x_11);
lean_dec(x_5);
x_2698 = lean_ctor_get(x_2655, 0);
lean_inc(x_2698);
x_2699 = lean_ctor_get(x_2655, 1);
lean_inc(x_2699);
if (lean_is_exclusive(x_2655)) {
 lean_ctor_release(x_2655, 0);
 lean_ctor_release(x_2655, 1);
 x_2700 = x_2655;
} else {
 lean_dec_ref(x_2655);
 x_2700 = lean_box(0);
}
if (lean_is_scalar(x_2700)) {
 x_2701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2701 = x_2700;
}
lean_ctor_set(x_2701, 0, x_2698);
lean_ctor_set(x_2701, 1, x_2699);
return x_2701;
}
}
else
{
lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; uint8_t x_2705; 
lean_dec(x_11);
x_2702 = lean_ctor_get(x_2646, 0);
lean_inc(x_2702);
lean_dec(x_2646);
x_2703 = lean_ctor_get(x_2702, 0);
lean_inc(x_2703);
x_2704 = lean_ctor_get(x_2702, 1);
lean_inc(x_2704);
lean_dec(x_2702);
x_2705 = l_Lean_Syntax_isNone(x_2704);
lean_dec(x_2704);
if (x_2705 == 0)
{
lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; 
lean_dec(x_2703);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2706 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_2707 = l_Lean_Elab_Term_throwError___rarg(x_2644, x_2706, x_5, x_6);
lean_dec(x_2644);
x_2708 = lean_ctor_get(x_2707, 0);
lean_inc(x_2708);
x_2709 = lean_ctor_get(x_2707, 1);
lean_inc(x_2709);
if (lean_is_exclusive(x_2707)) {
 lean_ctor_release(x_2707, 0);
 lean_ctor_release(x_2707, 1);
 x_2710 = x_2707;
} else {
 lean_dec_ref(x_2707);
 x_2710 = lean_box(0);
}
if (lean_is_scalar(x_2710)) {
 x_2711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2711 = x_2710;
}
lean_ctor_set(x_2711, 0, x_2708);
lean_ctor_set(x_2711, 1, x_2709);
return x_2711;
}
else
{
lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; 
x_2712 = l_Lean_mkHole(x_2644);
lean_dec(x_2644);
x_2713 = lean_unsigned_to_nat(1u);
x_2714 = lean_nat_add(x_3, x_2713);
lean_dec(x_3);
x_2715 = l_Lean_Elab_Term_mkExplicitBinder(x_2703, x_2712);
x_2716 = lean_array_push(x_4, x_2715);
x_3 = x_2714;
x_4 = x_2716;
goto _start;
}
}
}
else
{
lean_object* x_2718; lean_object* x_2719; uint8_t x_2720; 
lean_dec(x_2399);
lean_dec(x_2396);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2718 = lean_unsigned_to_nat(1u);
x_2719 = l_Lean_Syntax_getArg(x_11, x_2718);
x_2720 = l_Lean_Syntax_isNone(x_2719);
if (x_2720 == 0)
{
lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; uint8_t x_2724; 
x_2721 = lean_unsigned_to_nat(0u);
x_2722 = l_Lean_Syntax_getArg(x_2719, x_2721);
x_2723 = l_Lean_Syntax_getArg(x_2719, x_2718);
lean_dec(x_2719);
x_2724 = l_Lean_Syntax_isNone(x_2723);
if (x_2724 == 0)
{
lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; uint8_t x_2732; 
x_2725 = l_Lean_Syntax_getArg(x_2723, x_2721);
lean_dec(x_2723);
lean_inc(x_2725);
x_2726 = l_Lean_Syntax_getKind(x_2725);
x_2727 = lean_name_mk_string(x_16, x_2400);
x_2728 = lean_name_mk_string(x_2727, x_2475);
x_2729 = lean_name_mk_string(x_2728, x_2554);
x_2730 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_2731 = lean_name_mk_string(x_2729, x_2730);
x_2732 = lean_name_eq(x_2726, x_2731);
lean_dec(x_2731);
lean_dec(x_2726);
if (x_2732 == 0)
{
lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; 
lean_dec(x_2725);
lean_dec(x_2722);
x_2733 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2734 = lean_ctor_get(x_2733, 0);
lean_inc(x_2734);
x_2735 = lean_ctor_get(x_2733, 1);
lean_inc(x_2735);
lean_dec(x_2733);
x_2736 = lean_nat_add(x_3, x_2718);
lean_dec(x_3);
x_2737 = l_Lean_mkHole(x_11);
lean_inc(x_2734);
x_2738 = l_Lean_Elab_Term_mkExplicitBinder(x_2734, x_2737);
x_2739 = lean_array_push(x_4, x_2738);
lean_inc(x_5);
x_2740 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2736, x_2739, x_5, x_2735);
if (lean_obj_tag(x_2740) == 0)
{
lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; 
x_2741 = lean_ctor_get(x_2740, 0);
lean_inc(x_2741);
x_2742 = lean_ctor_get(x_2740, 1);
lean_inc(x_2742);
lean_dec(x_2740);
x_2743 = lean_ctor_get(x_2741, 0);
lean_inc(x_2743);
x_2744 = lean_ctor_get(x_2741, 1);
lean_inc(x_2744);
if (lean_is_exclusive(x_2741)) {
 lean_ctor_release(x_2741, 0);
 lean_ctor_release(x_2741, 1);
 x_2745 = x_2741;
} else {
 lean_dec_ref(x_2741);
 x_2745 = lean_box(0);
}
x_2746 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2742);
lean_dec(x_5);
x_2747 = lean_ctor_get(x_2746, 1);
lean_inc(x_2747);
lean_dec(x_2746);
x_2748 = l_Lean_Elab_Term_getMainModule___rarg(x_2747);
x_2749 = lean_ctor_get(x_2748, 1);
lean_inc(x_2749);
if (lean_is_exclusive(x_2748)) {
 lean_ctor_release(x_2748, 0);
 lean_ctor_release(x_2748, 1);
 x_2750 = x_2748;
} else {
 lean_dec_ref(x_2748);
 x_2750 = lean_box(0);
}
x_2751 = l_Array_empty___closed__1;
x_2752 = lean_array_push(x_2751, x_2734);
x_2753 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2754 = lean_array_push(x_2752, x_2753);
x_2755 = l_Lean_mkTermIdFromIdent___closed__2;
x_2756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2756, 0, x_2755);
lean_ctor_set(x_2756, 1, x_2754);
x_2757 = lean_array_push(x_2751, x_2756);
x_2758 = l_Lean_nullKind___closed__2;
x_2759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2759, 0, x_2758);
lean_ctor_set(x_2759, 1, x_2757);
x_2760 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2761 = lean_array_push(x_2760, x_2759);
x_2762 = lean_array_push(x_2761, x_2753);
x_2763 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2764 = lean_array_push(x_2762, x_2763);
x_2765 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2766 = lean_array_push(x_2764, x_2765);
lean_inc(x_11);
x_2767 = lean_array_push(x_2751, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2768 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2768 = lean_box(0);
}
if (lean_is_scalar(x_2768)) {
 x_2769 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2769 = x_2768;
}
lean_ctor_set(x_2769, 0, x_2758);
lean_ctor_set(x_2769, 1, x_2767);
x_2770 = lean_array_push(x_2751, x_2769);
x_2771 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2772 = lean_array_push(x_2770, x_2771);
x_2773 = lean_array_push(x_2772, x_2744);
x_2774 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2775, 0, x_2774);
lean_ctor_set(x_2775, 1, x_2773);
x_2776 = lean_array_push(x_2751, x_2775);
x_2777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2777, 0, x_2758);
lean_ctor_set(x_2777, 1, x_2776);
x_2778 = lean_array_push(x_2766, x_2777);
x_2779 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2780, 0, x_2779);
lean_ctor_set(x_2780, 1, x_2778);
if (lean_is_scalar(x_2745)) {
 x_2781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2781 = x_2745;
}
lean_ctor_set(x_2781, 0, x_2743);
lean_ctor_set(x_2781, 1, x_2780);
if (lean_is_scalar(x_2750)) {
 x_2782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2782 = x_2750;
}
lean_ctor_set(x_2782, 0, x_2781);
lean_ctor_set(x_2782, 1, x_2749);
return x_2782;
}
else
{
lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; 
lean_dec(x_2734);
lean_dec(x_11);
lean_dec(x_5);
x_2783 = lean_ctor_get(x_2740, 0);
lean_inc(x_2783);
x_2784 = lean_ctor_get(x_2740, 1);
lean_inc(x_2784);
if (lean_is_exclusive(x_2740)) {
 lean_ctor_release(x_2740, 0);
 lean_ctor_release(x_2740, 1);
 x_2785 = x_2740;
} else {
 lean_dec_ref(x_2740);
 x_2785 = lean_box(0);
}
if (lean_is_scalar(x_2785)) {
 x_2786 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2786 = x_2785;
}
lean_ctor_set(x_2786, 0, x_2783);
lean_ctor_set(x_2786, 1, x_2784);
return x_2786;
}
}
else
{
lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; 
x_2787 = l_Lean_Syntax_getArg(x_2725, x_2718);
lean_dec(x_2725);
x_2788 = l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(x_2722, x_5, x_6);
x_2789 = lean_ctor_get(x_2788, 0);
lean_inc(x_2789);
if (lean_obj_tag(x_2789) == 0)
{
lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; 
lean_dec(x_2787);
x_2790 = lean_ctor_get(x_2788, 1);
lean_inc(x_2790);
lean_dec(x_2788);
x_2791 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_2790);
x_2792 = lean_ctor_get(x_2791, 0);
lean_inc(x_2792);
x_2793 = lean_ctor_get(x_2791, 1);
lean_inc(x_2793);
lean_dec(x_2791);
x_2794 = lean_nat_add(x_3, x_2718);
lean_dec(x_3);
x_2795 = l_Lean_mkHole(x_11);
lean_inc(x_2792);
x_2796 = l_Lean_Elab_Term_mkExplicitBinder(x_2792, x_2795);
x_2797 = lean_array_push(x_4, x_2796);
lean_inc(x_5);
x_2798 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2794, x_2797, x_5, x_2793);
if (lean_obj_tag(x_2798) == 0)
{
lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; lean_object* x_2802; lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; 
x_2799 = lean_ctor_get(x_2798, 0);
lean_inc(x_2799);
x_2800 = lean_ctor_get(x_2798, 1);
lean_inc(x_2800);
lean_dec(x_2798);
x_2801 = lean_ctor_get(x_2799, 0);
lean_inc(x_2801);
x_2802 = lean_ctor_get(x_2799, 1);
lean_inc(x_2802);
if (lean_is_exclusive(x_2799)) {
 lean_ctor_release(x_2799, 0);
 lean_ctor_release(x_2799, 1);
 x_2803 = x_2799;
} else {
 lean_dec_ref(x_2799);
 x_2803 = lean_box(0);
}
x_2804 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2800);
lean_dec(x_5);
x_2805 = lean_ctor_get(x_2804, 1);
lean_inc(x_2805);
lean_dec(x_2804);
x_2806 = l_Lean_Elab_Term_getMainModule___rarg(x_2805);
x_2807 = lean_ctor_get(x_2806, 1);
lean_inc(x_2807);
if (lean_is_exclusive(x_2806)) {
 lean_ctor_release(x_2806, 0);
 lean_ctor_release(x_2806, 1);
 x_2808 = x_2806;
} else {
 lean_dec_ref(x_2806);
 x_2808 = lean_box(0);
}
x_2809 = l_Array_empty___closed__1;
x_2810 = lean_array_push(x_2809, x_2792);
x_2811 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2812 = lean_array_push(x_2810, x_2811);
x_2813 = l_Lean_mkTermIdFromIdent___closed__2;
x_2814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2814, 0, x_2813);
lean_ctor_set(x_2814, 1, x_2812);
x_2815 = lean_array_push(x_2809, x_2814);
x_2816 = l_Lean_nullKind___closed__2;
x_2817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2817, 0, x_2816);
lean_ctor_set(x_2817, 1, x_2815);
x_2818 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2819 = lean_array_push(x_2818, x_2817);
x_2820 = lean_array_push(x_2819, x_2811);
x_2821 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2822 = lean_array_push(x_2820, x_2821);
x_2823 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2824 = lean_array_push(x_2822, x_2823);
lean_inc(x_11);
x_2825 = lean_array_push(x_2809, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2826 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2826 = lean_box(0);
}
if (lean_is_scalar(x_2826)) {
 x_2827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2827 = x_2826;
}
lean_ctor_set(x_2827, 0, x_2816);
lean_ctor_set(x_2827, 1, x_2825);
x_2828 = lean_array_push(x_2809, x_2827);
x_2829 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2830 = lean_array_push(x_2828, x_2829);
x_2831 = lean_array_push(x_2830, x_2802);
x_2832 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2833, 0, x_2832);
lean_ctor_set(x_2833, 1, x_2831);
x_2834 = lean_array_push(x_2809, x_2833);
x_2835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2835, 0, x_2816);
lean_ctor_set(x_2835, 1, x_2834);
x_2836 = lean_array_push(x_2824, x_2835);
x_2837 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2838, 0, x_2837);
lean_ctor_set(x_2838, 1, x_2836);
if (lean_is_scalar(x_2803)) {
 x_2839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2839 = x_2803;
}
lean_ctor_set(x_2839, 0, x_2801);
lean_ctor_set(x_2839, 1, x_2838);
if (lean_is_scalar(x_2808)) {
 x_2840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2840 = x_2808;
}
lean_ctor_set(x_2840, 0, x_2839);
lean_ctor_set(x_2840, 1, x_2807);
return x_2840;
}
else
{
lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; 
lean_dec(x_2792);
lean_dec(x_11);
lean_dec(x_5);
x_2841 = lean_ctor_get(x_2798, 0);
lean_inc(x_2841);
x_2842 = lean_ctor_get(x_2798, 1);
lean_inc(x_2842);
if (lean_is_exclusive(x_2798)) {
 lean_ctor_release(x_2798, 0);
 lean_ctor_release(x_2798, 1);
 x_2843 = x_2798;
} else {
 lean_dec_ref(x_2798);
 x_2843 = lean_box(0);
}
if (lean_is_scalar(x_2843)) {
 x_2844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2844 = x_2843;
}
lean_ctor_set(x_2844, 0, x_2841);
lean_ctor_set(x_2844, 1, x_2842);
return x_2844;
}
}
else
{
lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; 
lean_dec(x_11);
x_2845 = lean_ctor_get(x_2788, 1);
lean_inc(x_2845);
lean_dec(x_2788);
x_2846 = lean_ctor_get(x_2789, 0);
lean_inc(x_2846);
lean_dec(x_2789);
x_2847 = lean_nat_add(x_3, x_2718);
lean_dec(x_3);
x_2848 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(x_2787, x_2721, x_2846);
x_2849 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2848, x_2848, x_2721, x_4);
lean_dec(x_2848);
x_3 = x_2847;
x_4 = x_2849;
x_6 = x_2845;
goto _start;
}
}
}
else
{
lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; 
lean_dec(x_2723);
lean_dec(x_2722);
x_2851 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2852 = lean_ctor_get(x_2851, 0);
lean_inc(x_2852);
x_2853 = lean_ctor_get(x_2851, 1);
lean_inc(x_2853);
lean_dec(x_2851);
x_2854 = lean_nat_add(x_3, x_2718);
lean_dec(x_3);
x_2855 = l_Lean_mkHole(x_11);
lean_inc(x_2852);
x_2856 = l_Lean_Elab_Term_mkExplicitBinder(x_2852, x_2855);
x_2857 = lean_array_push(x_4, x_2856);
lean_inc(x_5);
x_2858 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2854, x_2857, x_5, x_2853);
if (lean_obj_tag(x_2858) == 0)
{
lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; 
x_2859 = lean_ctor_get(x_2858, 0);
lean_inc(x_2859);
x_2860 = lean_ctor_get(x_2858, 1);
lean_inc(x_2860);
lean_dec(x_2858);
x_2861 = lean_ctor_get(x_2859, 0);
lean_inc(x_2861);
x_2862 = lean_ctor_get(x_2859, 1);
lean_inc(x_2862);
if (lean_is_exclusive(x_2859)) {
 lean_ctor_release(x_2859, 0);
 lean_ctor_release(x_2859, 1);
 x_2863 = x_2859;
} else {
 lean_dec_ref(x_2859);
 x_2863 = lean_box(0);
}
x_2864 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2860);
lean_dec(x_5);
x_2865 = lean_ctor_get(x_2864, 1);
lean_inc(x_2865);
lean_dec(x_2864);
x_2866 = l_Lean_Elab_Term_getMainModule___rarg(x_2865);
x_2867 = lean_ctor_get(x_2866, 1);
lean_inc(x_2867);
if (lean_is_exclusive(x_2866)) {
 lean_ctor_release(x_2866, 0);
 lean_ctor_release(x_2866, 1);
 x_2868 = x_2866;
} else {
 lean_dec_ref(x_2866);
 x_2868 = lean_box(0);
}
x_2869 = l_Array_empty___closed__1;
x_2870 = lean_array_push(x_2869, x_2852);
x_2871 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2872 = lean_array_push(x_2870, x_2871);
x_2873 = l_Lean_mkTermIdFromIdent___closed__2;
x_2874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2874, 0, x_2873);
lean_ctor_set(x_2874, 1, x_2872);
x_2875 = lean_array_push(x_2869, x_2874);
x_2876 = l_Lean_nullKind___closed__2;
x_2877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2877, 0, x_2876);
lean_ctor_set(x_2877, 1, x_2875);
x_2878 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2879 = lean_array_push(x_2878, x_2877);
x_2880 = lean_array_push(x_2879, x_2871);
x_2881 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2882 = lean_array_push(x_2880, x_2881);
x_2883 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2884 = lean_array_push(x_2882, x_2883);
lean_inc(x_11);
x_2885 = lean_array_push(x_2869, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2886 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2886 = lean_box(0);
}
if (lean_is_scalar(x_2886)) {
 x_2887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2887 = x_2886;
}
lean_ctor_set(x_2887, 0, x_2876);
lean_ctor_set(x_2887, 1, x_2885);
x_2888 = lean_array_push(x_2869, x_2887);
x_2889 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2890 = lean_array_push(x_2888, x_2889);
x_2891 = lean_array_push(x_2890, x_2862);
x_2892 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2893, 0, x_2892);
lean_ctor_set(x_2893, 1, x_2891);
x_2894 = lean_array_push(x_2869, x_2893);
x_2895 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2895, 0, x_2876);
lean_ctor_set(x_2895, 1, x_2894);
x_2896 = lean_array_push(x_2884, x_2895);
x_2897 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2898, 0, x_2897);
lean_ctor_set(x_2898, 1, x_2896);
if (lean_is_scalar(x_2863)) {
 x_2899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2899 = x_2863;
}
lean_ctor_set(x_2899, 0, x_2861);
lean_ctor_set(x_2899, 1, x_2898);
if (lean_is_scalar(x_2868)) {
 x_2900 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2900 = x_2868;
}
lean_ctor_set(x_2900, 0, x_2899);
lean_ctor_set(x_2900, 1, x_2867);
return x_2900;
}
else
{
lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; 
lean_dec(x_2852);
lean_dec(x_11);
lean_dec(x_5);
x_2901 = lean_ctor_get(x_2858, 0);
lean_inc(x_2901);
x_2902 = lean_ctor_get(x_2858, 1);
lean_inc(x_2902);
if (lean_is_exclusive(x_2858)) {
 lean_ctor_release(x_2858, 0);
 lean_ctor_release(x_2858, 1);
 x_2903 = x_2858;
} else {
 lean_dec_ref(x_2858);
 x_2903 = lean_box(0);
}
if (lean_is_scalar(x_2903)) {
 x_2904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2904 = x_2903;
}
lean_ctor_set(x_2904, 0, x_2901);
lean_ctor_set(x_2904, 1, x_2902);
return x_2904;
}
}
}
else
{
lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; 
lean_dec(x_2719);
x_2905 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2906 = lean_ctor_get(x_2905, 0);
lean_inc(x_2906);
x_2907 = lean_ctor_get(x_2905, 1);
lean_inc(x_2907);
lean_dec(x_2905);
x_2908 = lean_nat_add(x_3, x_2718);
lean_dec(x_3);
x_2909 = l_Lean_mkHole(x_11);
lean_inc(x_2906);
x_2910 = l_Lean_Elab_Term_mkExplicitBinder(x_2906, x_2909);
x_2911 = lean_array_push(x_4, x_2910);
lean_inc(x_5);
x_2912 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2908, x_2911, x_5, x_2907);
if (lean_obj_tag(x_2912) == 0)
{
lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; lean_object* x_2954; 
x_2913 = lean_ctor_get(x_2912, 0);
lean_inc(x_2913);
x_2914 = lean_ctor_get(x_2912, 1);
lean_inc(x_2914);
lean_dec(x_2912);
x_2915 = lean_ctor_get(x_2913, 0);
lean_inc(x_2915);
x_2916 = lean_ctor_get(x_2913, 1);
lean_inc(x_2916);
if (lean_is_exclusive(x_2913)) {
 lean_ctor_release(x_2913, 0);
 lean_ctor_release(x_2913, 1);
 x_2917 = x_2913;
} else {
 lean_dec_ref(x_2913);
 x_2917 = lean_box(0);
}
x_2918 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2914);
lean_dec(x_5);
x_2919 = lean_ctor_get(x_2918, 1);
lean_inc(x_2919);
lean_dec(x_2918);
x_2920 = l_Lean_Elab_Term_getMainModule___rarg(x_2919);
x_2921 = lean_ctor_get(x_2920, 1);
lean_inc(x_2921);
if (lean_is_exclusive(x_2920)) {
 lean_ctor_release(x_2920, 0);
 lean_ctor_release(x_2920, 1);
 x_2922 = x_2920;
} else {
 lean_dec_ref(x_2920);
 x_2922 = lean_box(0);
}
x_2923 = l_Array_empty___closed__1;
x_2924 = lean_array_push(x_2923, x_2906);
x_2925 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_2926 = lean_array_push(x_2924, x_2925);
x_2927 = l_Lean_mkTermIdFromIdent___closed__2;
x_2928 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2928, 0, x_2927);
lean_ctor_set(x_2928, 1, x_2926);
x_2929 = lean_array_push(x_2923, x_2928);
x_2930 = l_Lean_nullKind___closed__2;
x_2931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2931, 0, x_2930);
lean_ctor_set(x_2931, 1, x_2929);
x_2932 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_2933 = lean_array_push(x_2932, x_2931);
x_2934 = lean_array_push(x_2933, x_2925);
x_2935 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_2936 = lean_array_push(x_2934, x_2935);
x_2937 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_2938 = lean_array_push(x_2936, x_2937);
lean_inc(x_11);
x_2939 = lean_array_push(x_2923, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2940 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2940 = lean_box(0);
}
if (lean_is_scalar(x_2940)) {
 x_2941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2941 = x_2940;
}
lean_ctor_set(x_2941, 0, x_2930);
lean_ctor_set(x_2941, 1, x_2939);
x_2942 = lean_array_push(x_2923, x_2941);
x_2943 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_2944 = lean_array_push(x_2942, x_2943);
x_2945 = lean_array_push(x_2944, x_2916);
x_2946 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2947 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2947, 0, x_2946);
lean_ctor_set(x_2947, 1, x_2945);
x_2948 = lean_array_push(x_2923, x_2947);
x_2949 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2949, 0, x_2930);
lean_ctor_set(x_2949, 1, x_2948);
x_2950 = lean_array_push(x_2938, x_2949);
x_2951 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2952 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2952, 0, x_2951);
lean_ctor_set(x_2952, 1, x_2950);
if (lean_is_scalar(x_2917)) {
 x_2953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2953 = x_2917;
}
lean_ctor_set(x_2953, 0, x_2915);
lean_ctor_set(x_2953, 1, x_2952);
if (lean_is_scalar(x_2922)) {
 x_2954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2954 = x_2922;
}
lean_ctor_set(x_2954, 0, x_2953);
lean_ctor_set(x_2954, 1, x_2921);
return x_2954;
}
else
{
lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; 
lean_dec(x_2906);
lean_dec(x_11);
lean_dec(x_5);
x_2955 = lean_ctor_get(x_2912, 0);
lean_inc(x_2955);
x_2956 = lean_ctor_get(x_2912, 1);
lean_inc(x_2956);
if (lean_is_exclusive(x_2912)) {
 lean_ctor_release(x_2912, 0);
 lean_ctor_release(x_2912, 1);
 x_2957 = x_2912;
} else {
 lean_dec_ref(x_2912);
 x_2957 = lean_box(0);
}
if (lean_is_scalar(x_2957)) {
 x_2958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2958 = x_2957;
}
lean_ctor_set(x_2958, 0, x_2955);
lean_ctor_set(x_2958, 1, x_2956);
return x_2958;
}
}
}
}
else
{
lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; 
lean_dec(x_2399);
lean_dec(x_2396);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2959 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2960 = lean_ctor_get(x_2959, 0);
lean_inc(x_2960);
x_2961 = lean_ctor_get(x_2959, 1);
lean_inc(x_2961);
lean_dec(x_2959);
x_2962 = lean_unsigned_to_nat(1u);
x_2963 = lean_nat_add(x_3, x_2962);
lean_dec(x_3);
x_2964 = l_Lean_Elab_Term_mkExplicitBinder(x_2960, x_11);
x_2965 = lean_array_push(x_4, x_2964);
x_3 = x_2963;
x_4 = x_2965;
x_6 = x_2961;
goto _start;
}
}
else
{
lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; 
lean_dec(x_2399);
lean_dec(x_2396);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2967 = lean_unsigned_to_nat(1u);
x_2968 = lean_nat_add(x_3, x_2967);
lean_dec(x_3);
x_2969 = lean_array_push(x_4, x_11);
x_3 = x_2968;
x_4 = x_2969;
goto _start;
}
}
else
{
lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; 
lean_dec(x_2399);
lean_dec(x_2396);
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
x_2971 = lean_unsigned_to_nat(1u);
x_2972 = lean_nat_add(x_3, x_2971);
lean_dec(x_3);
x_2973 = lean_array_push(x_4, x_11);
x_3 = x_2972;
x_4 = x_2973;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_2975; size_t x_2976; lean_object* x_2977; size_t x_2978; lean_object* x_2979; lean_object* x_2980; size_t x_2981; lean_object* x_2982; lean_object* x_2983; size_t x_2984; lean_object* x_2985; lean_object* x_2986; uint8_t x_2987; 
x_2975 = lean_ctor_get(x_12, 1);
x_2976 = lean_ctor_get_usize(x_12, 2);
lean_inc(x_2975);
lean_dec(x_12);
x_2977 = lean_ctor_get(x_13, 1);
lean_inc(x_2977);
x_2978 = lean_ctor_get_usize(x_13, 2);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_2979 = x_13;
} else {
 lean_dec_ref(x_13);
 x_2979 = lean_box(0);
}
x_2980 = lean_ctor_get(x_14, 1);
lean_inc(x_2980);
x_2981 = lean_ctor_get_usize(x_14, 2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2982 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2982 = lean_box(0);
}
x_2983 = lean_ctor_get(x_15, 1);
lean_inc(x_2983);
x_2984 = lean_ctor_get_usize(x_15, 2);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_2985 = x_15;
} else {
 lean_dec_ref(x_15);
 x_2985 = lean_box(0);
}
x_2986 = l_Lean_mkAppStx___closed__1;
x_2987 = lean_string_dec_eq(x_2983, x_2986);
lean_dec(x_2983);
if (x_2987 == 0)
{
uint8_t x_2988; lean_object* x_2989; 
lean_dec(x_2985);
lean_dec(x_2982);
lean_dec(x_2980);
lean_dec(x_2979);
lean_dec(x_2977);
lean_dec(x_2975);
lean_dec(x_17);
x_2988 = 1;
lean_inc(x_11);
x_2989 = l_Lean_Syntax_isTermId_x3f(x_11, x_2988);
if (lean_obj_tag(x_2989) == 0)
{
lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; 
x_2990 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_2991 = lean_ctor_get(x_2990, 0);
lean_inc(x_2991);
x_2992 = lean_ctor_get(x_2990, 1);
lean_inc(x_2992);
lean_dec(x_2990);
x_2993 = lean_unsigned_to_nat(1u);
x_2994 = lean_nat_add(x_3, x_2993);
lean_dec(x_3);
x_2995 = l_Lean_mkHole(x_11);
lean_inc(x_2991);
x_2996 = l_Lean_Elab_Term_mkExplicitBinder(x_2991, x_2995);
x_2997 = lean_array_push(x_4, x_2996);
lean_inc(x_5);
x_2998 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_2994, x_2997, x_5, x_2992);
if (lean_obj_tag(x_2998) == 0)
{
lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; 
x_2999 = lean_ctor_get(x_2998, 0);
lean_inc(x_2999);
x_3000 = lean_ctor_get(x_2998, 1);
lean_inc(x_3000);
lean_dec(x_2998);
x_3001 = lean_ctor_get(x_2999, 0);
lean_inc(x_3001);
x_3002 = lean_ctor_get(x_2999, 1);
lean_inc(x_3002);
if (lean_is_exclusive(x_2999)) {
 lean_ctor_release(x_2999, 0);
 lean_ctor_release(x_2999, 1);
 x_3003 = x_2999;
} else {
 lean_dec_ref(x_2999);
 x_3003 = lean_box(0);
}
x_3004 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3000);
lean_dec(x_5);
x_3005 = lean_ctor_get(x_3004, 1);
lean_inc(x_3005);
lean_dec(x_3004);
x_3006 = l_Lean_Elab_Term_getMainModule___rarg(x_3005);
x_3007 = lean_ctor_get(x_3006, 1);
lean_inc(x_3007);
if (lean_is_exclusive(x_3006)) {
 lean_ctor_release(x_3006, 0);
 lean_ctor_release(x_3006, 1);
 x_3008 = x_3006;
} else {
 lean_dec_ref(x_3006);
 x_3008 = lean_box(0);
}
x_3009 = l_Array_empty___closed__1;
x_3010 = lean_array_push(x_3009, x_2991);
x_3011 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3012 = lean_array_push(x_3010, x_3011);
x_3013 = l_Lean_mkTermIdFromIdent___closed__2;
x_3014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3014, 0, x_3013);
lean_ctor_set(x_3014, 1, x_3012);
x_3015 = lean_array_push(x_3009, x_3014);
x_3016 = l_Lean_nullKind___closed__2;
x_3017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3017, 0, x_3016);
lean_ctor_set(x_3017, 1, x_3015);
x_3018 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3019 = lean_array_push(x_3018, x_3017);
x_3020 = lean_array_push(x_3019, x_3011);
x_3021 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3022 = lean_array_push(x_3020, x_3021);
x_3023 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3024 = lean_array_push(x_3022, x_3023);
lean_inc(x_11);
x_3025 = lean_array_push(x_3009, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3026 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3026 = lean_box(0);
}
if (lean_is_scalar(x_3026)) {
 x_3027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3027 = x_3026;
}
lean_ctor_set(x_3027, 0, x_3016);
lean_ctor_set(x_3027, 1, x_3025);
x_3028 = lean_array_push(x_3009, x_3027);
x_3029 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3030 = lean_array_push(x_3028, x_3029);
x_3031 = lean_array_push(x_3030, x_3002);
x_3032 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3033 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3033, 0, x_3032);
lean_ctor_set(x_3033, 1, x_3031);
x_3034 = lean_array_push(x_3009, x_3033);
x_3035 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3035, 0, x_3016);
lean_ctor_set(x_3035, 1, x_3034);
x_3036 = lean_array_push(x_3024, x_3035);
x_3037 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3038, 0, x_3037);
lean_ctor_set(x_3038, 1, x_3036);
if (lean_is_scalar(x_3003)) {
 x_3039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3039 = x_3003;
}
lean_ctor_set(x_3039, 0, x_3001);
lean_ctor_set(x_3039, 1, x_3038);
if (lean_is_scalar(x_3008)) {
 x_3040 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3040 = x_3008;
}
lean_ctor_set(x_3040, 0, x_3039);
lean_ctor_set(x_3040, 1, x_3007);
return x_3040;
}
else
{
lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; 
lean_dec(x_2991);
lean_dec(x_11);
lean_dec(x_5);
x_3041 = lean_ctor_get(x_2998, 0);
lean_inc(x_3041);
x_3042 = lean_ctor_get(x_2998, 1);
lean_inc(x_3042);
if (lean_is_exclusive(x_2998)) {
 lean_ctor_release(x_2998, 0);
 lean_ctor_release(x_2998, 1);
 x_3043 = x_2998;
} else {
 lean_dec_ref(x_2998);
 x_3043 = lean_box(0);
}
if (lean_is_scalar(x_3043)) {
 x_3044 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3044 = x_3043;
}
lean_ctor_set(x_3044, 0, x_3041);
lean_ctor_set(x_3044, 1, x_3042);
return x_3044;
}
}
else
{
lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; uint8_t x_3048; 
x_3045 = lean_ctor_get(x_2989, 0);
lean_inc(x_3045);
lean_dec(x_2989);
x_3046 = lean_ctor_get(x_3045, 0);
lean_inc(x_3046);
x_3047 = lean_ctor_get(x_3045, 1);
lean_inc(x_3047);
lean_dec(x_3045);
x_3048 = l_Lean_Syntax_isNone(x_3047);
lean_dec(x_3047);
if (x_3048 == 0)
{
lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; 
lean_dec(x_3046);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3049 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_3050 = l_Lean_Elab_Term_throwError___rarg(x_11, x_3049, x_5, x_6);
lean_dec(x_11);
x_3051 = lean_ctor_get(x_3050, 0);
lean_inc(x_3051);
x_3052 = lean_ctor_get(x_3050, 1);
lean_inc(x_3052);
if (lean_is_exclusive(x_3050)) {
 lean_ctor_release(x_3050, 0);
 lean_ctor_release(x_3050, 1);
 x_3053 = x_3050;
} else {
 lean_dec_ref(x_3050);
 x_3053 = lean_box(0);
}
if (lean_is_scalar(x_3053)) {
 x_3054 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3054 = x_3053;
}
lean_ctor_set(x_3054, 0, x_3051);
lean_ctor_set(x_3054, 1, x_3052);
return x_3054;
}
else
{
lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; 
x_3055 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_3056 = lean_unsigned_to_nat(1u);
x_3057 = lean_nat_add(x_3, x_3056);
lean_dec(x_3);
x_3058 = l_Lean_Elab_Term_mkExplicitBinder(x_3046, x_3055);
x_3059 = lean_array_push(x_4, x_3058);
x_3 = x_3057;
x_4 = x_3059;
goto _start;
}
}
}
else
{
lean_object* x_3061; uint8_t x_3062; 
x_3061 = l_Lean_mkAppStx___closed__3;
x_3062 = lean_string_dec_eq(x_2980, x_3061);
if (x_3062 == 0)
{
lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; lean_object* x_3067; uint8_t x_3068; lean_object* x_3069; 
if (lean_is_scalar(x_2985)) {
 x_3063 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3063 = x_2985;
}
lean_ctor_set(x_3063, 0, x_16);
lean_ctor_set(x_3063, 1, x_2986);
lean_ctor_set_usize(x_3063, 2, x_2984);
if (lean_is_scalar(x_2982)) {
 x_3064 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3064 = x_2982;
}
lean_ctor_set(x_3064, 0, x_3063);
lean_ctor_set(x_3064, 1, x_2980);
lean_ctor_set_usize(x_3064, 2, x_2981);
if (lean_is_scalar(x_2979)) {
 x_3065 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3065 = x_2979;
}
lean_ctor_set(x_3065, 0, x_3064);
lean_ctor_set(x_3065, 1, x_2977);
lean_ctor_set_usize(x_3065, 2, x_2978);
x_3066 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3066, 0, x_3065);
lean_ctor_set(x_3066, 1, x_2975);
lean_ctor_set_usize(x_3066, 2, x_2976);
x_3067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3067, 0, x_3066);
lean_ctor_set(x_3067, 1, x_17);
x_3068 = 1;
lean_inc(x_3067);
x_3069 = l_Lean_Syntax_isTermId_x3f(x_3067, x_3068);
if (lean_obj_tag(x_3069) == 0)
{
lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; 
lean_dec(x_3067);
x_3070 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3071 = lean_ctor_get(x_3070, 0);
lean_inc(x_3071);
x_3072 = lean_ctor_get(x_3070, 1);
lean_inc(x_3072);
lean_dec(x_3070);
x_3073 = lean_unsigned_to_nat(1u);
x_3074 = lean_nat_add(x_3, x_3073);
lean_dec(x_3);
x_3075 = l_Lean_mkHole(x_11);
lean_inc(x_3071);
x_3076 = l_Lean_Elab_Term_mkExplicitBinder(x_3071, x_3075);
x_3077 = lean_array_push(x_4, x_3076);
lean_inc(x_5);
x_3078 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3074, x_3077, x_5, x_3072);
if (lean_obj_tag(x_3078) == 0)
{
lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; lean_object* x_3086; lean_object* x_3087; lean_object* x_3088; lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; 
x_3079 = lean_ctor_get(x_3078, 0);
lean_inc(x_3079);
x_3080 = lean_ctor_get(x_3078, 1);
lean_inc(x_3080);
lean_dec(x_3078);
x_3081 = lean_ctor_get(x_3079, 0);
lean_inc(x_3081);
x_3082 = lean_ctor_get(x_3079, 1);
lean_inc(x_3082);
if (lean_is_exclusive(x_3079)) {
 lean_ctor_release(x_3079, 0);
 lean_ctor_release(x_3079, 1);
 x_3083 = x_3079;
} else {
 lean_dec_ref(x_3079);
 x_3083 = lean_box(0);
}
x_3084 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3080);
lean_dec(x_5);
x_3085 = lean_ctor_get(x_3084, 1);
lean_inc(x_3085);
lean_dec(x_3084);
x_3086 = l_Lean_Elab_Term_getMainModule___rarg(x_3085);
x_3087 = lean_ctor_get(x_3086, 1);
lean_inc(x_3087);
if (lean_is_exclusive(x_3086)) {
 lean_ctor_release(x_3086, 0);
 lean_ctor_release(x_3086, 1);
 x_3088 = x_3086;
} else {
 lean_dec_ref(x_3086);
 x_3088 = lean_box(0);
}
x_3089 = l_Array_empty___closed__1;
x_3090 = lean_array_push(x_3089, x_3071);
x_3091 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3092 = lean_array_push(x_3090, x_3091);
x_3093 = l_Lean_mkTermIdFromIdent___closed__2;
x_3094 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3094, 0, x_3093);
lean_ctor_set(x_3094, 1, x_3092);
x_3095 = lean_array_push(x_3089, x_3094);
x_3096 = l_Lean_nullKind___closed__2;
x_3097 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3097, 0, x_3096);
lean_ctor_set(x_3097, 1, x_3095);
x_3098 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3099 = lean_array_push(x_3098, x_3097);
x_3100 = lean_array_push(x_3099, x_3091);
x_3101 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3102 = lean_array_push(x_3100, x_3101);
x_3103 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3104 = lean_array_push(x_3102, x_3103);
lean_inc(x_11);
x_3105 = lean_array_push(x_3089, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3106 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3106 = lean_box(0);
}
if (lean_is_scalar(x_3106)) {
 x_3107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3107 = x_3106;
}
lean_ctor_set(x_3107, 0, x_3096);
lean_ctor_set(x_3107, 1, x_3105);
x_3108 = lean_array_push(x_3089, x_3107);
x_3109 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3110 = lean_array_push(x_3108, x_3109);
x_3111 = lean_array_push(x_3110, x_3082);
x_3112 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3113, 0, x_3112);
lean_ctor_set(x_3113, 1, x_3111);
x_3114 = lean_array_push(x_3089, x_3113);
x_3115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3115, 0, x_3096);
lean_ctor_set(x_3115, 1, x_3114);
x_3116 = lean_array_push(x_3104, x_3115);
x_3117 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3118, 0, x_3117);
lean_ctor_set(x_3118, 1, x_3116);
if (lean_is_scalar(x_3083)) {
 x_3119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3119 = x_3083;
}
lean_ctor_set(x_3119, 0, x_3081);
lean_ctor_set(x_3119, 1, x_3118);
if (lean_is_scalar(x_3088)) {
 x_3120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3120 = x_3088;
}
lean_ctor_set(x_3120, 0, x_3119);
lean_ctor_set(x_3120, 1, x_3087);
return x_3120;
}
else
{
lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; 
lean_dec(x_3071);
lean_dec(x_11);
lean_dec(x_5);
x_3121 = lean_ctor_get(x_3078, 0);
lean_inc(x_3121);
x_3122 = lean_ctor_get(x_3078, 1);
lean_inc(x_3122);
if (lean_is_exclusive(x_3078)) {
 lean_ctor_release(x_3078, 0);
 lean_ctor_release(x_3078, 1);
 x_3123 = x_3078;
} else {
 lean_dec_ref(x_3078);
 x_3123 = lean_box(0);
}
if (lean_is_scalar(x_3123)) {
 x_3124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3124 = x_3123;
}
lean_ctor_set(x_3124, 0, x_3121);
lean_ctor_set(x_3124, 1, x_3122);
return x_3124;
}
}
else
{
lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; uint8_t x_3128; 
lean_dec(x_11);
x_3125 = lean_ctor_get(x_3069, 0);
lean_inc(x_3125);
lean_dec(x_3069);
x_3126 = lean_ctor_get(x_3125, 0);
lean_inc(x_3126);
x_3127 = lean_ctor_get(x_3125, 1);
lean_inc(x_3127);
lean_dec(x_3125);
x_3128 = l_Lean_Syntax_isNone(x_3127);
lean_dec(x_3127);
if (x_3128 == 0)
{
lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; 
lean_dec(x_3126);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3129 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_3130 = l_Lean_Elab_Term_throwError___rarg(x_3067, x_3129, x_5, x_6);
lean_dec(x_3067);
x_3131 = lean_ctor_get(x_3130, 0);
lean_inc(x_3131);
x_3132 = lean_ctor_get(x_3130, 1);
lean_inc(x_3132);
if (lean_is_exclusive(x_3130)) {
 lean_ctor_release(x_3130, 0);
 lean_ctor_release(x_3130, 1);
 x_3133 = x_3130;
} else {
 lean_dec_ref(x_3130);
 x_3133 = lean_box(0);
}
if (lean_is_scalar(x_3133)) {
 x_3134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3134 = x_3133;
}
lean_ctor_set(x_3134, 0, x_3131);
lean_ctor_set(x_3134, 1, x_3132);
return x_3134;
}
else
{
lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; lean_object* x_3139; 
x_3135 = l_Lean_mkHole(x_3067);
lean_dec(x_3067);
x_3136 = lean_unsigned_to_nat(1u);
x_3137 = lean_nat_add(x_3, x_3136);
lean_dec(x_3);
x_3138 = l_Lean_Elab_Term_mkExplicitBinder(x_3126, x_3135);
x_3139 = lean_array_push(x_4, x_3138);
x_3 = x_3137;
x_4 = x_3139;
goto _start;
}
}
}
else
{
lean_object* x_3141; uint8_t x_3142; 
lean_dec(x_2980);
x_3141 = l_Lean_mkAppStx___closed__5;
x_3142 = lean_string_dec_eq(x_2977, x_3141);
if (x_3142 == 0)
{
lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; lean_object* x_3146; lean_object* x_3147; uint8_t x_3148; lean_object* x_3149; 
if (lean_is_scalar(x_2985)) {
 x_3143 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3143 = x_2985;
}
lean_ctor_set(x_3143, 0, x_16);
lean_ctor_set(x_3143, 1, x_2986);
lean_ctor_set_usize(x_3143, 2, x_2984);
if (lean_is_scalar(x_2982)) {
 x_3144 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3144 = x_2982;
}
lean_ctor_set(x_3144, 0, x_3143);
lean_ctor_set(x_3144, 1, x_3061);
lean_ctor_set_usize(x_3144, 2, x_2981);
if (lean_is_scalar(x_2979)) {
 x_3145 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3145 = x_2979;
}
lean_ctor_set(x_3145, 0, x_3144);
lean_ctor_set(x_3145, 1, x_2977);
lean_ctor_set_usize(x_3145, 2, x_2978);
x_3146 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3146, 0, x_3145);
lean_ctor_set(x_3146, 1, x_2975);
lean_ctor_set_usize(x_3146, 2, x_2976);
x_3147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3147, 0, x_3146);
lean_ctor_set(x_3147, 1, x_17);
x_3148 = 1;
lean_inc(x_3147);
x_3149 = l_Lean_Syntax_isTermId_x3f(x_3147, x_3148);
if (lean_obj_tag(x_3149) == 0)
{
lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; 
lean_dec(x_3147);
x_3150 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3151 = lean_ctor_get(x_3150, 0);
lean_inc(x_3151);
x_3152 = lean_ctor_get(x_3150, 1);
lean_inc(x_3152);
lean_dec(x_3150);
x_3153 = lean_unsigned_to_nat(1u);
x_3154 = lean_nat_add(x_3, x_3153);
lean_dec(x_3);
x_3155 = l_Lean_mkHole(x_11);
lean_inc(x_3151);
x_3156 = l_Lean_Elab_Term_mkExplicitBinder(x_3151, x_3155);
x_3157 = lean_array_push(x_4, x_3156);
lean_inc(x_5);
x_3158 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3154, x_3157, x_5, x_3152);
if (lean_obj_tag(x_3158) == 0)
{
lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; lean_object* x_3182; lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; lean_object* x_3188; lean_object* x_3189; lean_object* x_3190; lean_object* x_3191; lean_object* x_3192; lean_object* x_3193; lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; 
x_3159 = lean_ctor_get(x_3158, 0);
lean_inc(x_3159);
x_3160 = lean_ctor_get(x_3158, 1);
lean_inc(x_3160);
lean_dec(x_3158);
x_3161 = lean_ctor_get(x_3159, 0);
lean_inc(x_3161);
x_3162 = lean_ctor_get(x_3159, 1);
lean_inc(x_3162);
if (lean_is_exclusive(x_3159)) {
 lean_ctor_release(x_3159, 0);
 lean_ctor_release(x_3159, 1);
 x_3163 = x_3159;
} else {
 lean_dec_ref(x_3159);
 x_3163 = lean_box(0);
}
x_3164 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3160);
lean_dec(x_5);
x_3165 = lean_ctor_get(x_3164, 1);
lean_inc(x_3165);
lean_dec(x_3164);
x_3166 = l_Lean_Elab_Term_getMainModule___rarg(x_3165);
x_3167 = lean_ctor_get(x_3166, 1);
lean_inc(x_3167);
if (lean_is_exclusive(x_3166)) {
 lean_ctor_release(x_3166, 0);
 lean_ctor_release(x_3166, 1);
 x_3168 = x_3166;
} else {
 lean_dec_ref(x_3166);
 x_3168 = lean_box(0);
}
x_3169 = l_Array_empty___closed__1;
x_3170 = lean_array_push(x_3169, x_3151);
x_3171 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3172 = lean_array_push(x_3170, x_3171);
x_3173 = l_Lean_mkTermIdFromIdent___closed__2;
x_3174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3174, 0, x_3173);
lean_ctor_set(x_3174, 1, x_3172);
x_3175 = lean_array_push(x_3169, x_3174);
x_3176 = l_Lean_nullKind___closed__2;
x_3177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3177, 0, x_3176);
lean_ctor_set(x_3177, 1, x_3175);
x_3178 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3179 = lean_array_push(x_3178, x_3177);
x_3180 = lean_array_push(x_3179, x_3171);
x_3181 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3182 = lean_array_push(x_3180, x_3181);
x_3183 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3184 = lean_array_push(x_3182, x_3183);
lean_inc(x_11);
x_3185 = lean_array_push(x_3169, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3186 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3186 = lean_box(0);
}
if (lean_is_scalar(x_3186)) {
 x_3187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3187 = x_3186;
}
lean_ctor_set(x_3187, 0, x_3176);
lean_ctor_set(x_3187, 1, x_3185);
x_3188 = lean_array_push(x_3169, x_3187);
x_3189 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3190 = lean_array_push(x_3188, x_3189);
x_3191 = lean_array_push(x_3190, x_3162);
x_3192 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3193, 0, x_3192);
lean_ctor_set(x_3193, 1, x_3191);
x_3194 = lean_array_push(x_3169, x_3193);
x_3195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3195, 0, x_3176);
lean_ctor_set(x_3195, 1, x_3194);
x_3196 = lean_array_push(x_3184, x_3195);
x_3197 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3198, 0, x_3197);
lean_ctor_set(x_3198, 1, x_3196);
if (lean_is_scalar(x_3163)) {
 x_3199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3199 = x_3163;
}
lean_ctor_set(x_3199, 0, x_3161);
lean_ctor_set(x_3199, 1, x_3198);
if (lean_is_scalar(x_3168)) {
 x_3200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3200 = x_3168;
}
lean_ctor_set(x_3200, 0, x_3199);
lean_ctor_set(x_3200, 1, x_3167);
return x_3200;
}
else
{
lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; 
lean_dec(x_3151);
lean_dec(x_11);
lean_dec(x_5);
x_3201 = lean_ctor_get(x_3158, 0);
lean_inc(x_3201);
x_3202 = lean_ctor_get(x_3158, 1);
lean_inc(x_3202);
if (lean_is_exclusive(x_3158)) {
 lean_ctor_release(x_3158, 0);
 lean_ctor_release(x_3158, 1);
 x_3203 = x_3158;
} else {
 lean_dec_ref(x_3158);
 x_3203 = lean_box(0);
}
if (lean_is_scalar(x_3203)) {
 x_3204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3204 = x_3203;
}
lean_ctor_set(x_3204, 0, x_3201);
lean_ctor_set(x_3204, 1, x_3202);
return x_3204;
}
}
else
{
lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; uint8_t x_3208; 
lean_dec(x_11);
x_3205 = lean_ctor_get(x_3149, 0);
lean_inc(x_3205);
lean_dec(x_3149);
x_3206 = lean_ctor_get(x_3205, 0);
lean_inc(x_3206);
x_3207 = lean_ctor_get(x_3205, 1);
lean_inc(x_3207);
lean_dec(x_3205);
x_3208 = l_Lean_Syntax_isNone(x_3207);
lean_dec(x_3207);
if (x_3208 == 0)
{
lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; 
lean_dec(x_3206);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3209 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_3210 = l_Lean_Elab_Term_throwError___rarg(x_3147, x_3209, x_5, x_6);
lean_dec(x_3147);
x_3211 = lean_ctor_get(x_3210, 0);
lean_inc(x_3211);
x_3212 = lean_ctor_get(x_3210, 1);
lean_inc(x_3212);
if (lean_is_exclusive(x_3210)) {
 lean_ctor_release(x_3210, 0);
 lean_ctor_release(x_3210, 1);
 x_3213 = x_3210;
} else {
 lean_dec_ref(x_3210);
 x_3213 = lean_box(0);
}
if (lean_is_scalar(x_3213)) {
 x_3214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3214 = x_3213;
}
lean_ctor_set(x_3214, 0, x_3211);
lean_ctor_set(x_3214, 1, x_3212);
return x_3214;
}
else
{
lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; 
x_3215 = l_Lean_mkHole(x_3147);
lean_dec(x_3147);
x_3216 = lean_unsigned_to_nat(1u);
x_3217 = lean_nat_add(x_3, x_3216);
lean_dec(x_3);
x_3218 = l_Lean_Elab_Term_mkExplicitBinder(x_3206, x_3215);
x_3219 = lean_array_push(x_4, x_3218);
x_3 = x_3217;
x_4 = x_3219;
goto _start;
}
}
}
else
{
lean_object* x_3221; uint8_t x_3222; 
lean_dec(x_2977);
x_3221 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_3222 = lean_string_dec_eq(x_2975, x_3221);
if (x_3222 == 0)
{
lean_object* x_3223; uint8_t x_3224; 
x_3223 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_3224 = lean_string_dec_eq(x_2975, x_3223);
if (x_3224 == 0)
{
lean_object* x_3225; uint8_t x_3226; 
x_3225 = l_Lean_mkHole___closed__1;
x_3226 = lean_string_dec_eq(x_2975, x_3225);
if (x_3226 == 0)
{
lean_object* x_3227; uint8_t x_3228; 
x_3227 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_3228 = lean_string_dec_eq(x_2975, x_3227);
if (x_3228 == 0)
{
lean_object* x_3229; lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; uint8_t x_3234; lean_object* x_3235; 
if (lean_is_scalar(x_2985)) {
 x_3229 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3229 = x_2985;
}
lean_ctor_set(x_3229, 0, x_16);
lean_ctor_set(x_3229, 1, x_2986);
lean_ctor_set_usize(x_3229, 2, x_2984);
if (lean_is_scalar(x_2982)) {
 x_3230 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3230 = x_2982;
}
lean_ctor_set(x_3230, 0, x_3229);
lean_ctor_set(x_3230, 1, x_3061);
lean_ctor_set_usize(x_3230, 2, x_2981);
if (lean_is_scalar(x_2979)) {
 x_3231 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3231 = x_2979;
}
lean_ctor_set(x_3231, 0, x_3230);
lean_ctor_set(x_3231, 1, x_3141);
lean_ctor_set_usize(x_3231, 2, x_2978);
x_3232 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3232, 0, x_3231);
lean_ctor_set(x_3232, 1, x_2975);
lean_ctor_set_usize(x_3232, 2, x_2976);
x_3233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3233, 0, x_3232);
lean_ctor_set(x_3233, 1, x_17);
x_3234 = 1;
lean_inc(x_3233);
x_3235 = l_Lean_Syntax_isTermId_x3f(x_3233, x_3234);
if (lean_obj_tag(x_3235) == 0)
{
lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; lean_object* x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; 
lean_dec(x_3233);
x_3236 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3237 = lean_ctor_get(x_3236, 0);
lean_inc(x_3237);
x_3238 = lean_ctor_get(x_3236, 1);
lean_inc(x_3238);
lean_dec(x_3236);
x_3239 = lean_unsigned_to_nat(1u);
x_3240 = lean_nat_add(x_3, x_3239);
lean_dec(x_3);
x_3241 = l_Lean_mkHole(x_11);
lean_inc(x_3237);
x_3242 = l_Lean_Elab_Term_mkExplicitBinder(x_3237, x_3241);
x_3243 = lean_array_push(x_4, x_3242);
lean_inc(x_5);
x_3244 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3240, x_3243, x_5, x_3238);
if (lean_obj_tag(x_3244) == 0)
{
lean_object* x_3245; lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; lean_object* x_3250; lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; lean_object* x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; 
x_3245 = lean_ctor_get(x_3244, 0);
lean_inc(x_3245);
x_3246 = lean_ctor_get(x_3244, 1);
lean_inc(x_3246);
lean_dec(x_3244);
x_3247 = lean_ctor_get(x_3245, 0);
lean_inc(x_3247);
x_3248 = lean_ctor_get(x_3245, 1);
lean_inc(x_3248);
if (lean_is_exclusive(x_3245)) {
 lean_ctor_release(x_3245, 0);
 lean_ctor_release(x_3245, 1);
 x_3249 = x_3245;
} else {
 lean_dec_ref(x_3245);
 x_3249 = lean_box(0);
}
x_3250 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3246);
lean_dec(x_5);
x_3251 = lean_ctor_get(x_3250, 1);
lean_inc(x_3251);
lean_dec(x_3250);
x_3252 = l_Lean_Elab_Term_getMainModule___rarg(x_3251);
x_3253 = lean_ctor_get(x_3252, 1);
lean_inc(x_3253);
if (lean_is_exclusive(x_3252)) {
 lean_ctor_release(x_3252, 0);
 lean_ctor_release(x_3252, 1);
 x_3254 = x_3252;
} else {
 lean_dec_ref(x_3252);
 x_3254 = lean_box(0);
}
x_3255 = l_Array_empty___closed__1;
x_3256 = lean_array_push(x_3255, x_3237);
x_3257 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3258 = lean_array_push(x_3256, x_3257);
x_3259 = l_Lean_mkTermIdFromIdent___closed__2;
x_3260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3260, 0, x_3259);
lean_ctor_set(x_3260, 1, x_3258);
x_3261 = lean_array_push(x_3255, x_3260);
x_3262 = l_Lean_nullKind___closed__2;
x_3263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3263, 0, x_3262);
lean_ctor_set(x_3263, 1, x_3261);
x_3264 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3265 = lean_array_push(x_3264, x_3263);
x_3266 = lean_array_push(x_3265, x_3257);
x_3267 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3268 = lean_array_push(x_3266, x_3267);
x_3269 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3270 = lean_array_push(x_3268, x_3269);
lean_inc(x_11);
x_3271 = lean_array_push(x_3255, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3272 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3272 = lean_box(0);
}
if (lean_is_scalar(x_3272)) {
 x_3273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3273 = x_3272;
}
lean_ctor_set(x_3273, 0, x_3262);
lean_ctor_set(x_3273, 1, x_3271);
x_3274 = lean_array_push(x_3255, x_3273);
x_3275 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3276 = lean_array_push(x_3274, x_3275);
x_3277 = lean_array_push(x_3276, x_3248);
x_3278 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3279, 0, x_3278);
lean_ctor_set(x_3279, 1, x_3277);
x_3280 = lean_array_push(x_3255, x_3279);
x_3281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3281, 0, x_3262);
lean_ctor_set(x_3281, 1, x_3280);
x_3282 = lean_array_push(x_3270, x_3281);
x_3283 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3284, 0, x_3283);
lean_ctor_set(x_3284, 1, x_3282);
if (lean_is_scalar(x_3249)) {
 x_3285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3285 = x_3249;
}
lean_ctor_set(x_3285, 0, x_3247);
lean_ctor_set(x_3285, 1, x_3284);
if (lean_is_scalar(x_3254)) {
 x_3286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3286 = x_3254;
}
lean_ctor_set(x_3286, 0, x_3285);
lean_ctor_set(x_3286, 1, x_3253);
return x_3286;
}
else
{
lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; 
lean_dec(x_3237);
lean_dec(x_11);
lean_dec(x_5);
x_3287 = lean_ctor_get(x_3244, 0);
lean_inc(x_3287);
x_3288 = lean_ctor_get(x_3244, 1);
lean_inc(x_3288);
if (lean_is_exclusive(x_3244)) {
 lean_ctor_release(x_3244, 0);
 lean_ctor_release(x_3244, 1);
 x_3289 = x_3244;
} else {
 lean_dec_ref(x_3244);
 x_3289 = lean_box(0);
}
if (lean_is_scalar(x_3289)) {
 x_3290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3290 = x_3289;
}
lean_ctor_set(x_3290, 0, x_3287);
lean_ctor_set(x_3290, 1, x_3288);
return x_3290;
}
}
else
{
lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; uint8_t x_3294; 
lean_dec(x_11);
x_3291 = lean_ctor_get(x_3235, 0);
lean_inc(x_3291);
lean_dec(x_3235);
x_3292 = lean_ctor_get(x_3291, 0);
lean_inc(x_3292);
x_3293 = lean_ctor_get(x_3291, 1);
lean_inc(x_3293);
lean_dec(x_3291);
x_3294 = l_Lean_Syntax_isNone(x_3293);
lean_dec(x_3293);
if (x_3294 == 0)
{
lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; 
lean_dec(x_3292);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3295 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_3296 = l_Lean_Elab_Term_throwError___rarg(x_3233, x_3295, x_5, x_6);
lean_dec(x_3233);
x_3297 = lean_ctor_get(x_3296, 0);
lean_inc(x_3297);
x_3298 = lean_ctor_get(x_3296, 1);
lean_inc(x_3298);
if (lean_is_exclusive(x_3296)) {
 lean_ctor_release(x_3296, 0);
 lean_ctor_release(x_3296, 1);
 x_3299 = x_3296;
} else {
 lean_dec_ref(x_3296);
 x_3299 = lean_box(0);
}
if (lean_is_scalar(x_3299)) {
 x_3300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3300 = x_3299;
}
lean_ctor_set(x_3300, 0, x_3297);
lean_ctor_set(x_3300, 1, x_3298);
return x_3300;
}
else
{
lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; 
x_3301 = l_Lean_mkHole(x_3233);
lean_dec(x_3233);
x_3302 = lean_unsigned_to_nat(1u);
x_3303 = lean_nat_add(x_3, x_3302);
lean_dec(x_3);
x_3304 = l_Lean_Elab_Term_mkExplicitBinder(x_3292, x_3301);
x_3305 = lean_array_push(x_4, x_3304);
x_3 = x_3303;
x_4 = x_3305;
goto _start;
}
}
}
else
{
lean_object* x_3307; lean_object* x_3308; uint8_t x_3309; 
lean_dec(x_2985);
lean_dec(x_2982);
lean_dec(x_2979);
lean_dec(x_2975);
lean_dec(x_17);
x_3307 = lean_unsigned_to_nat(1u);
x_3308 = l_Lean_Syntax_getArg(x_11, x_3307);
x_3309 = l_Lean_Syntax_isNone(x_3308);
if (x_3309 == 0)
{
lean_object* x_3310; lean_object* x_3311; lean_object* x_3312; uint8_t x_3313; 
x_3310 = lean_unsigned_to_nat(0u);
x_3311 = l_Lean_Syntax_getArg(x_3308, x_3310);
x_3312 = l_Lean_Syntax_getArg(x_3308, x_3307);
lean_dec(x_3308);
x_3313 = l_Lean_Syntax_isNone(x_3312);
if (x_3313 == 0)
{
lean_object* x_3314; lean_object* x_3315; lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; uint8_t x_3321; 
x_3314 = l_Lean_Syntax_getArg(x_3312, x_3310);
lean_dec(x_3312);
lean_inc(x_3314);
x_3315 = l_Lean_Syntax_getKind(x_3314);
x_3316 = lean_name_mk_string(x_16, x_2986);
x_3317 = lean_name_mk_string(x_3316, x_3061);
x_3318 = lean_name_mk_string(x_3317, x_3141);
x_3319 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_3320 = lean_name_mk_string(x_3318, x_3319);
x_3321 = lean_name_eq(x_3315, x_3320);
lean_dec(x_3320);
lean_dec(x_3315);
if (x_3321 == 0)
{
lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; 
lean_dec(x_3314);
lean_dec(x_3311);
x_3322 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3323 = lean_ctor_get(x_3322, 0);
lean_inc(x_3323);
x_3324 = lean_ctor_get(x_3322, 1);
lean_inc(x_3324);
lean_dec(x_3322);
x_3325 = lean_nat_add(x_3, x_3307);
lean_dec(x_3);
x_3326 = l_Lean_mkHole(x_11);
lean_inc(x_3323);
x_3327 = l_Lean_Elab_Term_mkExplicitBinder(x_3323, x_3326);
x_3328 = lean_array_push(x_4, x_3327);
lean_inc(x_5);
x_3329 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3325, x_3328, x_5, x_3324);
if (lean_obj_tag(x_3329) == 0)
{
lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; lean_object* x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; lean_object* x_3366; lean_object* x_3367; lean_object* x_3368; lean_object* x_3369; lean_object* x_3370; lean_object* x_3371; 
x_3330 = lean_ctor_get(x_3329, 0);
lean_inc(x_3330);
x_3331 = lean_ctor_get(x_3329, 1);
lean_inc(x_3331);
lean_dec(x_3329);
x_3332 = lean_ctor_get(x_3330, 0);
lean_inc(x_3332);
x_3333 = lean_ctor_get(x_3330, 1);
lean_inc(x_3333);
if (lean_is_exclusive(x_3330)) {
 lean_ctor_release(x_3330, 0);
 lean_ctor_release(x_3330, 1);
 x_3334 = x_3330;
} else {
 lean_dec_ref(x_3330);
 x_3334 = lean_box(0);
}
x_3335 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3331);
lean_dec(x_5);
x_3336 = lean_ctor_get(x_3335, 1);
lean_inc(x_3336);
lean_dec(x_3335);
x_3337 = l_Lean_Elab_Term_getMainModule___rarg(x_3336);
x_3338 = lean_ctor_get(x_3337, 1);
lean_inc(x_3338);
if (lean_is_exclusive(x_3337)) {
 lean_ctor_release(x_3337, 0);
 lean_ctor_release(x_3337, 1);
 x_3339 = x_3337;
} else {
 lean_dec_ref(x_3337);
 x_3339 = lean_box(0);
}
x_3340 = l_Array_empty___closed__1;
x_3341 = lean_array_push(x_3340, x_3323);
x_3342 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3343 = lean_array_push(x_3341, x_3342);
x_3344 = l_Lean_mkTermIdFromIdent___closed__2;
x_3345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3345, 0, x_3344);
lean_ctor_set(x_3345, 1, x_3343);
x_3346 = lean_array_push(x_3340, x_3345);
x_3347 = l_Lean_nullKind___closed__2;
x_3348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3348, 0, x_3347);
lean_ctor_set(x_3348, 1, x_3346);
x_3349 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3350 = lean_array_push(x_3349, x_3348);
x_3351 = lean_array_push(x_3350, x_3342);
x_3352 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3353 = lean_array_push(x_3351, x_3352);
x_3354 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3355 = lean_array_push(x_3353, x_3354);
lean_inc(x_11);
x_3356 = lean_array_push(x_3340, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3357 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3357 = lean_box(0);
}
if (lean_is_scalar(x_3357)) {
 x_3358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3358 = x_3357;
}
lean_ctor_set(x_3358, 0, x_3347);
lean_ctor_set(x_3358, 1, x_3356);
x_3359 = lean_array_push(x_3340, x_3358);
x_3360 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3361 = lean_array_push(x_3359, x_3360);
x_3362 = lean_array_push(x_3361, x_3333);
x_3363 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3364, 0, x_3363);
lean_ctor_set(x_3364, 1, x_3362);
x_3365 = lean_array_push(x_3340, x_3364);
x_3366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3366, 0, x_3347);
lean_ctor_set(x_3366, 1, x_3365);
x_3367 = lean_array_push(x_3355, x_3366);
x_3368 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3369, 0, x_3368);
lean_ctor_set(x_3369, 1, x_3367);
if (lean_is_scalar(x_3334)) {
 x_3370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3370 = x_3334;
}
lean_ctor_set(x_3370, 0, x_3332);
lean_ctor_set(x_3370, 1, x_3369);
if (lean_is_scalar(x_3339)) {
 x_3371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3371 = x_3339;
}
lean_ctor_set(x_3371, 0, x_3370);
lean_ctor_set(x_3371, 1, x_3338);
return x_3371;
}
else
{
lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; lean_object* x_3375; 
lean_dec(x_3323);
lean_dec(x_11);
lean_dec(x_5);
x_3372 = lean_ctor_get(x_3329, 0);
lean_inc(x_3372);
x_3373 = lean_ctor_get(x_3329, 1);
lean_inc(x_3373);
if (lean_is_exclusive(x_3329)) {
 lean_ctor_release(x_3329, 0);
 lean_ctor_release(x_3329, 1);
 x_3374 = x_3329;
} else {
 lean_dec_ref(x_3329);
 x_3374 = lean_box(0);
}
if (lean_is_scalar(x_3374)) {
 x_3375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3375 = x_3374;
}
lean_ctor_set(x_3375, 0, x_3372);
lean_ctor_set(x_3375, 1, x_3373);
return x_3375;
}
}
else
{
lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; 
x_3376 = l_Lean_Syntax_getArg(x_3314, x_3307);
lean_dec(x_3314);
x_3377 = l___private_Init_Lean_Elab_Binders_9__getFunBinderIds_x3f(x_3311, x_5, x_6);
x_3378 = lean_ctor_get(x_3377, 0);
lean_inc(x_3378);
if (lean_obj_tag(x_3378) == 0)
{
lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; lean_object* x_3385; lean_object* x_3386; lean_object* x_3387; 
lean_dec(x_3376);
x_3379 = lean_ctor_get(x_3377, 1);
lean_inc(x_3379);
lean_dec(x_3377);
x_3380 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_3379);
x_3381 = lean_ctor_get(x_3380, 0);
lean_inc(x_3381);
x_3382 = lean_ctor_get(x_3380, 1);
lean_inc(x_3382);
lean_dec(x_3380);
x_3383 = lean_nat_add(x_3, x_3307);
lean_dec(x_3);
x_3384 = l_Lean_mkHole(x_11);
lean_inc(x_3381);
x_3385 = l_Lean_Elab_Term_mkExplicitBinder(x_3381, x_3384);
x_3386 = lean_array_push(x_4, x_3385);
lean_inc(x_5);
x_3387 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3383, x_3386, x_5, x_3382);
if (lean_obj_tag(x_3387) == 0)
{
lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; lean_object* x_3429; 
x_3388 = lean_ctor_get(x_3387, 0);
lean_inc(x_3388);
x_3389 = lean_ctor_get(x_3387, 1);
lean_inc(x_3389);
lean_dec(x_3387);
x_3390 = lean_ctor_get(x_3388, 0);
lean_inc(x_3390);
x_3391 = lean_ctor_get(x_3388, 1);
lean_inc(x_3391);
if (lean_is_exclusive(x_3388)) {
 lean_ctor_release(x_3388, 0);
 lean_ctor_release(x_3388, 1);
 x_3392 = x_3388;
} else {
 lean_dec_ref(x_3388);
 x_3392 = lean_box(0);
}
x_3393 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3389);
lean_dec(x_5);
x_3394 = lean_ctor_get(x_3393, 1);
lean_inc(x_3394);
lean_dec(x_3393);
x_3395 = l_Lean_Elab_Term_getMainModule___rarg(x_3394);
x_3396 = lean_ctor_get(x_3395, 1);
lean_inc(x_3396);
if (lean_is_exclusive(x_3395)) {
 lean_ctor_release(x_3395, 0);
 lean_ctor_release(x_3395, 1);
 x_3397 = x_3395;
} else {
 lean_dec_ref(x_3395);
 x_3397 = lean_box(0);
}
x_3398 = l_Array_empty___closed__1;
x_3399 = lean_array_push(x_3398, x_3381);
x_3400 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3401 = lean_array_push(x_3399, x_3400);
x_3402 = l_Lean_mkTermIdFromIdent___closed__2;
x_3403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3403, 0, x_3402);
lean_ctor_set(x_3403, 1, x_3401);
x_3404 = lean_array_push(x_3398, x_3403);
x_3405 = l_Lean_nullKind___closed__2;
x_3406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3406, 0, x_3405);
lean_ctor_set(x_3406, 1, x_3404);
x_3407 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3408 = lean_array_push(x_3407, x_3406);
x_3409 = lean_array_push(x_3408, x_3400);
x_3410 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3411 = lean_array_push(x_3409, x_3410);
x_3412 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3413 = lean_array_push(x_3411, x_3412);
lean_inc(x_11);
x_3414 = lean_array_push(x_3398, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3415 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3415 = lean_box(0);
}
if (lean_is_scalar(x_3415)) {
 x_3416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3416 = x_3415;
}
lean_ctor_set(x_3416, 0, x_3405);
lean_ctor_set(x_3416, 1, x_3414);
x_3417 = lean_array_push(x_3398, x_3416);
x_3418 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3419 = lean_array_push(x_3417, x_3418);
x_3420 = lean_array_push(x_3419, x_3391);
x_3421 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3422, 0, x_3421);
lean_ctor_set(x_3422, 1, x_3420);
x_3423 = lean_array_push(x_3398, x_3422);
x_3424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3424, 0, x_3405);
lean_ctor_set(x_3424, 1, x_3423);
x_3425 = lean_array_push(x_3413, x_3424);
x_3426 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3427, 0, x_3426);
lean_ctor_set(x_3427, 1, x_3425);
if (lean_is_scalar(x_3392)) {
 x_3428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3428 = x_3392;
}
lean_ctor_set(x_3428, 0, x_3390);
lean_ctor_set(x_3428, 1, x_3427);
if (lean_is_scalar(x_3397)) {
 x_3429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3429 = x_3397;
}
lean_ctor_set(x_3429, 0, x_3428);
lean_ctor_set(x_3429, 1, x_3396);
return x_3429;
}
else
{
lean_object* x_3430; lean_object* x_3431; lean_object* x_3432; lean_object* x_3433; 
lean_dec(x_3381);
lean_dec(x_11);
lean_dec(x_5);
x_3430 = lean_ctor_get(x_3387, 0);
lean_inc(x_3430);
x_3431 = lean_ctor_get(x_3387, 1);
lean_inc(x_3431);
if (lean_is_exclusive(x_3387)) {
 lean_ctor_release(x_3387, 0);
 lean_ctor_release(x_3387, 1);
 x_3432 = x_3387;
} else {
 lean_dec_ref(x_3387);
 x_3432 = lean_box(0);
}
if (lean_is_scalar(x_3432)) {
 x_3433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3433 = x_3432;
}
lean_ctor_set(x_3433, 0, x_3430);
lean_ctor_set(x_3433, 1, x_3431);
return x_3433;
}
}
else
{
lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; lean_object* x_3438; 
lean_dec(x_11);
x_3434 = lean_ctor_get(x_3377, 1);
lean_inc(x_3434);
lean_dec(x_3377);
x_3435 = lean_ctor_get(x_3378, 0);
lean_inc(x_3435);
lean_dec(x_3378);
x_3436 = lean_nat_add(x_3, x_3307);
lean_dec(x_3);
x_3437 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___spec__1(x_3376, x_3310, x_3435);
x_3438 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_3437, x_3437, x_3310, x_4);
lean_dec(x_3437);
x_3 = x_3436;
x_4 = x_3438;
x_6 = x_3434;
goto _start;
}
}
}
else
{
lean_object* x_3440; lean_object* x_3441; lean_object* x_3442; lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; 
lean_dec(x_3312);
lean_dec(x_3311);
x_3440 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3441 = lean_ctor_get(x_3440, 0);
lean_inc(x_3441);
x_3442 = lean_ctor_get(x_3440, 1);
lean_inc(x_3442);
lean_dec(x_3440);
x_3443 = lean_nat_add(x_3, x_3307);
lean_dec(x_3);
x_3444 = l_Lean_mkHole(x_11);
lean_inc(x_3441);
x_3445 = l_Lean_Elab_Term_mkExplicitBinder(x_3441, x_3444);
x_3446 = lean_array_push(x_4, x_3445);
lean_inc(x_5);
x_3447 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3443, x_3446, x_5, x_3442);
if (lean_obj_tag(x_3447) == 0)
{
lean_object* x_3448; lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; lean_object* x_3454; lean_object* x_3455; lean_object* x_3456; lean_object* x_3457; lean_object* x_3458; lean_object* x_3459; lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; lean_object* x_3470; lean_object* x_3471; lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; 
x_3448 = lean_ctor_get(x_3447, 0);
lean_inc(x_3448);
x_3449 = lean_ctor_get(x_3447, 1);
lean_inc(x_3449);
lean_dec(x_3447);
x_3450 = lean_ctor_get(x_3448, 0);
lean_inc(x_3450);
x_3451 = lean_ctor_get(x_3448, 1);
lean_inc(x_3451);
if (lean_is_exclusive(x_3448)) {
 lean_ctor_release(x_3448, 0);
 lean_ctor_release(x_3448, 1);
 x_3452 = x_3448;
} else {
 lean_dec_ref(x_3448);
 x_3452 = lean_box(0);
}
x_3453 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3449);
lean_dec(x_5);
x_3454 = lean_ctor_get(x_3453, 1);
lean_inc(x_3454);
lean_dec(x_3453);
x_3455 = l_Lean_Elab_Term_getMainModule___rarg(x_3454);
x_3456 = lean_ctor_get(x_3455, 1);
lean_inc(x_3456);
if (lean_is_exclusive(x_3455)) {
 lean_ctor_release(x_3455, 0);
 lean_ctor_release(x_3455, 1);
 x_3457 = x_3455;
} else {
 lean_dec_ref(x_3455);
 x_3457 = lean_box(0);
}
x_3458 = l_Array_empty___closed__1;
x_3459 = lean_array_push(x_3458, x_3441);
x_3460 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3461 = lean_array_push(x_3459, x_3460);
x_3462 = l_Lean_mkTermIdFromIdent___closed__2;
x_3463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3463, 0, x_3462);
lean_ctor_set(x_3463, 1, x_3461);
x_3464 = lean_array_push(x_3458, x_3463);
x_3465 = l_Lean_nullKind___closed__2;
x_3466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3466, 0, x_3465);
lean_ctor_set(x_3466, 1, x_3464);
x_3467 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3468 = lean_array_push(x_3467, x_3466);
x_3469 = lean_array_push(x_3468, x_3460);
x_3470 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3471 = lean_array_push(x_3469, x_3470);
x_3472 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3473 = lean_array_push(x_3471, x_3472);
lean_inc(x_11);
x_3474 = lean_array_push(x_3458, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3475 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3475 = lean_box(0);
}
if (lean_is_scalar(x_3475)) {
 x_3476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3476 = x_3475;
}
lean_ctor_set(x_3476, 0, x_3465);
lean_ctor_set(x_3476, 1, x_3474);
x_3477 = lean_array_push(x_3458, x_3476);
x_3478 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3479 = lean_array_push(x_3477, x_3478);
x_3480 = lean_array_push(x_3479, x_3451);
x_3481 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3482, 0, x_3481);
lean_ctor_set(x_3482, 1, x_3480);
x_3483 = lean_array_push(x_3458, x_3482);
x_3484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3484, 0, x_3465);
lean_ctor_set(x_3484, 1, x_3483);
x_3485 = lean_array_push(x_3473, x_3484);
x_3486 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3487, 0, x_3486);
lean_ctor_set(x_3487, 1, x_3485);
if (lean_is_scalar(x_3452)) {
 x_3488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3488 = x_3452;
}
lean_ctor_set(x_3488, 0, x_3450);
lean_ctor_set(x_3488, 1, x_3487);
if (lean_is_scalar(x_3457)) {
 x_3489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3489 = x_3457;
}
lean_ctor_set(x_3489, 0, x_3488);
lean_ctor_set(x_3489, 1, x_3456);
return x_3489;
}
else
{
lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; 
lean_dec(x_3441);
lean_dec(x_11);
lean_dec(x_5);
x_3490 = lean_ctor_get(x_3447, 0);
lean_inc(x_3490);
x_3491 = lean_ctor_get(x_3447, 1);
lean_inc(x_3491);
if (lean_is_exclusive(x_3447)) {
 lean_ctor_release(x_3447, 0);
 lean_ctor_release(x_3447, 1);
 x_3492 = x_3447;
} else {
 lean_dec_ref(x_3447);
 x_3492 = lean_box(0);
}
if (lean_is_scalar(x_3492)) {
 x_3493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3493 = x_3492;
}
lean_ctor_set(x_3493, 0, x_3490);
lean_ctor_set(x_3493, 1, x_3491);
return x_3493;
}
}
}
else
{
lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3499; lean_object* x_3500; lean_object* x_3501; 
lean_dec(x_3308);
x_3494 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3495 = lean_ctor_get(x_3494, 0);
lean_inc(x_3495);
x_3496 = lean_ctor_get(x_3494, 1);
lean_inc(x_3496);
lean_dec(x_3494);
x_3497 = lean_nat_add(x_3, x_3307);
lean_dec(x_3);
x_3498 = l_Lean_mkHole(x_11);
lean_inc(x_3495);
x_3499 = l_Lean_Elab_Term_mkExplicitBinder(x_3495, x_3498);
x_3500 = lean_array_push(x_4, x_3499);
lean_inc(x_5);
x_3501 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3497, x_3500, x_5, x_3496);
if (lean_obj_tag(x_3501) == 0)
{
lean_object* x_3502; lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; lean_object* x_3507; lean_object* x_3508; lean_object* x_3509; lean_object* x_3510; lean_object* x_3511; lean_object* x_3512; lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; lean_object* x_3541; lean_object* x_3542; lean_object* x_3543; 
x_3502 = lean_ctor_get(x_3501, 0);
lean_inc(x_3502);
x_3503 = lean_ctor_get(x_3501, 1);
lean_inc(x_3503);
lean_dec(x_3501);
x_3504 = lean_ctor_get(x_3502, 0);
lean_inc(x_3504);
x_3505 = lean_ctor_get(x_3502, 1);
lean_inc(x_3505);
if (lean_is_exclusive(x_3502)) {
 lean_ctor_release(x_3502, 0);
 lean_ctor_release(x_3502, 1);
 x_3506 = x_3502;
} else {
 lean_dec_ref(x_3502);
 x_3506 = lean_box(0);
}
x_3507 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3503);
lean_dec(x_5);
x_3508 = lean_ctor_get(x_3507, 1);
lean_inc(x_3508);
lean_dec(x_3507);
x_3509 = l_Lean_Elab_Term_getMainModule___rarg(x_3508);
x_3510 = lean_ctor_get(x_3509, 1);
lean_inc(x_3510);
if (lean_is_exclusive(x_3509)) {
 lean_ctor_release(x_3509, 0);
 lean_ctor_release(x_3509, 1);
 x_3511 = x_3509;
} else {
 lean_dec_ref(x_3509);
 x_3511 = lean_box(0);
}
x_3512 = l_Array_empty___closed__1;
x_3513 = lean_array_push(x_3512, x_3495);
x_3514 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3515 = lean_array_push(x_3513, x_3514);
x_3516 = l_Lean_mkTermIdFromIdent___closed__2;
x_3517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3517, 0, x_3516);
lean_ctor_set(x_3517, 1, x_3515);
x_3518 = lean_array_push(x_3512, x_3517);
x_3519 = l_Lean_nullKind___closed__2;
x_3520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3520, 0, x_3519);
lean_ctor_set(x_3520, 1, x_3518);
x_3521 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3522 = lean_array_push(x_3521, x_3520);
x_3523 = lean_array_push(x_3522, x_3514);
x_3524 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3525 = lean_array_push(x_3523, x_3524);
x_3526 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3527 = lean_array_push(x_3525, x_3526);
lean_inc(x_11);
x_3528 = lean_array_push(x_3512, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3529 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3529 = lean_box(0);
}
if (lean_is_scalar(x_3529)) {
 x_3530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3530 = x_3529;
}
lean_ctor_set(x_3530, 0, x_3519);
lean_ctor_set(x_3530, 1, x_3528);
x_3531 = lean_array_push(x_3512, x_3530);
x_3532 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3533 = lean_array_push(x_3531, x_3532);
x_3534 = lean_array_push(x_3533, x_3505);
x_3535 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3536, 0, x_3535);
lean_ctor_set(x_3536, 1, x_3534);
x_3537 = lean_array_push(x_3512, x_3536);
x_3538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3538, 0, x_3519);
lean_ctor_set(x_3538, 1, x_3537);
x_3539 = lean_array_push(x_3527, x_3538);
x_3540 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3541, 0, x_3540);
lean_ctor_set(x_3541, 1, x_3539);
if (lean_is_scalar(x_3506)) {
 x_3542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3542 = x_3506;
}
lean_ctor_set(x_3542, 0, x_3504);
lean_ctor_set(x_3542, 1, x_3541);
if (lean_is_scalar(x_3511)) {
 x_3543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3543 = x_3511;
}
lean_ctor_set(x_3543, 0, x_3542);
lean_ctor_set(x_3543, 1, x_3510);
return x_3543;
}
else
{
lean_object* x_3544; lean_object* x_3545; lean_object* x_3546; lean_object* x_3547; 
lean_dec(x_3495);
lean_dec(x_11);
lean_dec(x_5);
x_3544 = lean_ctor_get(x_3501, 0);
lean_inc(x_3544);
x_3545 = lean_ctor_get(x_3501, 1);
lean_inc(x_3545);
if (lean_is_exclusive(x_3501)) {
 lean_ctor_release(x_3501, 0);
 lean_ctor_release(x_3501, 1);
 x_3546 = x_3501;
} else {
 lean_dec_ref(x_3501);
 x_3546 = lean_box(0);
}
if (lean_is_scalar(x_3546)) {
 x_3547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3547 = x_3546;
}
lean_ctor_set(x_3547, 0, x_3544);
lean_ctor_set(x_3547, 1, x_3545);
return x_3547;
}
}
}
}
else
{
lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; lean_object* x_3554; 
lean_dec(x_2985);
lean_dec(x_2982);
lean_dec(x_2979);
lean_dec(x_2975);
lean_dec(x_17);
x_3548 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3549 = lean_ctor_get(x_3548, 0);
lean_inc(x_3549);
x_3550 = lean_ctor_get(x_3548, 1);
lean_inc(x_3550);
lean_dec(x_3548);
x_3551 = lean_unsigned_to_nat(1u);
x_3552 = lean_nat_add(x_3, x_3551);
lean_dec(x_3);
x_3553 = l_Lean_Elab_Term_mkExplicitBinder(x_3549, x_11);
x_3554 = lean_array_push(x_4, x_3553);
x_3 = x_3552;
x_4 = x_3554;
x_6 = x_3550;
goto _start;
}
}
else
{
lean_object* x_3556; lean_object* x_3557; lean_object* x_3558; 
lean_dec(x_2985);
lean_dec(x_2982);
lean_dec(x_2979);
lean_dec(x_2975);
lean_dec(x_17);
x_3556 = lean_unsigned_to_nat(1u);
x_3557 = lean_nat_add(x_3, x_3556);
lean_dec(x_3);
x_3558 = lean_array_push(x_4, x_11);
x_3 = x_3557;
x_4 = x_3558;
goto _start;
}
}
else
{
lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; 
lean_dec(x_2985);
lean_dec(x_2982);
lean_dec(x_2979);
lean_dec(x_2975);
lean_dec(x_17);
x_3560 = lean_unsigned_to_nat(1u);
x_3561 = lean_nat_add(x_3, x_3560);
lean_dec(x_3);
x_3562 = lean_array_push(x_4, x_11);
x_3 = x_3561;
x_4 = x_3562;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_3564; lean_object* x_3565; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_3564 = 1;
lean_inc(x_11);
x_3565 = l_Lean_Syntax_isTermId_x3f(x_11, x_3564);
if (lean_obj_tag(x_3565) == 0)
{
lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; lean_object* x_3573; lean_object* x_3574; 
x_3566 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3567 = lean_ctor_get(x_3566, 0);
lean_inc(x_3567);
x_3568 = lean_ctor_get(x_3566, 1);
lean_inc(x_3568);
lean_dec(x_3566);
x_3569 = lean_unsigned_to_nat(1u);
x_3570 = lean_nat_add(x_3, x_3569);
lean_dec(x_3);
x_3571 = l_Lean_mkHole(x_11);
lean_inc(x_3567);
x_3572 = l_Lean_Elab_Term_mkExplicitBinder(x_3567, x_3571);
x_3573 = lean_array_push(x_4, x_3572);
lean_inc(x_5);
x_3574 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3570, x_3573, x_5, x_3568);
if (lean_obj_tag(x_3574) == 0)
{
lean_object* x_3575; lean_object* x_3576; uint8_t x_3577; 
x_3575 = lean_ctor_get(x_3574, 0);
lean_inc(x_3575);
x_3576 = lean_ctor_get(x_3574, 1);
lean_inc(x_3576);
lean_dec(x_3574);
x_3577 = !lean_is_exclusive(x_3575);
if (x_3577 == 0)
{
lean_object* x_3578; lean_object* x_3579; lean_object* x_3580; lean_object* x_3581; uint8_t x_3582; 
x_3578 = lean_ctor_get(x_3575, 1);
x_3579 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3576);
lean_dec(x_5);
x_3580 = lean_ctor_get(x_3579, 1);
lean_inc(x_3580);
lean_dec(x_3579);
x_3581 = l_Lean_Elab_Term_getMainModule___rarg(x_3580);
x_3582 = !lean_is_exclusive(x_3581);
if (x_3582 == 0)
{
lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; lean_object* x_3591; lean_object* x_3592; lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; lean_object* x_3599; lean_object* x_3600; uint8_t x_3601; 
x_3583 = lean_ctor_get(x_3581, 0);
lean_dec(x_3583);
x_3584 = l_Array_empty___closed__1;
x_3585 = lean_array_push(x_3584, x_3567);
x_3586 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3587 = lean_array_push(x_3585, x_3586);
x_3588 = l_Lean_mkTermIdFromIdent___closed__2;
x_3589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3589, 0, x_3588);
lean_ctor_set(x_3589, 1, x_3587);
x_3590 = lean_array_push(x_3584, x_3589);
x_3591 = l_Lean_nullKind___closed__2;
x_3592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3592, 0, x_3591);
lean_ctor_set(x_3592, 1, x_3590);
x_3593 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3594 = lean_array_push(x_3593, x_3592);
x_3595 = lean_array_push(x_3594, x_3586);
x_3596 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3597 = lean_array_push(x_3595, x_3596);
x_3598 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3599 = lean_array_push(x_3597, x_3598);
lean_inc(x_11);
x_3600 = lean_array_push(x_3584, x_11);
x_3601 = !lean_is_exclusive(x_11);
if (x_3601 == 0)
{
lean_object* x_3602; lean_object* x_3603; lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; lean_object* x_3607; lean_object* x_3608; lean_object* x_3609; lean_object* x_3610; lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; lean_object* x_3614; 
x_3602 = lean_ctor_get(x_11, 1);
lean_dec(x_3602);
x_3603 = lean_ctor_get(x_11, 0);
lean_dec(x_3603);
lean_ctor_set(x_11, 1, x_3600);
lean_ctor_set(x_11, 0, x_3591);
x_3604 = lean_array_push(x_3584, x_11);
x_3605 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3606 = lean_array_push(x_3604, x_3605);
x_3607 = lean_array_push(x_3606, x_3578);
x_3608 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3609, 0, x_3608);
lean_ctor_set(x_3609, 1, x_3607);
x_3610 = lean_array_push(x_3584, x_3609);
x_3611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3611, 0, x_3591);
lean_ctor_set(x_3611, 1, x_3610);
x_3612 = lean_array_push(x_3599, x_3611);
x_3613 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3614, 0, x_3613);
lean_ctor_set(x_3614, 1, x_3612);
lean_ctor_set(x_3575, 1, x_3614);
lean_ctor_set(x_3581, 0, x_3575);
return x_3581;
}
else
{
lean_object* x_3615; lean_object* x_3616; lean_object* x_3617; lean_object* x_3618; lean_object* x_3619; lean_object* x_3620; lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; lean_object* x_3626; 
lean_dec(x_11);
x_3615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3615, 0, x_3591);
lean_ctor_set(x_3615, 1, x_3600);
x_3616 = lean_array_push(x_3584, x_3615);
x_3617 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3618 = lean_array_push(x_3616, x_3617);
x_3619 = lean_array_push(x_3618, x_3578);
x_3620 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3621, 0, x_3620);
lean_ctor_set(x_3621, 1, x_3619);
x_3622 = lean_array_push(x_3584, x_3621);
x_3623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3623, 0, x_3591);
lean_ctor_set(x_3623, 1, x_3622);
x_3624 = lean_array_push(x_3599, x_3623);
x_3625 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3626, 0, x_3625);
lean_ctor_set(x_3626, 1, x_3624);
lean_ctor_set(x_3575, 1, x_3626);
lean_ctor_set(x_3581, 0, x_3575);
return x_3581;
}
}
else
{
lean_object* x_3627; lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; lean_object* x_3631; lean_object* x_3632; lean_object* x_3633; lean_object* x_3634; lean_object* x_3635; lean_object* x_3636; lean_object* x_3637; lean_object* x_3638; lean_object* x_3639; lean_object* x_3640; lean_object* x_3641; lean_object* x_3642; lean_object* x_3643; lean_object* x_3644; lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; lean_object* x_3648; lean_object* x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; lean_object* x_3658; 
x_3627 = lean_ctor_get(x_3581, 1);
lean_inc(x_3627);
lean_dec(x_3581);
x_3628 = l_Array_empty___closed__1;
x_3629 = lean_array_push(x_3628, x_3567);
x_3630 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3631 = lean_array_push(x_3629, x_3630);
x_3632 = l_Lean_mkTermIdFromIdent___closed__2;
x_3633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3633, 0, x_3632);
lean_ctor_set(x_3633, 1, x_3631);
x_3634 = lean_array_push(x_3628, x_3633);
x_3635 = l_Lean_nullKind___closed__2;
x_3636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3636, 0, x_3635);
lean_ctor_set(x_3636, 1, x_3634);
x_3637 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3638 = lean_array_push(x_3637, x_3636);
x_3639 = lean_array_push(x_3638, x_3630);
x_3640 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3641 = lean_array_push(x_3639, x_3640);
x_3642 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3643 = lean_array_push(x_3641, x_3642);
lean_inc(x_11);
x_3644 = lean_array_push(x_3628, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3645 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3645 = lean_box(0);
}
if (lean_is_scalar(x_3645)) {
 x_3646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3646 = x_3645;
}
lean_ctor_set(x_3646, 0, x_3635);
lean_ctor_set(x_3646, 1, x_3644);
x_3647 = lean_array_push(x_3628, x_3646);
x_3648 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3649 = lean_array_push(x_3647, x_3648);
x_3650 = lean_array_push(x_3649, x_3578);
x_3651 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3652, 0, x_3651);
lean_ctor_set(x_3652, 1, x_3650);
x_3653 = lean_array_push(x_3628, x_3652);
x_3654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3654, 0, x_3635);
lean_ctor_set(x_3654, 1, x_3653);
x_3655 = lean_array_push(x_3643, x_3654);
x_3656 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3657, 0, x_3656);
lean_ctor_set(x_3657, 1, x_3655);
lean_ctor_set(x_3575, 1, x_3657);
x_3658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3658, 0, x_3575);
lean_ctor_set(x_3658, 1, x_3627);
return x_3658;
}
}
else
{
lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; lean_object* x_3662; lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; lean_object* x_3667; lean_object* x_3668; lean_object* x_3669; lean_object* x_3670; lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; lean_object* x_3677; lean_object* x_3678; lean_object* x_3679; lean_object* x_3680; lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; lean_object* x_3695; lean_object* x_3696; lean_object* x_3697; 
x_3659 = lean_ctor_get(x_3575, 0);
x_3660 = lean_ctor_get(x_3575, 1);
lean_inc(x_3660);
lean_inc(x_3659);
lean_dec(x_3575);
x_3661 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3576);
lean_dec(x_5);
x_3662 = lean_ctor_get(x_3661, 1);
lean_inc(x_3662);
lean_dec(x_3661);
x_3663 = l_Lean_Elab_Term_getMainModule___rarg(x_3662);
x_3664 = lean_ctor_get(x_3663, 1);
lean_inc(x_3664);
if (lean_is_exclusive(x_3663)) {
 lean_ctor_release(x_3663, 0);
 lean_ctor_release(x_3663, 1);
 x_3665 = x_3663;
} else {
 lean_dec_ref(x_3663);
 x_3665 = lean_box(0);
}
x_3666 = l_Array_empty___closed__1;
x_3667 = lean_array_push(x_3666, x_3567);
x_3668 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3669 = lean_array_push(x_3667, x_3668);
x_3670 = l_Lean_mkTermIdFromIdent___closed__2;
x_3671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3671, 0, x_3670);
lean_ctor_set(x_3671, 1, x_3669);
x_3672 = lean_array_push(x_3666, x_3671);
x_3673 = l_Lean_nullKind___closed__2;
x_3674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3674, 0, x_3673);
lean_ctor_set(x_3674, 1, x_3672);
x_3675 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3676 = lean_array_push(x_3675, x_3674);
x_3677 = lean_array_push(x_3676, x_3668);
x_3678 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3679 = lean_array_push(x_3677, x_3678);
x_3680 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3681 = lean_array_push(x_3679, x_3680);
lean_inc(x_11);
x_3682 = lean_array_push(x_3666, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3683 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3683 = lean_box(0);
}
if (lean_is_scalar(x_3683)) {
 x_3684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3684 = x_3683;
}
lean_ctor_set(x_3684, 0, x_3673);
lean_ctor_set(x_3684, 1, x_3682);
x_3685 = lean_array_push(x_3666, x_3684);
x_3686 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3687 = lean_array_push(x_3685, x_3686);
x_3688 = lean_array_push(x_3687, x_3660);
x_3689 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3690, 0, x_3689);
lean_ctor_set(x_3690, 1, x_3688);
x_3691 = lean_array_push(x_3666, x_3690);
x_3692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3692, 0, x_3673);
lean_ctor_set(x_3692, 1, x_3691);
x_3693 = lean_array_push(x_3681, x_3692);
x_3694 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3695, 0, x_3694);
lean_ctor_set(x_3695, 1, x_3693);
x_3696 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3696, 0, x_3659);
lean_ctor_set(x_3696, 1, x_3695);
if (lean_is_scalar(x_3665)) {
 x_3697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3697 = x_3665;
}
lean_ctor_set(x_3697, 0, x_3696);
lean_ctor_set(x_3697, 1, x_3664);
return x_3697;
}
}
else
{
uint8_t x_3698; 
lean_dec(x_3567);
lean_dec(x_11);
lean_dec(x_5);
x_3698 = !lean_is_exclusive(x_3574);
if (x_3698 == 0)
{
return x_3574;
}
else
{
lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; 
x_3699 = lean_ctor_get(x_3574, 0);
x_3700 = lean_ctor_get(x_3574, 1);
lean_inc(x_3700);
lean_inc(x_3699);
lean_dec(x_3574);
x_3701 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3701, 0, x_3699);
lean_ctor_set(x_3701, 1, x_3700);
return x_3701;
}
}
}
else
{
lean_object* x_3702; lean_object* x_3703; lean_object* x_3704; uint8_t x_3705; 
x_3702 = lean_ctor_get(x_3565, 0);
lean_inc(x_3702);
lean_dec(x_3565);
x_3703 = lean_ctor_get(x_3702, 0);
lean_inc(x_3703);
x_3704 = lean_ctor_get(x_3702, 1);
lean_inc(x_3704);
lean_dec(x_3702);
x_3705 = l_Lean_Syntax_isNone(x_3704);
lean_dec(x_3704);
if (x_3705 == 0)
{
lean_object* x_3706; lean_object* x_3707; uint8_t x_3708; 
lean_dec(x_3703);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3706 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_3707 = l_Lean_Elab_Term_throwError___rarg(x_11, x_3706, x_5, x_6);
lean_dec(x_11);
x_3708 = !lean_is_exclusive(x_3707);
if (x_3708 == 0)
{
return x_3707;
}
else
{
lean_object* x_3709; lean_object* x_3710; lean_object* x_3711; 
x_3709 = lean_ctor_get(x_3707, 0);
x_3710 = lean_ctor_get(x_3707, 1);
lean_inc(x_3710);
lean_inc(x_3709);
lean_dec(x_3707);
x_3711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3711, 0, x_3709);
lean_ctor_set(x_3711, 1, x_3710);
return x_3711;
}
}
else
{
lean_object* x_3712; lean_object* x_3713; lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; 
x_3712 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_3713 = lean_unsigned_to_nat(1u);
x_3714 = lean_nat_add(x_3, x_3713);
lean_dec(x_3);
x_3715 = l_Lean_Elab_Term_mkExplicitBinder(x_3703, x_3712);
x_3716 = lean_array_push(x_4, x_3715);
x_3 = x_3714;
x_4 = x_3716;
goto _start;
}
}
}
}
else
{
uint8_t x_3718; lean_object* x_3719; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_3718 = 1;
lean_inc(x_11);
x_3719 = l_Lean_Syntax_isTermId_x3f(x_11, x_3718);
if (lean_obj_tag(x_3719) == 0)
{
lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; 
x_3720 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3721 = lean_ctor_get(x_3720, 0);
lean_inc(x_3721);
x_3722 = lean_ctor_get(x_3720, 1);
lean_inc(x_3722);
lean_dec(x_3720);
x_3723 = lean_unsigned_to_nat(1u);
x_3724 = lean_nat_add(x_3, x_3723);
lean_dec(x_3);
x_3725 = l_Lean_mkHole(x_11);
lean_inc(x_3721);
x_3726 = l_Lean_Elab_Term_mkExplicitBinder(x_3721, x_3725);
x_3727 = lean_array_push(x_4, x_3726);
lean_inc(x_5);
x_3728 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3724, x_3727, x_5, x_3722);
if (lean_obj_tag(x_3728) == 0)
{
lean_object* x_3729; lean_object* x_3730; uint8_t x_3731; 
x_3729 = lean_ctor_get(x_3728, 0);
lean_inc(x_3729);
x_3730 = lean_ctor_get(x_3728, 1);
lean_inc(x_3730);
lean_dec(x_3728);
x_3731 = !lean_is_exclusive(x_3729);
if (x_3731 == 0)
{
lean_object* x_3732; lean_object* x_3733; lean_object* x_3734; lean_object* x_3735; uint8_t x_3736; 
x_3732 = lean_ctor_get(x_3729, 1);
x_3733 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3730);
lean_dec(x_5);
x_3734 = lean_ctor_get(x_3733, 1);
lean_inc(x_3734);
lean_dec(x_3733);
x_3735 = l_Lean_Elab_Term_getMainModule___rarg(x_3734);
x_3736 = !lean_is_exclusive(x_3735);
if (x_3736 == 0)
{
lean_object* x_3737; lean_object* x_3738; lean_object* x_3739; lean_object* x_3740; lean_object* x_3741; lean_object* x_3742; lean_object* x_3743; lean_object* x_3744; lean_object* x_3745; lean_object* x_3746; lean_object* x_3747; lean_object* x_3748; lean_object* x_3749; lean_object* x_3750; lean_object* x_3751; lean_object* x_3752; lean_object* x_3753; lean_object* x_3754; uint8_t x_3755; 
x_3737 = lean_ctor_get(x_3735, 0);
lean_dec(x_3737);
x_3738 = l_Array_empty___closed__1;
x_3739 = lean_array_push(x_3738, x_3721);
x_3740 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3741 = lean_array_push(x_3739, x_3740);
x_3742 = l_Lean_mkTermIdFromIdent___closed__2;
x_3743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3743, 0, x_3742);
lean_ctor_set(x_3743, 1, x_3741);
x_3744 = lean_array_push(x_3738, x_3743);
x_3745 = l_Lean_nullKind___closed__2;
x_3746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3746, 0, x_3745);
lean_ctor_set(x_3746, 1, x_3744);
x_3747 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3748 = lean_array_push(x_3747, x_3746);
x_3749 = lean_array_push(x_3748, x_3740);
x_3750 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3751 = lean_array_push(x_3749, x_3750);
x_3752 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3753 = lean_array_push(x_3751, x_3752);
lean_inc(x_11);
x_3754 = lean_array_push(x_3738, x_11);
x_3755 = !lean_is_exclusive(x_11);
if (x_3755 == 0)
{
lean_object* x_3756; lean_object* x_3757; lean_object* x_3758; lean_object* x_3759; lean_object* x_3760; lean_object* x_3761; lean_object* x_3762; lean_object* x_3763; lean_object* x_3764; lean_object* x_3765; lean_object* x_3766; lean_object* x_3767; lean_object* x_3768; 
x_3756 = lean_ctor_get(x_11, 1);
lean_dec(x_3756);
x_3757 = lean_ctor_get(x_11, 0);
lean_dec(x_3757);
lean_ctor_set(x_11, 1, x_3754);
lean_ctor_set(x_11, 0, x_3745);
x_3758 = lean_array_push(x_3738, x_11);
x_3759 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3760 = lean_array_push(x_3758, x_3759);
x_3761 = lean_array_push(x_3760, x_3732);
x_3762 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3763, 0, x_3762);
lean_ctor_set(x_3763, 1, x_3761);
x_3764 = lean_array_push(x_3738, x_3763);
x_3765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3765, 0, x_3745);
lean_ctor_set(x_3765, 1, x_3764);
x_3766 = lean_array_push(x_3753, x_3765);
x_3767 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3768, 0, x_3767);
lean_ctor_set(x_3768, 1, x_3766);
lean_ctor_set(x_3729, 1, x_3768);
lean_ctor_set(x_3735, 0, x_3729);
return x_3735;
}
else
{
lean_object* x_3769; lean_object* x_3770; lean_object* x_3771; lean_object* x_3772; lean_object* x_3773; lean_object* x_3774; lean_object* x_3775; lean_object* x_3776; lean_object* x_3777; lean_object* x_3778; lean_object* x_3779; lean_object* x_3780; 
lean_dec(x_11);
x_3769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3769, 0, x_3745);
lean_ctor_set(x_3769, 1, x_3754);
x_3770 = lean_array_push(x_3738, x_3769);
x_3771 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3772 = lean_array_push(x_3770, x_3771);
x_3773 = lean_array_push(x_3772, x_3732);
x_3774 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3775, 0, x_3774);
lean_ctor_set(x_3775, 1, x_3773);
x_3776 = lean_array_push(x_3738, x_3775);
x_3777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3777, 0, x_3745);
lean_ctor_set(x_3777, 1, x_3776);
x_3778 = lean_array_push(x_3753, x_3777);
x_3779 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3780, 0, x_3779);
lean_ctor_set(x_3780, 1, x_3778);
lean_ctor_set(x_3729, 1, x_3780);
lean_ctor_set(x_3735, 0, x_3729);
return x_3735;
}
}
else
{
lean_object* x_3781; lean_object* x_3782; lean_object* x_3783; lean_object* x_3784; lean_object* x_3785; lean_object* x_3786; lean_object* x_3787; lean_object* x_3788; lean_object* x_3789; lean_object* x_3790; lean_object* x_3791; lean_object* x_3792; lean_object* x_3793; lean_object* x_3794; lean_object* x_3795; lean_object* x_3796; lean_object* x_3797; lean_object* x_3798; lean_object* x_3799; lean_object* x_3800; lean_object* x_3801; lean_object* x_3802; lean_object* x_3803; lean_object* x_3804; lean_object* x_3805; lean_object* x_3806; lean_object* x_3807; lean_object* x_3808; lean_object* x_3809; lean_object* x_3810; lean_object* x_3811; lean_object* x_3812; 
x_3781 = lean_ctor_get(x_3735, 1);
lean_inc(x_3781);
lean_dec(x_3735);
x_3782 = l_Array_empty___closed__1;
x_3783 = lean_array_push(x_3782, x_3721);
x_3784 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3785 = lean_array_push(x_3783, x_3784);
x_3786 = l_Lean_mkTermIdFromIdent___closed__2;
x_3787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3787, 0, x_3786);
lean_ctor_set(x_3787, 1, x_3785);
x_3788 = lean_array_push(x_3782, x_3787);
x_3789 = l_Lean_nullKind___closed__2;
x_3790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3790, 0, x_3789);
lean_ctor_set(x_3790, 1, x_3788);
x_3791 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3792 = lean_array_push(x_3791, x_3790);
x_3793 = lean_array_push(x_3792, x_3784);
x_3794 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3795 = lean_array_push(x_3793, x_3794);
x_3796 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3797 = lean_array_push(x_3795, x_3796);
lean_inc(x_11);
x_3798 = lean_array_push(x_3782, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3799 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3799 = lean_box(0);
}
if (lean_is_scalar(x_3799)) {
 x_3800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3800 = x_3799;
}
lean_ctor_set(x_3800, 0, x_3789);
lean_ctor_set(x_3800, 1, x_3798);
x_3801 = lean_array_push(x_3782, x_3800);
x_3802 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3803 = lean_array_push(x_3801, x_3802);
x_3804 = lean_array_push(x_3803, x_3732);
x_3805 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3806, 0, x_3805);
lean_ctor_set(x_3806, 1, x_3804);
x_3807 = lean_array_push(x_3782, x_3806);
x_3808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3808, 0, x_3789);
lean_ctor_set(x_3808, 1, x_3807);
x_3809 = lean_array_push(x_3797, x_3808);
x_3810 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3811, 0, x_3810);
lean_ctor_set(x_3811, 1, x_3809);
lean_ctor_set(x_3729, 1, x_3811);
x_3812 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3812, 0, x_3729);
lean_ctor_set(x_3812, 1, x_3781);
return x_3812;
}
}
else
{
lean_object* x_3813; lean_object* x_3814; lean_object* x_3815; lean_object* x_3816; lean_object* x_3817; lean_object* x_3818; lean_object* x_3819; lean_object* x_3820; lean_object* x_3821; lean_object* x_3822; lean_object* x_3823; lean_object* x_3824; lean_object* x_3825; lean_object* x_3826; lean_object* x_3827; lean_object* x_3828; lean_object* x_3829; lean_object* x_3830; lean_object* x_3831; lean_object* x_3832; lean_object* x_3833; lean_object* x_3834; lean_object* x_3835; lean_object* x_3836; lean_object* x_3837; lean_object* x_3838; lean_object* x_3839; lean_object* x_3840; lean_object* x_3841; lean_object* x_3842; lean_object* x_3843; lean_object* x_3844; lean_object* x_3845; lean_object* x_3846; lean_object* x_3847; lean_object* x_3848; lean_object* x_3849; lean_object* x_3850; lean_object* x_3851; 
x_3813 = lean_ctor_get(x_3729, 0);
x_3814 = lean_ctor_get(x_3729, 1);
lean_inc(x_3814);
lean_inc(x_3813);
lean_dec(x_3729);
x_3815 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3730);
lean_dec(x_5);
x_3816 = lean_ctor_get(x_3815, 1);
lean_inc(x_3816);
lean_dec(x_3815);
x_3817 = l_Lean_Elab_Term_getMainModule___rarg(x_3816);
x_3818 = lean_ctor_get(x_3817, 1);
lean_inc(x_3818);
if (lean_is_exclusive(x_3817)) {
 lean_ctor_release(x_3817, 0);
 lean_ctor_release(x_3817, 1);
 x_3819 = x_3817;
} else {
 lean_dec_ref(x_3817);
 x_3819 = lean_box(0);
}
x_3820 = l_Array_empty___closed__1;
x_3821 = lean_array_push(x_3820, x_3721);
x_3822 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3823 = lean_array_push(x_3821, x_3822);
x_3824 = l_Lean_mkTermIdFromIdent___closed__2;
x_3825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3825, 0, x_3824);
lean_ctor_set(x_3825, 1, x_3823);
x_3826 = lean_array_push(x_3820, x_3825);
x_3827 = l_Lean_nullKind___closed__2;
x_3828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3828, 0, x_3827);
lean_ctor_set(x_3828, 1, x_3826);
x_3829 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3830 = lean_array_push(x_3829, x_3828);
x_3831 = lean_array_push(x_3830, x_3822);
x_3832 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3833 = lean_array_push(x_3831, x_3832);
x_3834 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3835 = lean_array_push(x_3833, x_3834);
lean_inc(x_11);
x_3836 = lean_array_push(x_3820, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3837 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3837 = lean_box(0);
}
if (lean_is_scalar(x_3837)) {
 x_3838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3838 = x_3837;
}
lean_ctor_set(x_3838, 0, x_3827);
lean_ctor_set(x_3838, 1, x_3836);
x_3839 = lean_array_push(x_3820, x_3838);
x_3840 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3841 = lean_array_push(x_3839, x_3840);
x_3842 = lean_array_push(x_3841, x_3814);
x_3843 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3844, 0, x_3843);
lean_ctor_set(x_3844, 1, x_3842);
x_3845 = lean_array_push(x_3820, x_3844);
x_3846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3846, 0, x_3827);
lean_ctor_set(x_3846, 1, x_3845);
x_3847 = lean_array_push(x_3835, x_3846);
x_3848 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3849, 0, x_3848);
lean_ctor_set(x_3849, 1, x_3847);
x_3850 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3850, 0, x_3813);
lean_ctor_set(x_3850, 1, x_3849);
if (lean_is_scalar(x_3819)) {
 x_3851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3851 = x_3819;
}
lean_ctor_set(x_3851, 0, x_3850);
lean_ctor_set(x_3851, 1, x_3818);
return x_3851;
}
}
else
{
uint8_t x_3852; 
lean_dec(x_3721);
lean_dec(x_11);
lean_dec(x_5);
x_3852 = !lean_is_exclusive(x_3728);
if (x_3852 == 0)
{
return x_3728;
}
else
{
lean_object* x_3853; lean_object* x_3854; lean_object* x_3855; 
x_3853 = lean_ctor_get(x_3728, 0);
x_3854 = lean_ctor_get(x_3728, 1);
lean_inc(x_3854);
lean_inc(x_3853);
lean_dec(x_3728);
x_3855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3855, 0, x_3853);
lean_ctor_set(x_3855, 1, x_3854);
return x_3855;
}
}
}
else
{
lean_object* x_3856; lean_object* x_3857; lean_object* x_3858; uint8_t x_3859; 
x_3856 = lean_ctor_get(x_3719, 0);
lean_inc(x_3856);
lean_dec(x_3719);
x_3857 = lean_ctor_get(x_3856, 0);
lean_inc(x_3857);
x_3858 = lean_ctor_get(x_3856, 1);
lean_inc(x_3858);
lean_dec(x_3856);
x_3859 = l_Lean_Syntax_isNone(x_3858);
lean_dec(x_3858);
if (x_3859 == 0)
{
lean_object* x_3860; lean_object* x_3861; uint8_t x_3862; 
lean_dec(x_3857);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3860 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_3861 = l_Lean_Elab_Term_throwError___rarg(x_11, x_3860, x_5, x_6);
lean_dec(x_11);
x_3862 = !lean_is_exclusive(x_3861);
if (x_3862 == 0)
{
return x_3861;
}
else
{
lean_object* x_3863; lean_object* x_3864; lean_object* x_3865; 
x_3863 = lean_ctor_get(x_3861, 0);
x_3864 = lean_ctor_get(x_3861, 1);
lean_inc(x_3864);
lean_inc(x_3863);
lean_dec(x_3861);
x_3865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3865, 0, x_3863);
lean_ctor_set(x_3865, 1, x_3864);
return x_3865;
}
}
else
{
lean_object* x_3866; lean_object* x_3867; lean_object* x_3868; lean_object* x_3869; lean_object* x_3870; 
x_3866 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_3867 = lean_unsigned_to_nat(1u);
x_3868 = lean_nat_add(x_3, x_3867);
lean_dec(x_3);
x_3869 = l_Lean_Elab_Term_mkExplicitBinder(x_3857, x_3866);
x_3870 = lean_array_push(x_4, x_3869);
x_3 = x_3868;
x_4 = x_3870;
goto _start;
}
}
}
}
else
{
uint8_t x_3872; lean_object* x_3873; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_3872 = 1;
lean_inc(x_11);
x_3873 = l_Lean_Syntax_isTermId_x3f(x_11, x_3872);
if (lean_obj_tag(x_3873) == 0)
{
lean_object* x_3874; lean_object* x_3875; lean_object* x_3876; lean_object* x_3877; lean_object* x_3878; lean_object* x_3879; lean_object* x_3880; lean_object* x_3881; lean_object* x_3882; 
x_3874 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_3875 = lean_ctor_get(x_3874, 0);
lean_inc(x_3875);
x_3876 = lean_ctor_get(x_3874, 1);
lean_inc(x_3876);
lean_dec(x_3874);
x_3877 = lean_unsigned_to_nat(1u);
x_3878 = lean_nat_add(x_3, x_3877);
lean_dec(x_3);
x_3879 = l_Lean_mkHole(x_11);
lean_inc(x_3875);
x_3880 = l_Lean_Elab_Term_mkExplicitBinder(x_3875, x_3879);
x_3881 = lean_array_push(x_4, x_3880);
lean_inc(x_5);
x_3882 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3878, x_3881, x_5, x_3876);
if (lean_obj_tag(x_3882) == 0)
{
lean_object* x_3883; lean_object* x_3884; uint8_t x_3885; 
x_3883 = lean_ctor_get(x_3882, 0);
lean_inc(x_3883);
x_3884 = lean_ctor_get(x_3882, 1);
lean_inc(x_3884);
lean_dec(x_3882);
x_3885 = !lean_is_exclusive(x_3883);
if (x_3885 == 0)
{
lean_object* x_3886; lean_object* x_3887; lean_object* x_3888; lean_object* x_3889; uint8_t x_3890; 
x_3886 = lean_ctor_get(x_3883, 1);
x_3887 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3884);
lean_dec(x_5);
x_3888 = lean_ctor_get(x_3887, 1);
lean_inc(x_3888);
lean_dec(x_3887);
x_3889 = l_Lean_Elab_Term_getMainModule___rarg(x_3888);
x_3890 = !lean_is_exclusive(x_3889);
if (x_3890 == 0)
{
lean_object* x_3891; lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; lean_object* x_3896; lean_object* x_3897; lean_object* x_3898; lean_object* x_3899; lean_object* x_3900; lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; lean_object* x_3904; lean_object* x_3905; lean_object* x_3906; lean_object* x_3907; lean_object* x_3908; uint8_t x_3909; 
x_3891 = lean_ctor_get(x_3889, 0);
lean_dec(x_3891);
x_3892 = l_Array_empty___closed__1;
x_3893 = lean_array_push(x_3892, x_3875);
x_3894 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3895 = lean_array_push(x_3893, x_3894);
x_3896 = l_Lean_mkTermIdFromIdent___closed__2;
x_3897 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3897, 0, x_3896);
lean_ctor_set(x_3897, 1, x_3895);
x_3898 = lean_array_push(x_3892, x_3897);
x_3899 = l_Lean_nullKind___closed__2;
x_3900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3900, 0, x_3899);
lean_ctor_set(x_3900, 1, x_3898);
x_3901 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3902 = lean_array_push(x_3901, x_3900);
x_3903 = lean_array_push(x_3902, x_3894);
x_3904 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3905 = lean_array_push(x_3903, x_3904);
x_3906 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3907 = lean_array_push(x_3905, x_3906);
lean_inc(x_11);
x_3908 = lean_array_push(x_3892, x_11);
x_3909 = !lean_is_exclusive(x_11);
if (x_3909 == 0)
{
lean_object* x_3910; lean_object* x_3911; lean_object* x_3912; lean_object* x_3913; lean_object* x_3914; lean_object* x_3915; lean_object* x_3916; lean_object* x_3917; lean_object* x_3918; lean_object* x_3919; lean_object* x_3920; lean_object* x_3921; lean_object* x_3922; 
x_3910 = lean_ctor_get(x_11, 1);
lean_dec(x_3910);
x_3911 = lean_ctor_get(x_11, 0);
lean_dec(x_3911);
lean_ctor_set(x_11, 1, x_3908);
lean_ctor_set(x_11, 0, x_3899);
x_3912 = lean_array_push(x_3892, x_11);
x_3913 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3914 = lean_array_push(x_3912, x_3913);
x_3915 = lean_array_push(x_3914, x_3886);
x_3916 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3917, 0, x_3916);
lean_ctor_set(x_3917, 1, x_3915);
x_3918 = lean_array_push(x_3892, x_3917);
x_3919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3919, 0, x_3899);
lean_ctor_set(x_3919, 1, x_3918);
x_3920 = lean_array_push(x_3907, x_3919);
x_3921 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3922, 0, x_3921);
lean_ctor_set(x_3922, 1, x_3920);
lean_ctor_set(x_3883, 1, x_3922);
lean_ctor_set(x_3889, 0, x_3883);
return x_3889;
}
else
{
lean_object* x_3923; lean_object* x_3924; lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; lean_object* x_3928; lean_object* x_3929; lean_object* x_3930; lean_object* x_3931; lean_object* x_3932; lean_object* x_3933; lean_object* x_3934; 
lean_dec(x_11);
x_3923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3923, 0, x_3899);
lean_ctor_set(x_3923, 1, x_3908);
x_3924 = lean_array_push(x_3892, x_3923);
x_3925 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3926 = lean_array_push(x_3924, x_3925);
x_3927 = lean_array_push(x_3926, x_3886);
x_3928 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3929, 0, x_3928);
lean_ctor_set(x_3929, 1, x_3927);
x_3930 = lean_array_push(x_3892, x_3929);
x_3931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3931, 0, x_3899);
lean_ctor_set(x_3931, 1, x_3930);
x_3932 = lean_array_push(x_3907, x_3931);
x_3933 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3934 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3934, 0, x_3933);
lean_ctor_set(x_3934, 1, x_3932);
lean_ctor_set(x_3883, 1, x_3934);
lean_ctor_set(x_3889, 0, x_3883);
return x_3889;
}
}
else
{
lean_object* x_3935; lean_object* x_3936; lean_object* x_3937; lean_object* x_3938; lean_object* x_3939; lean_object* x_3940; lean_object* x_3941; lean_object* x_3942; lean_object* x_3943; lean_object* x_3944; lean_object* x_3945; lean_object* x_3946; lean_object* x_3947; lean_object* x_3948; lean_object* x_3949; lean_object* x_3950; lean_object* x_3951; lean_object* x_3952; lean_object* x_3953; lean_object* x_3954; lean_object* x_3955; lean_object* x_3956; lean_object* x_3957; lean_object* x_3958; lean_object* x_3959; lean_object* x_3960; lean_object* x_3961; lean_object* x_3962; lean_object* x_3963; lean_object* x_3964; lean_object* x_3965; lean_object* x_3966; 
x_3935 = lean_ctor_get(x_3889, 1);
lean_inc(x_3935);
lean_dec(x_3889);
x_3936 = l_Array_empty___closed__1;
x_3937 = lean_array_push(x_3936, x_3875);
x_3938 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3939 = lean_array_push(x_3937, x_3938);
x_3940 = l_Lean_mkTermIdFromIdent___closed__2;
x_3941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3941, 0, x_3940);
lean_ctor_set(x_3941, 1, x_3939);
x_3942 = lean_array_push(x_3936, x_3941);
x_3943 = l_Lean_nullKind___closed__2;
x_3944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3944, 0, x_3943);
lean_ctor_set(x_3944, 1, x_3942);
x_3945 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3946 = lean_array_push(x_3945, x_3944);
x_3947 = lean_array_push(x_3946, x_3938);
x_3948 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3949 = lean_array_push(x_3947, x_3948);
x_3950 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3951 = lean_array_push(x_3949, x_3950);
lean_inc(x_11);
x_3952 = lean_array_push(x_3936, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3953 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3953 = lean_box(0);
}
if (lean_is_scalar(x_3953)) {
 x_3954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3954 = x_3953;
}
lean_ctor_set(x_3954, 0, x_3943);
lean_ctor_set(x_3954, 1, x_3952);
x_3955 = lean_array_push(x_3936, x_3954);
x_3956 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3957 = lean_array_push(x_3955, x_3956);
x_3958 = lean_array_push(x_3957, x_3886);
x_3959 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3960, 0, x_3959);
lean_ctor_set(x_3960, 1, x_3958);
x_3961 = lean_array_push(x_3936, x_3960);
x_3962 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3962, 0, x_3943);
lean_ctor_set(x_3962, 1, x_3961);
x_3963 = lean_array_push(x_3951, x_3962);
x_3964 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3965, 0, x_3964);
lean_ctor_set(x_3965, 1, x_3963);
lean_ctor_set(x_3883, 1, x_3965);
x_3966 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3966, 0, x_3883);
lean_ctor_set(x_3966, 1, x_3935);
return x_3966;
}
}
else
{
lean_object* x_3967; lean_object* x_3968; lean_object* x_3969; lean_object* x_3970; lean_object* x_3971; lean_object* x_3972; lean_object* x_3973; lean_object* x_3974; lean_object* x_3975; lean_object* x_3976; lean_object* x_3977; lean_object* x_3978; lean_object* x_3979; lean_object* x_3980; lean_object* x_3981; lean_object* x_3982; lean_object* x_3983; lean_object* x_3984; lean_object* x_3985; lean_object* x_3986; lean_object* x_3987; lean_object* x_3988; lean_object* x_3989; lean_object* x_3990; lean_object* x_3991; lean_object* x_3992; lean_object* x_3993; lean_object* x_3994; lean_object* x_3995; lean_object* x_3996; lean_object* x_3997; lean_object* x_3998; lean_object* x_3999; lean_object* x_4000; lean_object* x_4001; lean_object* x_4002; lean_object* x_4003; lean_object* x_4004; lean_object* x_4005; 
x_3967 = lean_ctor_get(x_3883, 0);
x_3968 = lean_ctor_get(x_3883, 1);
lean_inc(x_3968);
lean_inc(x_3967);
lean_dec(x_3883);
x_3969 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3884);
lean_dec(x_5);
x_3970 = lean_ctor_get(x_3969, 1);
lean_inc(x_3970);
lean_dec(x_3969);
x_3971 = l_Lean_Elab_Term_getMainModule___rarg(x_3970);
x_3972 = lean_ctor_get(x_3971, 1);
lean_inc(x_3972);
if (lean_is_exclusive(x_3971)) {
 lean_ctor_release(x_3971, 0);
 lean_ctor_release(x_3971, 1);
 x_3973 = x_3971;
} else {
 lean_dec_ref(x_3971);
 x_3973 = lean_box(0);
}
x_3974 = l_Array_empty___closed__1;
x_3975 = lean_array_push(x_3974, x_3875);
x_3976 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3977 = lean_array_push(x_3975, x_3976);
x_3978 = l_Lean_mkTermIdFromIdent___closed__2;
x_3979 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3979, 0, x_3978);
lean_ctor_set(x_3979, 1, x_3977);
x_3980 = lean_array_push(x_3974, x_3979);
x_3981 = l_Lean_nullKind___closed__2;
x_3982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3982, 0, x_3981);
lean_ctor_set(x_3982, 1, x_3980);
x_3983 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_3984 = lean_array_push(x_3983, x_3982);
x_3985 = lean_array_push(x_3984, x_3976);
x_3986 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_3987 = lean_array_push(x_3985, x_3986);
x_3988 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_3989 = lean_array_push(x_3987, x_3988);
lean_inc(x_11);
x_3990 = lean_array_push(x_3974, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_3991 = x_11;
} else {
 lean_dec_ref(x_11);
 x_3991 = lean_box(0);
}
if (lean_is_scalar(x_3991)) {
 x_3992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3992 = x_3991;
}
lean_ctor_set(x_3992, 0, x_3981);
lean_ctor_set(x_3992, 1, x_3990);
x_3993 = lean_array_push(x_3974, x_3992);
x_3994 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3995 = lean_array_push(x_3993, x_3994);
x_3996 = lean_array_push(x_3995, x_3968);
x_3997 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3998, 0, x_3997);
lean_ctor_set(x_3998, 1, x_3996);
x_3999 = lean_array_push(x_3974, x_3998);
x_4000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4000, 0, x_3981);
lean_ctor_set(x_4000, 1, x_3999);
x_4001 = lean_array_push(x_3989, x_4000);
x_4002 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4003 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4003, 0, x_4002);
lean_ctor_set(x_4003, 1, x_4001);
x_4004 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4004, 0, x_3967);
lean_ctor_set(x_4004, 1, x_4003);
if (lean_is_scalar(x_3973)) {
 x_4005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4005 = x_3973;
}
lean_ctor_set(x_4005, 0, x_4004);
lean_ctor_set(x_4005, 1, x_3972);
return x_4005;
}
}
else
{
uint8_t x_4006; 
lean_dec(x_3875);
lean_dec(x_11);
lean_dec(x_5);
x_4006 = !lean_is_exclusive(x_3882);
if (x_4006 == 0)
{
return x_3882;
}
else
{
lean_object* x_4007; lean_object* x_4008; lean_object* x_4009; 
x_4007 = lean_ctor_get(x_3882, 0);
x_4008 = lean_ctor_get(x_3882, 1);
lean_inc(x_4008);
lean_inc(x_4007);
lean_dec(x_3882);
x_4009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4009, 0, x_4007);
lean_ctor_set(x_4009, 1, x_4008);
return x_4009;
}
}
}
else
{
lean_object* x_4010; lean_object* x_4011; lean_object* x_4012; uint8_t x_4013; 
x_4010 = lean_ctor_get(x_3873, 0);
lean_inc(x_4010);
lean_dec(x_3873);
x_4011 = lean_ctor_get(x_4010, 0);
lean_inc(x_4011);
x_4012 = lean_ctor_get(x_4010, 1);
lean_inc(x_4012);
lean_dec(x_4010);
x_4013 = l_Lean_Syntax_isNone(x_4012);
lean_dec(x_4012);
if (x_4013 == 0)
{
lean_object* x_4014; lean_object* x_4015; uint8_t x_4016; 
lean_dec(x_4011);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4014 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_4015 = l_Lean_Elab_Term_throwError___rarg(x_11, x_4014, x_5, x_6);
lean_dec(x_11);
x_4016 = !lean_is_exclusive(x_4015);
if (x_4016 == 0)
{
return x_4015;
}
else
{
lean_object* x_4017; lean_object* x_4018; lean_object* x_4019; 
x_4017 = lean_ctor_get(x_4015, 0);
x_4018 = lean_ctor_get(x_4015, 1);
lean_inc(x_4018);
lean_inc(x_4017);
lean_dec(x_4015);
x_4019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4019, 0, x_4017);
lean_ctor_set(x_4019, 1, x_4018);
return x_4019;
}
}
else
{
lean_object* x_4020; lean_object* x_4021; lean_object* x_4022; lean_object* x_4023; lean_object* x_4024; 
x_4020 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_4021 = lean_unsigned_to_nat(1u);
x_4022 = lean_nat_add(x_3, x_4021);
lean_dec(x_3);
x_4023 = l_Lean_Elab_Term_mkExplicitBinder(x_4011, x_4020);
x_4024 = lean_array_push(x_4, x_4023);
x_3 = x_4022;
x_4 = x_4024;
goto _start;
}
}
}
}
else
{
uint8_t x_4026; lean_object* x_4027; 
lean_dec(x_13);
lean_dec(x_12);
x_4026 = 1;
lean_inc(x_11);
x_4027 = l_Lean_Syntax_isTermId_x3f(x_11, x_4026);
if (lean_obj_tag(x_4027) == 0)
{
lean_object* x_4028; lean_object* x_4029; lean_object* x_4030; lean_object* x_4031; lean_object* x_4032; lean_object* x_4033; lean_object* x_4034; lean_object* x_4035; lean_object* x_4036; 
x_4028 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_4029 = lean_ctor_get(x_4028, 0);
lean_inc(x_4029);
x_4030 = lean_ctor_get(x_4028, 1);
lean_inc(x_4030);
lean_dec(x_4028);
x_4031 = lean_unsigned_to_nat(1u);
x_4032 = lean_nat_add(x_3, x_4031);
lean_dec(x_3);
x_4033 = l_Lean_mkHole(x_11);
lean_inc(x_4029);
x_4034 = l_Lean_Elab_Term_mkExplicitBinder(x_4029, x_4033);
x_4035 = lean_array_push(x_4, x_4034);
lean_inc(x_5);
x_4036 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_4032, x_4035, x_5, x_4030);
if (lean_obj_tag(x_4036) == 0)
{
lean_object* x_4037; lean_object* x_4038; uint8_t x_4039; 
x_4037 = lean_ctor_get(x_4036, 0);
lean_inc(x_4037);
x_4038 = lean_ctor_get(x_4036, 1);
lean_inc(x_4038);
lean_dec(x_4036);
x_4039 = !lean_is_exclusive(x_4037);
if (x_4039 == 0)
{
lean_object* x_4040; lean_object* x_4041; lean_object* x_4042; lean_object* x_4043; uint8_t x_4044; 
x_4040 = lean_ctor_get(x_4037, 1);
x_4041 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4038);
lean_dec(x_5);
x_4042 = lean_ctor_get(x_4041, 1);
lean_inc(x_4042);
lean_dec(x_4041);
x_4043 = l_Lean_Elab_Term_getMainModule___rarg(x_4042);
x_4044 = !lean_is_exclusive(x_4043);
if (x_4044 == 0)
{
lean_object* x_4045; lean_object* x_4046; lean_object* x_4047; lean_object* x_4048; lean_object* x_4049; lean_object* x_4050; lean_object* x_4051; lean_object* x_4052; lean_object* x_4053; lean_object* x_4054; lean_object* x_4055; lean_object* x_4056; lean_object* x_4057; lean_object* x_4058; lean_object* x_4059; lean_object* x_4060; lean_object* x_4061; lean_object* x_4062; uint8_t x_4063; 
x_4045 = lean_ctor_get(x_4043, 0);
lean_dec(x_4045);
x_4046 = l_Array_empty___closed__1;
x_4047 = lean_array_push(x_4046, x_4029);
x_4048 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4049 = lean_array_push(x_4047, x_4048);
x_4050 = l_Lean_mkTermIdFromIdent___closed__2;
x_4051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4051, 0, x_4050);
lean_ctor_set(x_4051, 1, x_4049);
x_4052 = lean_array_push(x_4046, x_4051);
x_4053 = l_Lean_nullKind___closed__2;
x_4054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4054, 0, x_4053);
lean_ctor_set(x_4054, 1, x_4052);
x_4055 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4056 = lean_array_push(x_4055, x_4054);
x_4057 = lean_array_push(x_4056, x_4048);
x_4058 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4059 = lean_array_push(x_4057, x_4058);
x_4060 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4061 = lean_array_push(x_4059, x_4060);
lean_inc(x_11);
x_4062 = lean_array_push(x_4046, x_11);
x_4063 = !lean_is_exclusive(x_11);
if (x_4063 == 0)
{
lean_object* x_4064; lean_object* x_4065; lean_object* x_4066; lean_object* x_4067; lean_object* x_4068; lean_object* x_4069; lean_object* x_4070; lean_object* x_4071; lean_object* x_4072; lean_object* x_4073; lean_object* x_4074; lean_object* x_4075; lean_object* x_4076; 
x_4064 = lean_ctor_get(x_11, 1);
lean_dec(x_4064);
x_4065 = lean_ctor_get(x_11, 0);
lean_dec(x_4065);
lean_ctor_set(x_11, 1, x_4062);
lean_ctor_set(x_11, 0, x_4053);
x_4066 = lean_array_push(x_4046, x_11);
x_4067 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4068 = lean_array_push(x_4066, x_4067);
x_4069 = lean_array_push(x_4068, x_4040);
x_4070 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4071 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4071, 0, x_4070);
lean_ctor_set(x_4071, 1, x_4069);
x_4072 = lean_array_push(x_4046, x_4071);
x_4073 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4073, 0, x_4053);
lean_ctor_set(x_4073, 1, x_4072);
x_4074 = lean_array_push(x_4061, x_4073);
x_4075 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4076 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4076, 0, x_4075);
lean_ctor_set(x_4076, 1, x_4074);
lean_ctor_set(x_4037, 1, x_4076);
lean_ctor_set(x_4043, 0, x_4037);
return x_4043;
}
else
{
lean_object* x_4077; lean_object* x_4078; lean_object* x_4079; lean_object* x_4080; lean_object* x_4081; lean_object* x_4082; lean_object* x_4083; lean_object* x_4084; lean_object* x_4085; lean_object* x_4086; lean_object* x_4087; lean_object* x_4088; 
lean_dec(x_11);
x_4077 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4077, 0, x_4053);
lean_ctor_set(x_4077, 1, x_4062);
x_4078 = lean_array_push(x_4046, x_4077);
x_4079 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4080 = lean_array_push(x_4078, x_4079);
x_4081 = lean_array_push(x_4080, x_4040);
x_4082 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4083, 0, x_4082);
lean_ctor_set(x_4083, 1, x_4081);
x_4084 = lean_array_push(x_4046, x_4083);
x_4085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4085, 0, x_4053);
lean_ctor_set(x_4085, 1, x_4084);
x_4086 = lean_array_push(x_4061, x_4085);
x_4087 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4088 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4088, 0, x_4087);
lean_ctor_set(x_4088, 1, x_4086);
lean_ctor_set(x_4037, 1, x_4088);
lean_ctor_set(x_4043, 0, x_4037);
return x_4043;
}
}
else
{
lean_object* x_4089; lean_object* x_4090; lean_object* x_4091; lean_object* x_4092; lean_object* x_4093; lean_object* x_4094; lean_object* x_4095; lean_object* x_4096; lean_object* x_4097; lean_object* x_4098; lean_object* x_4099; lean_object* x_4100; lean_object* x_4101; lean_object* x_4102; lean_object* x_4103; lean_object* x_4104; lean_object* x_4105; lean_object* x_4106; lean_object* x_4107; lean_object* x_4108; lean_object* x_4109; lean_object* x_4110; lean_object* x_4111; lean_object* x_4112; lean_object* x_4113; lean_object* x_4114; lean_object* x_4115; lean_object* x_4116; lean_object* x_4117; lean_object* x_4118; lean_object* x_4119; lean_object* x_4120; 
x_4089 = lean_ctor_get(x_4043, 1);
lean_inc(x_4089);
lean_dec(x_4043);
x_4090 = l_Array_empty___closed__1;
x_4091 = lean_array_push(x_4090, x_4029);
x_4092 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4093 = lean_array_push(x_4091, x_4092);
x_4094 = l_Lean_mkTermIdFromIdent___closed__2;
x_4095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4095, 0, x_4094);
lean_ctor_set(x_4095, 1, x_4093);
x_4096 = lean_array_push(x_4090, x_4095);
x_4097 = l_Lean_nullKind___closed__2;
x_4098 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4098, 0, x_4097);
lean_ctor_set(x_4098, 1, x_4096);
x_4099 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4100 = lean_array_push(x_4099, x_4098);
x_4101 = lean_array_push(x_4100, x_4092);
x_4102 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4103 = lean_array_push(x_4101, x_4102);
x_4104 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4105 = lean_array_push(x_4103, x_4104);
lean_inc(x_11);
x_4106 = lean_array_push(x_4090, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_4107 = x_11;
} else {
 lean_dec_ref(x_11);
 x_4107 = lean_box(0);
}
if (lean_is_scalar(x_4107)) {
 x_4108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4108 = x_4107;
}
lean_ctor_set(x_4108, 0, x_4097);
lean_ctor_set(x_4108, 1, x_4106);
x_4109 = lean_array_push(x_4090, x_4108);
x_4110 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4111 = lean_array_push(x_4109, x_4110);
x_4112 = lean_array_push(x_4111, x_4040);
x_4113 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4114, 0, x_4113);
lean_ctor_set(x_4114, 1, x_4112);
x_4115 = lean_array_push(x_4090, x_4114);
x_4116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4116, 0, x_4097);
lean_ctor_set(x_4116, 1, x_4115);
x_4117 = lean_array_push(x_4105, x_4116);
x_4118 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4119, 0, x_4118);
lean_ctor_set(x_4119, 1, x_4117);
lean_ctor_set(x_4037, 1, x_4119);
x_4120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4120, 0, x_4037);
lean_ctor_set(x_4120, 1, x_4089);
return x_4120;
}
}
else
{
lean_object* x_4121; lean_object* x_4122; lean_object* x_4123; lean_object* x_4124; lean_object* x_4125; lean_object* x_4126; lean_object* x_4127; lean_object* x_4128; lean_object* x_4129; lean_object* x_4130; lean_object* x_4131; lean_object* x_4132; lean_object* x_4133; lean_object* x_4134; lean_object* x_4135; lean_object* x_4136; lean_object* x_4137; lean_object* x_4138; lean_object* x_4139; lean_object* x_4140; lean_object* x_4141; lean_object* x_4142; lean_object* x_4143; lean_object* x_4144; lean_object* x_4145; lean_object* x_4146; lean_object* x_4147; lean_object* x_4148; lean_object* x_4149; lean_object* x_4150; lean_object* x_4151; lean_object* x_4152; lean_object* x_4153; lean_object* x_4154; lean_object* x_4155; lean_object* x_4156; lean_object* x_4157; lean_object* x_4158; lean_object* x_4159; 
x_4121 = lean_ctor_get(x_4037, 0);
x_4122 = lean_ctor_get(x_4037, 1);
lean_inc(x_4122);
lean_inc(x_4121);
lean_dec(x_4037);
x_4123 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4038);
lean_dec(x_5);
x_4124 = lean_ctor_get(x_4123, 1);
lean_inc(x_4124);
lean_dec(x_4123);
x_4125 = l_Lean_Elab_Term_getMainModule___rarg(x_4124);
x_4126 = lean_ctor_get(x_4125, 1);
lean_inc(x_4126);
if (lean_is_exclusive(x_4125)) {
 lean_ctor_release(x_4125, 0);
 lean_ctor_release(x_4125, 1);
 x_4127 = x_4125;
} else {
 lean_dec_ref(x_4125);
 x_4127 = lean_box(0);
}
x_4128 = l_Array_empty___closed__1;
x_4129 = lean_array_push(x_4128, x_4029);
x_4130 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4131 = lean_array_push(x_4129, x_4130);
x_4132 = l_Lean_mkTermIdFromIdent___closed__2;
x_4133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4133, 0, x_4132);
lean_ctor_set(x_4133, 1, x_4131);
x_4134 = lean_array_push(x_4128, x_4133);
x_4135 = l_Lean_nullKind___closed__2;
x_4136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4136, 0, x_4135);
lean_ctor_set(x_4136, 1, x_4134);
x_4137 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4138 = lean_array_push(x_4137, x_4136);
x_4139 = lean_array_push(x_4138, x_4130);
x_4140 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4141 = lean_array_push(x_4139, x_4140);
x_4142 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4143 = lean_array_push(x_4141, x_4142);
lean_inc(x_11);
x_4144 = lean_array_push(x_4128, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_4145 = x_11;
} else {
 lean_dec_ref(x_11);
 x_4145 = lean_box(0);
}
if (lean_is_scalar(x_4145)) {
 x_4146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4146 = x_4145;
}
lean_ctor_set(x_4146, 0, x_4135);
lean_ctor_set(x_4146, 1, x_4144);
x_4147 = lean_array_push(x_4128, x_4146);
x_4148 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4149 = lean_array_push(x_4147, x_4148);
x_4150 = lean_array_push(x_4149, x_4122);
x_4151 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4152, 0, x_4151);
lean_ctor_set(x_4152, 1, x_4150);
x_4153 = lean_array_push(x_4128, x_4152);
x_4154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4154, 0, x_4135);
lean_ctor_set(x_4154, 1, x_4153);
x_4155 = lean_array_push(x_4143, x_4154);
x_4156 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4157, 0, x_4156);
lean_ctor_set(x_4157, 1, x_4155);
x_4158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4158, 0, x_4121);
lean_ctor_set(x_4158, 1, x_4157);
if (lean_is_scalar(x_4127)) {
 x_4159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4159 = x_4127;
}
lean_ctor_set(x_4159, 0, x_4158);
lean_ctor_set(x_4159, 1, x_4126);
return x_4159;
}
}
else
{
uint8_t x_4160; 
lean_dec(x_4029);
lean_dec(x_11);
lean_dec(x_5);
x_4160 = !lean_is_exclusive(x_4036);
if (x_4160 == 0)
{
return x_4036;
}
else
{
lean_object* x_4161; lean_object* x_4162; lean_object* x_4163; 
x_4161 = lean_ctor_get(x_4036, 0);
x_4162 = lean_ctor_get(x_4036, 1);
lean_inc(x_4162);
lean_inc(x_4161);
lean_dec(x_4036);
x_4163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4163, 0, x_4161);
lean_ctor_set(x_4163, 1, x_4162);
return x_4163;
}
}
}
else
{
lean_object* x_4164; lean_object* x_4165; lean_object* x_4166; uint8_t x_4167; 
x_4164 = lean_ctor_get(x_4027, 0);
lean_inc(x_4164);
lean_dec(x_4027);
x_4165 = lean_ctor_get(x_4164, 0);
lean_inc(x_4165);
x_4166 = lean_ctor_get(x_4164, 1);
lean_inc(x_4166);
lean_dec(x_4164);
x_4167 = l_Lean_Syntax_isNone(x_4166);
lean_dec(x_4166);
if (x_4167 == 0)
{
lean_object* x_4168; lean_object* x_4169; uint8_t x_4170; 
lean_dec(x_4165);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4168 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_4169 = l_Lean_Elab_Term_throwError___rarg(x_11, x_4168, x_5, x_6);
lean_dec(x_11);
x_4170 = !lean_is_exclusive(x_4169);
if (x_4170 == 0)
{
return x_4169;
}
else
{
lean_object* x_4171; lean_object* x_4172; lean_object* x_4173; 
x_4171 = lean_ctor_get(x_4169, 0);
x_4172 = lean_ctor_get(x_4169, 1);
lean_inc(x_4172);
lean_inc(x_4171);
lean_dec(x_4169);
x_4173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4173, 0, x_4171);
lean_ctor_set(x_4173, 1, x_4172);
return x_4173;
}
}
else
{
lean_object* x_4174; lean_object* x_4175; lean_object* x_4176; lean_object* x_4177; lean_object* x_4178; 
x_4174 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_4175 = lean_unsigned_to_nat(1u);
x_4176 = lean_nat_add(x_3, x_4175);
lean_dec(x_3);
x_4177 = l_Lean_Elab_Term_mkExplicitBinder(x_4165, x_4174);
x_4178 = lean_array_push(x_4, x_4177);
x_3 = x_4176;
x_4 = x_4178;
goto _start;
}
}
}
}
else
{
uint8_t x_4180; lean_object* x_4181; 
lean_dec(x_12);
x_4180 = 1;
lean_inc(x_11);
x_4181 = l_Lean_Syntax_isTermId_x3f(x_11, x_4180);
if (lean_obj_tag(x_4181) == 0)
{
lean_object* x_4182; lean_object* x_4183; lean_object* x_4184; lean_object* x_4185; lean_object* x_4186; lean_object* x_4187; lean_object* x_4188; lean_object* x_4189; lean_object* x_4190; 
x_4182 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_4183 = lean_ctor_get(x_4182, 0);
lean_inc(x_4183);
x_4184 = lean_ctor_get(x_4182, 1);
lean_inc(x_4184);
lean_dec(x_4182);
x_4185 = lean_unsigned_to_nat(1u);
x_4186 = lean_nat_add(x_3, x_4185);
lean_dec(x_3);
x_4187 = l_Lean_mkHole(x_11);
lean_inc(x_4183);
x_4188 = l_Lean_Elab_Term_mkExplicitBinder(x_4183, x_4187);
x_4189 = lean_array_push(x_4, x_4188);
lean_inc(x_5);
x_4190 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_4186, x_4189, x_5, x_4184);
if (lean_obj_tag(x_4190) == 0)
{
lean_object* x_4191; lean_object* x_4192; uint8_t x_4193; 
x_4191 = lean_ctor_get(x_4190, 0);
lean_inc(x_4191);
x_4192 = lean_ctor_get(x_4190, 1);
lean_inc(x_4192);
lean_dec(x_4190);
x_4193 = !lean_is_exclusive(x_4191);
if (x_4193 == 0)
{
lean_object* x_4194; lean_object* x_4195; lean_object* x_4196; lean_object* x_4197; uint8_t x_4198; 
x_4194 = lean_ctor_get(x_4191, 1);
x_4195 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4192);
lean_dec(x_5);
x_4196 = lean_ctor_get(x_4195, 1);
lean_inc(x_4196);
lean_dec(x_4195);
x_4197 = l_Lean_Elab_Term_getMainModule___rarg(x_4196);
x_4198 = !lean_is_exclusive(x_4197);
if (x_4198 == 0)
{
lean_object* x_4199; lean_object* x_4200; lean_object* x_4201; lean_object* x_4202; lean_object* x_4203; lean_object* x_4204; lean_object* x_4205; lean_object* x_4206; lean_object* x_4207; lean_object* x_4208; lean_object* x_4209; lean_object* x_4210; lean_object* x_4211; lean_object* x_4212; lean_object* x_4213; lean_object* x_4214; lean_object* x_4215; lean_object* x_4216; uint8_t x_4217; 
x_4199 = lean_ctor_get(x_4197, 0);
lean_dec(x_4199);
x_4200 = l_Array_empty___closed__1;
x_4201 = lean_array_push(x_4200, x_4183);
x_4202 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4203 = lean_array_push(x_4201, x_4202);
x_4204 = l_Lean_mkTermIdFromIdent___closed__2;
x_4205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4205, 0, x_4204);
lean_ctor_set(x_4205, 1, x_4203);
x_4206 = lean_array_push(x_4200, x_4205);
x_4207 = l_Lean_nullKind___closed__2;
x_4208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4208, 0, x_4207);
lean_ctor_set(x_4208, 1, x_4206);
x_4209 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4210 = lean_array_push(x_4209, x_4208);
x_4211 = lean_array_push(x_4210, x_4202);
x_4212 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4213 = lean_array_push(x_4211, x_4212);
x_4214 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4215 = lean_array_push(x_4213, x_4214);
lean_inc(x_11);
x_4216 = lean_array_push(x_4200, x_11);
x_4217 = !lean_is_exclusive(x_11);
if (x_4217 == 0)
{
lean_object* x_4218; lean_object* x_4219; lean_object* x_4220; lean_object* x_4221; lean_object* x_4222; lean_object* x_4223; lean_object* x_4224; lean_object* x_4225; lean_object* x_4226; lean_object* x_4227; lean_object* x_4228; lean_object* x_4229; lean_object* x_4230; 
x_4218 = lean_ctor_get(x_11, 1);
lean_dec(x_4218);
x_4219 = lean_ctor_get(x_11, 0);
lean_dec(x_4219);
lean_ctor_set(x_11, 1, x_4216);
lean_ctor_set(x_11, 0, x_4207);
x_4220 = lean_array_push(x_4200, x_11);
x_4221 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4222 = lean_array_push(x_4220, x_4221);
x_4223 = lean_array_push(x_4222, x_4194);
x_4224 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4225, 0, x_4224);
lean_ctor_set(x_4225, 1, x_4223);
x_4226 = lean_array_push(x_4200, x_4225);
x_4227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4227, 0, x_4207);
lean_ctor_set(x_4227, 1, x_4226);
x_4228 = lean_array_push(x_4215, x_4227);
x_4229 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4230, 0, x_4229);
lean_ctor_set(x_4230, 1, x_4228);
lean_ctor_set(x_4191, 1, x_4230);
lean_ctor_set(x_4197, 0, x_4191);
return x_4197;
}
else
{
lean_object* x_4231; lean_object* x_4232; lean_object* x_4233; lean_object* x_4234; lean_object* x_4235; lean_object* x_4236; lean_object* x_4237; lean_object* x_4238; lean_object* x_4239; lean_object* x_4240; lean_object* x_4241; lean_object* x_4242; 
lean_dec(x_11);
x_4231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4231, 0, x_4207);
lean_ctor_set(x_4231, 1, x_4216);
x_4232 = lean_array_push(x_4200, x_4231);
x_4233 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4234 = lean_array_push(x_4232, x_4233);
x_4235 = lean_array_push(x_4234, x_4194);
x_4236 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4237, 0, x_4236);
lean_ctor_set(x_4237, 1, x_4235);
x_4238 = lean_array_push(x_4200, x_4237);
x_4239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4239, 0, x_4207);
lean_ctor_set(x_4239, 1, x_4238);
x_4240 = lean_array_push(x_4215, x_4239);
x_4241 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4242, 0, x_4241);
lean_ctor_set(x_4242, 1, x_4240);
lean_ctor_set(x_4191, 1, x_4242);
lean_ctor_set(x_4197, 0, x_4191);
return x_4197;
}
}
else
{
lean_object* x_4243; lean_object* x_4244; lean_object* x_4245; lean_object* x_4246; lean_object* x_4247; lean_object* x_4248; lean_object* x_4249; lean_object* x_4250; lean_object* x_4251; lean_object* x_4252; lean_object* x_4253; lean_object* x_4254; lean_object* x_4255; lean_object* x_4256; lean_object* x_4257; lean_object* x_4258; lean_object* x_4259; lean_object* x_4260; lean_object* x_4261; lean_object* x_4262; lean_object* x_4263; lean_object* x_4264; lean_object* x_4265; lean_object* x_4266; lean_object* x_4267; lean_object* x_4268; lean_object* x_4269; lean_object* x_4270; lean_object* x_4271; lean_object* x_4272; lean_object* x_4273; lean_object* x_4274; 
x_4243 = lean_ctor_get(x_4197, 1);
lean_inc(x_4243);
lean_dec(x_4197);
x_4244 = l_Array_empty___closed__1;
x_4245 = lean_array_push(x_4244, x_4183);
x_4246 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4247 = lean_array_push(x_4245, x_4246);
x_4248 = l_Lean_mkTermIdFromIdent___closed__2;
x_4249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4249, 0, x_4248);
lean_ctor_set(x_4249, 1, x_4247);
x_4250 = lean_array_push(x_4244, x_4249);
x_4251 = l_Lean_nullKind___closed__2;
x_4252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4252, 0, x_4251);
lean_ctor_set(x_4252, 1, x_4250);
x_4253 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4254 = lean_array_push(x_4253, x_4252);
x_4255 = lean_array_push(x_4254, x_4246);
x_4256 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4257 = lean_array_push(x_4255, x_4256);
x_4258 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4259 = lean_array_push(x_4257, x_4258);
lean_inc(x_11);
x_4260 = lean_array_push(x_4244, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_4261 = x_11;
} else {
 lean_dec_ref(x_11);
 x_4261 = lean_box(0);
}
if (lean_is_scalar(x_4261)) {
 x_4262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4262 = x_4261;
}
lean_ctor_set(x_4262, 0, x_4251);
lean_ctor_set(x_4262, 1, x_4260);
x_4263 = lean_array_push(x_4244, x_4262);
x_4264 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4265 = lean_array_push(x_4263, x_4264);
x_4266 = lean_array_push(x_4265, x_4194);
x_4267 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4268, 0, x_4267);
lean_ctor_set(x_4268, 1, x_4266);
x_4269 = lean_array_push(x_4244, x_4268);
x_4270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4270, 0, x_4251);
lean_ctor_set(x_4270, 1, x_4269);
x_4271 = lean_array_push(x_4259, x_4270);
x_4272 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4273, 0, x_4272);
lean_ctor_set(x_4273, 1, x_4271);
lean_ctor_set(x_4191, 1, x_4273);
x_4274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4274, 0, x_4191);
lean_ctor_set(x_4274, 1, x_4243);
return x_4274;
}
}
else
{
lean_object* x_4275; lean_object* x_4276; lean_object* x_4277; lean_object* x_4278; lean_object* x_4279; lean_object* x_4280; lean_object* x_4281; lean_object* x_4282; lean_object* x_4283; lean_object* x_4284; lean_object* x_4285; lean_object* x_4286; lean_object* x_4287; lean_object* x_4288; lean_object* x_4289; lean_object* x_4290; lean_object* x_4291; lean_object* x_4292; lean_object* x_4293; lean_object* x_4294; lean_object* x_4295; lean_object* x_4296; lean_object* x_4297; lean_object* x_4298; lean_object* x_4299; lean_object* x_4300; lean_object* x_4301; lean_object* x_4302; lean_object* x_4303; lean_object* x_4304; lean_object* x_4305; lean_object* x_4306; lean_object* x_4307; lean_object* x_4308; lean_object* x_4309; lean_object* x_4310; lean_object* x_4311; lean_object* x_4312; lean_object* x_4313; 
x_4275 = lean_ctor_get(x_4191, 0);
x_4276 = lean_ctor_get(x_4191, 1);
lean_inc(x_4276);
lean_inc(x_4275);
lean_dec(x_4191);
x_4277 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4192);
lean_dec(x_5);
x_4278 = lean_ctor_get(x_4277, 1);
lean_inc(x_4278);
lean_dec(x_4277);
x_4279 = l_Lean_Elab_Term_getMainModule___rarg(x_4278);
x_4280 = lean_ctor_get(x_4279, 1);
lean_inc(x_4280);
if (lean_is_exclusive(x_4279)) {
 lean_ctor_release(x_4279, 0);
 lean_ctor_release(x_4279, 1);
 x_4281 = x_4279;
} else {
 lean_dec_ref(x_4279);
 x_4281 = lean_box(0);
}
x_4282 = l_Array_empty___closed__1;
x_4283 = lean_array_push(x_4282, x_4183);
x_4284 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4285 = lean_array_push(x_4283, x_4284);
x_4286 = l_Lean_mkTermIdFromIdent___closed__2;
x_4287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4287, 0, x_4286);
lean_ctor_set(x_4287, 1, x_4285);
x_4288 = lean_array_push(x_4282, x_4287);
x_4289 = l_Lean_nullKind___closed__2;
x_4290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4290, 0, x_4289);
lean_ctor_set(x_4290, 1, x_4288);
x_4291 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4292 = lean_array_push(x_4291, x_4290);
x_4293 = lean_array_push(x_4292, x_4284);
x_4294 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4295 = lean_array_push(x_4293, x_4294);
x_4296 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4297 = lean_array_push(x_4295, x_4296);
lean_inc(x_11);
x_4298 = lean_array_push(x_4282, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_4299 = x_11;
} else {
 lean_dec_ref(x_11);
 x_4299 = lean_box(0);
}
if (lean_is_scalar(x_4299)) {
 x_4300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4300 = x_4299;
}
lean_ctor_set(x_4300, 0, x_4289);
lean_ctor_set(x_4300, 1, x_4298);
x_4301 = lean_array_push(x_4282, x_4300);
x_4302 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4303 = lean_array_push(x_4301, x_4302);
x_4304 = lean_array_push(x_4303, x_4276);
x_4305 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4306, 0, x_4305);
lean_ctor_set(x_4306, 1, x_4304);
x_4307 = lean_array_push(x_4282, x_4306);
x_4308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4308, 0, x_4289);
lean_ctor_set(x_4308, 1, x_4307);
x_4309 = lean_array_push(x_4297, x_4308);
x_4310 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4311, 0, x_4310);
lean_ctor_set(x_4311, 1, x_4309);
x_4312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4312, 0, x_4275);
lean_ctor_set(x_4312, 1, x_4311);
if (lean_is_scalar(x_4281)) {
 x_4313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4313 = x_4281;
}
lean_ctor_set(x_4313, 0, x_4312);
lean_ctor_set(x_4313, 1, x_4280);
return x_4313;
}
}
else
{
uint8_t x_4314; 
lean_dec(x_4183);
lean_dec(x_11);
lean_dec(x_5);
x_4314 = !lean_is_exclusive(x_4190);
if (x_4314 == 0)
{
return x_4190;
}
else
{
lean_object* x_4315; lean_object* x_4316; lean_object* x_4317; 
x_4315 = lean_ctor_get(x_4190, 0);
x_4316 = lean_ctor_get(x_4190, 1);
lean_inc(x_4316);
lean_inc(x_4315);
lean_dec(x_4190);
x_4317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4317, 0, x_4315);
lean_ctor_set(x_4317, 1, x_4316);
return x_4317;
}
}
}
else
{
lean_object* x_4318; lean_object* x_4319; lean_object* x_4320; uint8_t x_4321; 
x_4318 = lean_ctor_get(x_4181, 0);
lean_inc(x_4318);
lean_dec(x_4181);
x_4319 = lean_ctor_get(x_4318, 0);
lean_inc(x_4319);
x_4320 = lean_ctor_get(x_4318, 1);
lean_inc(x_4320);
lean_dec(x_4318);
x_4321 = l_Lean_Syntax_isNone(x_4320);
lean_dec(x_4320);
if (x_4321 == 0)
{
lean_object* x_4322; lean_object* x_4323; uint8_t x_4324; 
lean_dec(x_4319);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4322 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_4323 = l_Lean_Elab_Term_throwError___rarg(x_11, x_4322, x_5, x_6);
lean_dec(x_11);
x_4324 = !lean_is_exclusive(x_4323);
if (x_4324 == 0)
{
return x_4323;
}
else
{
lean_object* x_4325; lean_object* x_4326; lean_object* x_4327; 
x_4325 = lean_ctor_get(x_4323, 0);
x_4326 = lean_ctor_get(x_4323, 1);
lean_inc(x_4326);
lean_inc(x_4325);
lean_dec(x_4323);
x_4327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4327, 0, x_4325);
lean_ctor_set(x_4327, 1, x_4326);
return x_4327;
}
}
else
{
lean_object* x_4328; lean_object* x_4329; lean_object* x_4330; lean_object* x_4331; lean_object* x_4332; 
x_4328 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_4329 = lean_unsigned_to_nat(1u);
x_4330 = lean_nat_add(x_3, x_4329);
lean_dec(x_3);
x_4331 = l_Lean_Elab_Term_mkExplicitBinder(x_4319, x_4328);
x_4332 = lean_array_push(x_4, x_4331);
x_3 = x_4330;
x_4 = x_4332;
goto _start;
}
}
}
}
case 2:
{
uint8_t x_4334; lean_object* x_4335; 
x_4334 = 1;
lean_inc(x_11);
x_4335 = l_Lean_Syntax_isTermId_x3f(x_11, x_4334);
if (lean_obj_tag(x_4335) == 0)
{
lean_object* x_4336; lean_object* x_4337; lean_object* x_4338; lean_object* x_4339; lean_object* x_4340; lean_object* x_4341; lean_object* x_4342; lean_object* x_4343; lean_object* x_4344; 
x_4336 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_4337 = lean_ctor_get(x_4336, 0);
lean_inc(x_4337);
x_4338 = lean_ctor_get(x_4336, 1);
lean_inc(x_4338);
lean_dec(x_4336);
x_4339 = lean_unsigned_to_nat(1u);
x_4340 = lean_nat_add(x_3, x_4339);
lean_dec(x_3);
x_4341 = l_Lean_mkHole(x_11);
lean_inc(x_4337);
x_4342 = l_Lean_Elab_Term_mkExplicitBinder(x_4337, x_4341);
x_4343 = lean_array_push(x_4, x_4342);
lean_inc(x_5);
x_4344 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_4340, x_4343, x_5, x_4338);
if (lean_obj_tag(x_4344) == 0)
{
lean_object* x_4345; lean_object* x_4346; uint8_t x_4347; 
x_4345 = lean_ctor_get(x_4344, 0);
lean_inc(x_4345);
x_4346 = lean_ctor_get(x_4344, 1);
lean_inc(x_4346);
lean_dec(x_4344);
x_4347 = !lean_is_exclusive(x_4345);
if (x_4347 == 0)
{
lean_object* x_4348; lean_object* x_4349; lean_object* x_4350; lean_object* x_4351; uint8_t x_4352; 
x_4348 = lean_ctor_get(x_4345, 1);
x_4349 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4346);
lean_dec(x_5);
x_4350 = lean_ctor_get(x_4349, 1);
lean_inc(x_4350);
lean_dec(x_4349);
x_4351 = l_Lean_Elab_Term_getMainModule___rarg(x_4350);
x_4352 = !lean_is_exclusive(x_4351);
if (x_4352 == 0)
{
lean_object* x_4353; lean_object* x_4354; lean_object* x_4355; lean_object* x_4356; lean_object* x_4357; lean_object* x_4358; lean_object* x_4359; lean_object* x_4360; lean_object* x_4361; lean_object* x_4362; lean_object* x_4363; lean_object* x_4364; lean_object* x_4365; lean_object* x_4366; lean_object* x_4367; lean_object* x_4368; lean_object* x_4369; lean_object* x_4370; uint8_t x_4371; 
x_4353 = lean_ctor_get(x_4351, 0);
lean_dec(x_4353);
x_4354 = l_Array_empty___closed__1;
x_4355 = lean_array_push(x_4354, x_4337);
x_4356 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4357 = lean_array_push(x_4355, x_4356);
x_4358 = l_Lean_mkTermIdFromIdent___closed__2;
x_4359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4359, 0, x_4358);
lean_ctor_set(x_4359, 1, x_4357);
x_4360 = lean_array_push(x_4354, x_4359);
x_4361 = l_Lean_nullKind___closed__2;
x_4362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4362, 0, x_4361);
lean_ctor_set(x_4362, 1, x_4360);
x_4363 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4364 = lean_array_push(x_4363, x_4362);
x_4365 = lean_array_push(x_4364, x_4356);
x_4366 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4367 = lean_array_push(x_4365, x_4366);
x_4368 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4369 = lean_array_push(x_4367, x_4368);
lean_inc(x_11);
x_4370 = lean_array_push(x_4354, x_11);
x_4371 = !lean_is_exclusive(x_11);
if (x_4371 == 0)
{
lean_object* x_4372; lean_object* x_4373; lean_object* x_4374; lean_object* x_4375; lean_object* x_4376; lean_object* x_4377; lean_object* x_4378; lean_object* x_4379; lean_object* x_4380; lean_object* x_4381; lean_object* x_4382; lean_object* x_4383; lean_object* x_4384; 
x_4372 = lean_ctor_get(x_11, 1);
lean_dec(x_4372);
x_4373 = lean_ctor_get(x_11, 0);
lean_dec(x_4373);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_4370);
lean_ctor_set(x_11, 0, x_4361);
x_4374 = lean_array_push(x_4354, x_11);
x_4375 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4376 = lean_array_push(x_4374, x_4375);
x_4377 = lean_array_push(x_4376, x_4348);
x_4378 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4379, 0, x_4378);
lean_ctor_set(x_4379, 1, x_4377);
x_4380 = lean_array_push(x_4354, x_4379);
x_4381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4381, 0, x_4361);
lean_ctor_set(x_4381, 1, x_4380);
x_4382 = lean_array_push(x_4369, x_4381);
x_4383 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4384, 0, x_4383);
lean_ctor_set(x_4384, 1, x_4382);
lean_ctor_set(x_4345, 1, x_4384);
lean_ctor_set(x_4351, 0, x_4345);
return x_4351;
}
else
{
lean_object* x_4385; lean_object* x_4386; lean_object* x_4387; lean_object* x_4388; lean_object* x_4389; lean_object* x_4390; lean_object* x_4391; lean_object* x_4392; lean_object* x_4393; lean_object* x_4394; lean_object* x_4395; lean_object* x_4396; 
lean_dec(x_11);
x_4385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4385, 0, x_4361);
lean_ctor_set(x_4385, 1, x_4370);
x_4386 = lean_array_push(x_4354, x_4385);
x_4387 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4388 = lean_array_push(x_4386, x_4387);
x_4389 = lean_array_push(x_4388, x_4348);
x_4390 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4391, 0, x_4390);
lean_ctor_set(x_4391, 1, x_4389);
x_4392 = lean_array_push(x_4354, x_4391);
x_4393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4393, 0, x_4361);
lean_ctor_set(x_4393, 1, x_4392);
x_4394 = lean_array_push(x_4369, x_4393);
x_4395 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4396, 0, x_4395);
lean_ctor_set(x_4396, 1, x_4394);
lean_ctor_set(x_4345, 1, x_4396);
lean_ctor_set(x_4351, 0, x_4345);
return x_4351;
}
}
else
{
lean_object* x_4397; lean_object* x_4398; lean_object* x_4399; lean_object* x_4400; lean_object* x_4401; lean_object* x_4402; lean_object* x_4403; lean_object* x_4404; lean_object* x_4405; lean_object* x_4406; lean_object* x_4407; lean_object* x_4408; lean_object* x_4409; lean_object* x_4410; lean_object* x_4411; lean_object* x_4412; lean_object* x_4413; lean_object* x_4414; lean_object* x_4415; lean_object* x_4416; lean_object* x_4417; lean_object* x_4418; lean_object* x_4419; lean_object* x_4420; lean_object* x_4421; lean_object* x_4422; lean_object* x_4423; lean_object* x_4424; lean_object* x_4425; lean_object* x_4426; lean_object* x_4427; lean_object* x_4428; 
x_4397 = lean_ctor_get(x_4351, 1);
lean_inc(x_4397);
lean_dec(x_4351);
x_4398 = l_Array_empty___closed__1;
x_4399 = lean_array_push(x_4398, x_4337);
x_4400 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4401 = lean_array_push(x_4399, x_4400);
x_4402 = l_Lean_mkTermIdFromIdent___closed__2;
x_4403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4403, 0, x_4402);
lean_ctor_set(x_4403, 1, x_4401);
x_4404 = lean_array_push(x_4398, x_4403);
x_4405 = l_Lean_nullKind___closed__2;
x_4406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4406, 0, x_4405);
lean_ctor_set(x_4406, 1, x_4404);
x_4407 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4408 = lean_array_push(x_4407, x_4406);
x_4409 = lean_array_push(x_4408, x_4400);
x_4410 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4411 = lean_array_push(x_4409, x_4410);
x_4412 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4413 = lean_array_push(x_4411, x_4412);
lean_inc(x_11);
x_4414 = lean_array_push(x_4398, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_4415 = x_11;
} else {
 lean_dec_ref(x_11);
 x_4415 = lean_box(0);
}
if (lean_is_scalar(x_4415)) {
 x_4416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4416 = x_4415;
 lean_ctor_set_tag(x_4416, 1);
}
lean_ctor_set(x_4416, 0, x_4405);
lean_ctor_set(x_4416, 1, x_4414);
x_4417 = lean_array_push(x_4398, x_4416);
x_4418 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4419 = lean_array_push(x_4417, x_4418);
x_4420 = lean_array_push(x_4419, x_4348);
x_4421 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4422, 0, x_4421);
lean_ctor_set(x_4422, 1, x_4420);
x_4423 = lean_array_push(x_4398, x_4422);
x_4424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4424, 0, x_4405);
lean_ctor_set(x_4424, 1, x_4423);
x_4425 = lean_array_push(x_4413, x_4424);
x_4426 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4427, 0, x_4426);
lean_ctor_set(x_4427, 1, x_4425);
lean_ctor_set(x_4345, 1, x_4427);
x_4428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4428, 0, x_4345);
lean_ctor_set(x_4428, 1, x_4397);
return x_4428;
}
}
else
{
lean_object* x_4429; lean_object* x_4430; lean_object* x_4431; lean_object* x_4432; lean_object* x_4433; lean_object* x_4434; lean_object* x_4435; lean_object* x_4436; lean_object* x_4437; lean_object* x_4438; lean_object* x_4439; lean_object* x_4440; lean_object* x_4441; lean_object* x_4442; lean_object* x_4443; lean_object* x_4444; lean_object* x_4445; lean_object* x_4446; lean_object* x_4447; lean_object* x_4448; lean_object* x_4449; lean_object* x_4450; lean_object* x_4451; lean_object* x_4452; lean_object* x_4453; lean_object* x_4454; lean_object* x_4455; lean_object* x_4456; lean_object* x_4457; lean_object* x_4458; lean_object* x_4459; lean_object* x_4460; lean_object* x_4461; lean_object* x_4462; lean_object* x_4463; lean_object* x_4464; lean_object* x_4465; lean_object* x_4466; lean_object* x_4467; 
x_4429 = lean_ctor_get(x_4345, 0);
x_4430 = lean_ctor_get(x_4345, 1);
lean_inc(x_4430);
lean_inc(x_4429);
lean_dec(x_4345);
x_4431 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4346);
lean_dec(x_5);
x_4432 = lean_ctor_get(x_4431, 1);
lean_inc(x_4432);
lean_dec(x_4431);
x_4433 = l_Lean_Elab_Term_getMainModule___rarg(x_4432);
x_4434 = lean_ctor_get(x_4433, 1);
lean_inc(x_4434);
if (lean_is_exclusive(x_4433)) {
 lean_ctor_release(x_4433, 0);
 lean_ctor_release(x_4433, 1);
 x_4435 = x_4433;
} else {
 lean_dec_ref(x_4433);
 x_4435 = lean_box(0);
}
x_4436 = l_Array_empty___closed__1;
x_4437 = lean_array_push(x_4436, x_4337);
x_4438 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4439 = lean_array_push(x_4437, x_4438);
x_4440 = l_Lean_mkTermIdFromIdent___closed__2;
x_4441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4441, 0, x_4440);
lean_ctor_set(x_4441, 1, x_4439);
x_4442 = lean_array_push(x_4436, x_4441);
x_4443 = l_Lean_nullKind___closed__2;
x_4444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4444, 0, x_4443);
lean_ctor_set(x_4444, 1, x_4442);
x_4445 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4446 = lean_array_push(x_4445, x_4444);
x_4447 = lean_array_push(x_4446, x_4438);
x_4448 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4449 = lean_array_push(x_4447, x_4448);
x_4450 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4451 = lean_array_push(x_4449, x_4450);
lean_inc(x_11);
x_4452 = lean_array_push(x_4436, x_11);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_4453 = x_11;
} else {
 lean_dec_ref(x_11);
 x_4453 = lean_box(0);
}
if (lean_is_scalar(x_4453)) {
 x_4454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4454 = x_4453;
 lean_ctor_set_tag(x_4454, 1);
}
lean_ctor_set(x_4454, 0, x_4443);
lean_ctor_set(x_4454, 1, x_4452);
x_4455 = lean_array_push(x_4436, x_4454);
x_4456 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4457 = lean_array_push(x_4455, x_4456);
x_4458 = lean_array_push(x_4457, x_4430);
x_4459 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4460, 0, x_4459);
lean_ctor_set(x_4460, 1, x_4458);
x_4461 = lean_array_push(x_4436, x_4460);
x_4462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4462, 0, x_4443);
lean_ctor_set(x_4462, 1, x_4461);
x_4463 = lean_array_push(x_4451, x_4462);
x_4464 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4465, 0, x_4464);
lean_ctor_set(x_4465, 1, x_4463);
x_4466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4466, 0, x_4429);
lean_ctor_set(x_4466, 1, x_4465);
if (lean_is_scalar(x_4435)) {
 x_4467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4467 = x_4435;
}
lean_ctor_set(x_4467, 0, x_4466);
lean_ctor_set(x_4467, 1, x_4434);
return x_4467;
}
}
else
{
uint8_t x_4468; 
lean_dec(x_4337);
lean_dec(x_11);
lean_dec(x_5);
x_4468 = !lean_is_exclusive(x_4344);
if (x_4468 == 0)
{
return x_4344;
}
else
{
lean_object* x_4469; lean_object* x_4470; lean_object* x_4471; 
x_4469 = lean_ctor_get(x_4344, 0);
x_4470 = lean_ctor_get(x_4344, 1);
lean_inc(x_4470);
lean_inc(x_4469);
lean_dec(x_4344);
x_4471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4471, 0, x_4469);
lean_ctor_set(x_4471, 1, x_4470);
return x_4471;
}
}
}
else
{
lean_object* x_4472; lean_object* x_4473; lean_object* x_4474; uint8_t x_4475; 
x_4472 = lean_ctor_get(x_4335, 0);
lean_inc(x_4472);
lean_dec(x_4335);
x_4473 = lean_ctor_get(x_4472, 0);
lean_inc(x_4473);
x_4474 = lean_ctor_get(x_4472, 1);
lean_inc(x_4474);
lean_dec(x_4472);
x_4475 = l_Lean_Syntax_isNone(x_4474);
lean_dec(x_4474);
if (x_4475 == 0)
{
lean_object* x_4476; lean_object* x_4477; uint8_t x_4478; 
lean_dec(x_4473);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4476 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_4477 = l_Lean_Elab_Term_throwError___rarg(x_11, x_4476, x_5, x_6);
lean_dec(x_11);
x_4478 = !lean_is_exclusive(x_4477);
if (x_4478 == 0)
{
return x_4477;
}
else
{
lean_object* x_4479; lean_object* x_4480; lean_object* x_4481; 
x_4479 = lean_ctor_get(x_4477, 0);
x_4480 = lean_ctor_get(x_4477, 1);
lean_inc(x_4480);
lean_inc(x_4479);
lean_dec(x_4477);
x_4481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4481, 0, x_4479);
lean_ctor_set(x_4481, 1, x_4480);
return x_4481;
}
}
else
{
lean_object* x_4482; lean_object* x_4483; lean_object* x_4484; lean_object* x_4485; lean_object* x_4486; 
x_4482 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_4483 = lean_unsigned_to_nat(1u);
x_4484 = lean_nat_add(x_3, x_4483);
lean_dec(x_3);
x_4485 = l_Lean_Elab_Term_mkExplicitBinder(x_4473, x_4482);
x_4486 = lean_array_push(x_4, x_4485);
x_3 = x_4484;
x_4 = x_4486;
goto _start;
}
}
}
default: 
{
uint8_t x_4488; lean_object* x_4489; 
x_4488 = 1;
lean_inc(x_11);
x_4489 = l_Lean_Syntax_isTermId_x3f(x_11, x_4488);
if (lean_obj_tag(x_4489) == 0)
{
lean_object* x_4490; lean_object* x_4491; lean_object* x_4492; lean_object* x_4493; lean_object* x_4494; lean_object* x_4495; lean_object* x_4496; lean_object* x_4497; lean_object* x_4498; 
x_4490 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_11, x_5, x_6);
x_4491 = lean_ctor_get(x_4490, 0);
lean_inc(x_4491);
x_4492 = lean_ctor_get(x_4490, 1);
lean_inc(x_4492);
lean_dec(x_4490);
x_4493 = lean_unsigned_to_nat(1u);
x_4494 = lean_nat_add(x_3, x_4493);
lean_dec(x_3);
x_4495 = l_Lean_mkHole(x_11);
lean_inc(x_4491);
x_4496 = l_Lean_Elab_Term_mkExplicitBinder(x_4491, x_4495);
x_4497 = lean_array_push(x_4, x_4496);
lean_inc(x_5);
x_4498 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_4494, x_4497, x_5, x_4492);
if (lean_obj_tag(x_4498) == 0)
{
lean_object* x_4499; lean_object* x_4500; uint8_t x_4501; 
x_4499 = lean_ctor_get(x_4498, 0);
lean_inc(x_4499);
x_4500 = lean_ctor_get(x_4498, 1);
lean_inc(x_4500);
lean_dec(x_4498);
x_4501 = !lean_is_exclusive(x_4499);
if (x_4501 == 0)
{
lean_object* x_4502; lean_object* x_4503; lean_object* x_4504; lean_object* x_4505; uint8_t x_4506; 
x_4502 = lean_ctor_get(x_4499, 1);
x_4503 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4500);
lean_dec(x_5);
x_4504 = lean_ctor_get(x_4503, 1);
lean_inc(x_4504);
lean_dec(x_4503);
x_4505 = l_Lean_Elab_Term_getMainModule___rarg(x_4504);
x_4506 = !lean_is_exclusive(x_4505);
if (x_4506 == 0)
{
lean_object* x_4507; lean_object* x_4508; lean_object* x_4509; lean_object* x_4510; lean_object* x_4511; lean_object* x_4512; lean_object* x_4513; lean_object* x_4514; lean_object* x_4515; lean_object* x_4516; lean_object* x_4517; lean_object* x_4518; lean_object* x_4519; lean_object* x_4520; lean_object* x_4521; lean_object* x_4522; lean_object* x_4523; lean_object* x_4524; lean_object* x_4525; lean_object* x_4526; lean_object* x_4527; lean_object* x_4528; lean_object* x_4529; lean_object* x_4530; lean_object* x_4531; lean_object* x_4532; lean_object* x_4533; lean_object* x_4534; lean_object* x_4535; lean_object* x_4536; 
x_4507 = lean_ctor_get(x_4505, 0);
lean_dec(x_4507);
x_4508 = l_Array_empty___closed__1;
x_4509 = lean_array_push(x_4508, x_4491);
x_4510 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4511 = lean_array_push(x_4509, x_4510);
x_4512 = l_Lean_mkTermIdFromIdent___closed__2;
x_4513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4513, 0, x_4512);
lean_ctor_set(x_4513, 1, x_4511);
x_4514 = lean_array_push(x_4508, x_4513);
x_4515 = l_Lean_nullKind___closed__2;
x_4516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4516, 0, x_4515);
lean_ctor_set(x_4516, 1, x_4514);
x_4517 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4518 = lean_array_push(x_4517, x_4516);
x_4519 = lean_array_push(x_4518, x_4510);
x_4520 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4521 = lean_array_push(x_4519, x_4520);
x_4522 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4523 = lean_array_push(x_4521, x_4522);
x_4524 = lean_array_push(x_4508, x_11);
x_4525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4525, 0, x_4515);
lean_ctor_set(x_4525, 1, x_4524);
x_4526 = lean_array_push(x_4508, x_4525);
x_4527 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4528 = lean_array_push(x_4526, x_4527);
x_4529 = lean_array_push(x_4528, x_4502);
x_4530 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4531, 0, x_4530);
lean_ctor_set(x_4531, 1, x_4529);
x_4532 = lean_array_push(x_4508, x_4531);
x_4533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4533, 0, x_4515);
lean_ctor_set(x_4533, 1, x_4532);
x_4534 = lean_array_push(x_4523, x_4533);
x_4535 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4536, 0, x_4535);
lean_ctor_set(x_4536, 1, x_4534);
lean_ctor_set(x_4499, 1, x_4536);
lean_ctor_set(x_4505, 0, x_4499);
return x_4505;
}
else
{
lean_object* x_4537; lean_object* x_4538; lean_object* x_4539; lean_object* x_4540; lean_object* x_4541; lean_object* x_4542; lean_object* x_4543; lean_object* x_4544; lean_object* x_4545; lean_object* x_4546; lean_object* x_4547; lean_object* x_4548; lean_object* x_4549; lean_object* x_4550; lean_object* x_4551; lean_object* x_4552; lean_object* x_4553; lean_object* x_4554; lean_object* x_4555; lean_object* x_4556; lean_object* x_4557; lean_object* x_4558; lean_object* x_4559; lean_object* x_4560; lean_object* x_4561; lean_object* x_4562; lean_object* x_4563; lean_object* x_4564; lean_object* x_4565; lean_object* x_4566; lean_object* x_4567; 
x_4537 = lean_ctor_get(x_4505, 1);
lean_inc(x_4537);
lean_dec(x_4505);
x_4538 = l_Array_empty___closed__1;
x_4539 = lean_array_push(x_4538, x_4491);
x_4540 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4541 = lean_array_push(x_4539, x_4540);
x_4542 = l_Lean_mkTermIdFromIdent___closed__2;
x_4543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4543, 0, x_4542);
lean_ctor_set(x_4543, 1, x_4541);
x_4544 = lean_array_push(x_4538, x_4543);
x_4545 = l_Lean_nullKind___closed__2;
x_4546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4546, 0, x_4545);
lean_ctor_set(x_4546, 1, x_4544);
x_4547 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4548 = lean_array_push(x_4547, x_4546);
x_4549 = lean_array_push(x_4548, x_4540);
x_4550 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4551 = lean_array_push(x_4549, x_4550);
x_4552 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4553 = lean_array_push(x_4551, x_4552);
x_4554 = lean_array_push(x_4538, x_11);
x_4555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4555, 0, x_4545);
lean_ctor_set(x_4555, 1, x_4554);
x_4556 = lean_array_push(x_4538, x_4555);
x_4557 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4558 = lean_array_push(x_4556, x_4557);
x_4559 = lean_array_push(x_4558, x_4502);
x_4560 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4561, 0, x_4560);
lean_ctor_set(x_4561, 1, x_4559);
x_4562 = lean_array_push(x_4538, x_4561);
x_4563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4563, 0, x_4545);
lean_ctor_set(x_4563, 1, x_4562);
x_4564 = lean_array_push(x_4553, x_4563);
x_4565 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4566, 0, x_4565);
lean_ctor_set(x_4566, 1, x_4564);
lean_ctor_set(x_4499, 1, x_4566);
x_4567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4567, 0, x_4499);
lean_ctor_set(x_4567, 1, x_4537);
return x_4567;
}
}
else
{
lean_object* x_4568; lean_object* x_4569; lean_object* x_4570; lean_object* x_4571; lean_object* x_4572; lean_object* x_4573; lean_object* x_4574; lean_object* x_4575; lean_object* x_4576; lean_object* x_4577; lean_object* x_4578; lean_object* x_4579; lean_object* x_4580; lean_object* x_4581; lean_object* x_4582; lean_object* x_4583; lean_object* x_4584; lean_object* x_4585; lean_object* x_4586; lean_object* x_4587; lean_object* x_4588; lean_object* x_4589; lean_object* x_4590; lean_object* x_4591; lean_object* x_4592; lean_object* x_4593; lean_object* x_4594; lean_object* x_4595; lean_object* x_4596; lean_object* x_4597; lean_object* x_4598; lean_object* x_4599; lean_object* x_4600; lean_object* x_4601; lean_object* x_4602; lean_object* x_4603; lean_object* x_4604; lean_object* x_4605; 
x_4568 = lean_ctor_get(x_4499, 0);
x_4569 = lean_ctor_get(x_4499, 1);
lean_inc(x_4569);
lean_inc(x_4568);
lean_dec(x_4499);
x_4570 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4500);
lean_dec(x_5);
x_4571 = lean_ctor_get(x_4570, 1);
lean_inc(x_4571);
lean_dec(x_4570);
x_4572 = l_Lean_Elab_Term_getMainModule___rarg(x_4571);
x_4573 = lean_ctor_get(x_4572, 1);
lean_inc(x_4573);
if (lean_is_exclusive(x_4572)) {
 lean_ctor_release(x_4572, 0);
 lean_ctor_release(x_4572, 1);
 x_4574 = x_4572;
} else {
 lean_dec_ref(x_4572);
 x_4574 = lean_box(0);
}
x_4575 = l_Array_empty___closed__1;
x_4576 = lean_array_push(x_4575, x_4491);
x_4577 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_4578 = lean_array_push(x_4576, x_4577);
x_4579 = l_Lean_mkTermIdFromIdent___closed__2;
x_4580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4580, 0, x_4579);
lean_ctor_set(x_4580, 1, x_4578);
x_4581 = lean_array_push(x_4575, x_4580);
x_4582 = l_Lean_nullKind___closed__2;
x_4583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4583, 0, x_4582);
lean_ctor_set(x_4583, 1, x_4581);
x_4584 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_4585 = lean_array_push(x_4584, x_4583);
x_4586 = lean_array_push(x_4585, x_4577);
x_4587 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_4588 = lean_array_push(x_4586, x_4587);
x_4589 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7;
x_4590 = lean_array_push(x_4588, x_4589);
x_4591 = lean_array_push(x_4575, x_11);
x_4592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4592, 0, x_4582);
lean_ctor_set(x_4592, 1, x_4591);
x_4593 = lean_array_push(x_4575, x_4592);
x_4594 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_4595 = lean_array_push(x_4593, x_4594);
x_4596 = lean_array_push(x_4595, x_4569);
x_4597 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4598, 0, x_4597);
lean_ctor_set(x_4598, 1, x_4596);
x_4599 = lean_array_push(x_4575, x_4598);
x_4600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4600, 0, x_4582);
lean_ctor_set(x_4600, 1, x_4599);
x_4601 = lean_array_push(x_4590, x_4600);
x_4602 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4603, 0, x_4602);
lean_ctor_set(x_4603, 1, x_4601);
x_4604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4604, 0, x_4568);
lean_ctor_set(x_4604, 1, x_4603);
if (lean_is_scalar(x_4574)) {
 x_4605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4605 = x_4574;
}
lean_ctor_set(x_4605, 0, x_4604);
lean_ctor_set(x_4605, 1, x_4573);
return x_4605;
}
}
else
{
uint8_t x_4606; 
lean_dec(x_4491);
lean_dec(x_11);
lean_dec(x_5);
x_4606 = !lean_is_exclusive(x_4498);
if (x_4606 == 0)
{
return x_4498;
}
else
{
lean_object* x_4607; lean_object* x_4608; lean_object* x_4609; 
x_4607 = lean_ctor_get(x_4498, 0);
x_4608 = lean_ctor_get(x_4498, 1);
lean_inc(x_4608);
lean_inc(x_4607);
lean_dec(x_4498);
x_4609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4609, 0, x_4607);
lean_ctor_set(x_4609, 1, x_4608);
return x_4609;
}
}
}
else
{
lean_object* x_4610; lean_object* x_4611; lean_object* x_4612; uint8_t x_4613; 
x_4610 = lean_ctor_get(x_4489, 0);
lean_inc(x_4610);
lean_dec(x_4489);
x_4611 = lean_ctor_get(x_4610, 0);
lean_inc(x_4611);
x_4612 = lean_ctor_get(x_4610, 1);
lean_inc(x_4612);
lean_dec(x_4610);
x_4613 = l_Lean_Syntax_isNone(x_4612);
lean_dec(x_4612);
if (x_4613 == 0)
{
lean_object* x_4614; lean_object* x_4615; uint8_t x_4616; 
lean_dec(x_4611);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4614 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10;
x_4615 = l_Lean_Elab_Term_throwError___rarg(x_11, x_4614, x_5, x_6);
lean_dec(x_11);
x_4616 = !lean_is_exclusive(x_4615);
if (x_4616 == 0)
{
return x_4615;
}
else
{
lean_object* x_4617; lean_object* x_4618; lean_object* x_4619; 
x_4617 = lean_ctor_get(x_4615, 0);
x_4618 = lean_ctor_get(x_4615, 1);
lean_inc(x_4618);
lean_inc(x_4617);
lean_dec(x_4615);
x_4619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4619, 0, x_4617);
lean_ctor_set(x_4619, 1, x_4618);
return x_4619;
}
}
else
{
lean_object* x_4620; lean_object* x_4621; lean_object* x_4622; lean_object* x_4623; lean_object* x_4624; 
x_4620 = l_Lean_mkHole(x_11);
lean_dec(x_11);
x_4621 = lean_unsigned_to_nat(1u);
x_4622 = lean_nat_add(x_3, x_4621);
lean_dec(x_3);
x_4623 = l_Lean_Elab_Term_mkExplicitBinder(x_4611, x_4620);
x_4624 = lean_array_push(x_4, x_4623);
x_3 = x_4622;
x_4 = x_4624;
goto _start;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main(x_1, x_2, x_5, x_6, x_3, x_4);
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
lean_object* _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("autoParam is not allowed at 'fun/λ' binders");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optParam is not allowed at 'fun/λ' binders");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_instantiateMVars(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_isOptParam(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAutoParam(x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
x_12 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3;
x_13 = l_Lean_Elab_Term_throwError___rarg(x_1, x_12, x_3, x_8);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_5);
lean_dec(x_7);
x_14 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6;
x_15 = l_Lean_Elab_Term_throwError___rarg(x_1, x_14, x_3, x_8);
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
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = l_Lean_Expr_isOptParam(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_isAutoParam(x_20);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3;
x_27 = l_Lean_Elab_Term_throwError___rarg(x_1, x_26, x_3, x_21);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_28 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6;
x_29 = l_Lean_Elab_Term_throwError___rarg(x_1, x_28, x_3, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_whnfForall(x_1, x_15, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 2);
lean_inc(x_26);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_3);
x_27 = l_Lean_Elab_Term_isDefEq(x_1, x_3, x_25, x_5, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(x_1, x_3, x_5, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_expr_instantiate1(x_26, x_2);
lean_dec(x_26);
lean_ctor_set(x_7, 0, x_32);
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set(x_33, 2, x_11);
lean_ctor_set(x_33, 3, x_7);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_12);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_expr_instantiate1(x_26, x_2);
lean_dec(x_26);
lean_ctor_set(x_7, 0, x_35);
x_36 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
lean_ctor_set(x_36, 2, x_11);
lean_ctor_set(x_36, 3, x_7);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_12);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_26);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
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
lean_dec(x_26);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_17);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_46 = lean_box(0);
x_20 = x_46;
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_21 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(0, 4, 1);
} else {
 x_22 = x_13;
}
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_11);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_12);
if (lean_is_scalar(x_19)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_19;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_47; 
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
return x_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
lean_dec(x_7);
lean_inc(x_5);
x_52 = l_Lean_Elab_Term_whnfForall(x_1, x_51, x_5, x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_obj_tag(x_53) == 7)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
lean_dec(x_13);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
lean_dec(x_53);
lean_inc(x_5);
lean_inc(x_3);
x_63 = l_Lean_Elab_Term_isDefEq(x_1, x_3, x_61, x_5, x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(x_1, x_3, x_5, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
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
x_68 = lean_expr_instantiate1(x_62, x_2);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_10);
lean_ctor_set(x_70, 2, x_11);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_12);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_62);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_74 = x_65;
} else {
 lean_dec_ref(x_65);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_78 = x_63;
} else {
 lean_dec_ref(x_63);
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
else
{
lean_object* x_80; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_3);
x_80 = lean_box(0);
x_56 = x_80;
goto block_60;
}
block_60:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_57 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_58 = lean_alloc_ctor(0, 4, 1);
} else {
 x_58 = x_13;
}
lean_ctor_set(x_58, 0, x_9);
lean_ctor_set(x_58, 1, x_10);
lean_ctor_set(x_58, 2, x_11);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_12);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_81 = lean_ctor_get(x_52, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_52, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_83 = x_52;
} else {
 lean_dec_ref(x_52);
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
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_12__propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_15 = l_Lean_BinderInfo_isExplicit(x_14);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_16, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_dec(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_inc(x_4);
lean_inc(x_17);
x_23 = l_Lean_Elab_Term_elabType(x_17, x_4, x_5);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_23, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_23, 1);
lean_inc(x_209);
lean_dec(x_23);
x_24 = x_3;
x_25 = x_208;
x_26 = x_209;
goto block_207;
}
else
{
uint8_t x_210; 
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_23);
if (x_210 == 0)
{
return x_23;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_23, 0);
x_212 = lean_ctor_get(x_23, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_23);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_3);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_3, 3);
lean_dec(x_215);
x_216 = lean_ctor_get(x_3, 2);
lean_dec(x_216);
x_217 = lean_ctor_get(x_3, 1);
lean_dec(x_217);
x_218 = lean_ctor_get(x_3, 0);
lean_dec(x_218);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_23, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_23, 1);
lean_inc(x_220);
lean_dec(x_23);
x_221 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_221);
x_24 = x_3;
x_25 = x_219;
x_26 = x_220;
goto block_207;
}
else
{
uint8_t x_222; 
lean_free_object(x_3);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_23);
if (x_222 == 0)
{
return x_23;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_23, 0);
x_224 = lean_ctor_get(x_23, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_23);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_23, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_23, 1);
lean_inc(x_227);
lean_dec(x_23);
x_228 = 1;
x_229 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_229, 0, x_10);
lean_ctor_set(x_229, 1, x_11);
lean_ctor_set(x_229, 2, x_12);
lean_ctor_set(x_229, 3, x_13);
lean_ctor_set_uint8(x_229, sizeof(void*)*4, x_228);
x_24 = x_229;
x_25 = x_226;
x_26 = x_227;
goto block_207;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_230 = lean_ctor_get(x_23, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_23, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_232 = x_23;
} else {
 lean_dec_ref(x_23);
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
block_207:
{
lean_object* x_27; 
lean_inc(x_4);
lean_inc(x_25);
x_27 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(x_17, x_25, x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_30);
x_32 = l_Lean_mkFVar(x_30);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get_uint8(x_24, sizeof(void*)*4);
lean_inc(x_32);
x_39 = lean_array_push(x_34, x_32);
if (x_38 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_dec(x_9);
lean_inc(x_25);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_25);
x_42 = 0;
x_43 = lean_box(0);
lean_inc(x_4);
x_44 = l_Lean_Elab_Term_mkFreshExprMVar(x_40, x_41, x_42, x_43, x_4, x_31);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Syntax_getId(x_40);
lean_dec(x_40);
lean_inc(x_25);
x_48 = lean_local_ctx_mk_let_decl(x_35, x_30, x_47, x_25, x_45);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_48);
lean_inc(x_39);
lean_ctor_set(x_24, 1, x_48);
lean_ctor_set(x_24, 0, x_39);
lean_inc(x_4);
x_49 = l_Lean_Elab_Term_isClass(x_17, x_25, x_4, x_46);
lean_dec(x_17);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_2, x_52);
lean_dec(x_2);
x_2 = x_53;
x_3 = x_24;
x_5 = x_51;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_24);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_55);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_32);
x_60 = lean_array_push(x_36, x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_2, x_61);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_63, 0, x_39);
lean_ctor_set(x_63, 1, x_48);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_37);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_38);
x_2 = x_62;
x_3 = x_63;
x_5 = x_58;
goto _start;
}
}
else
{
uint8_t x_65; 
lean_dec(x_24);
lean_dec(x_48);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
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
lean_inc(x_35);
lean_ctor_set(x_24, 0, x_39);
x_69 = lean_ctor_get(x_9, 0);
lean_inc(x_69);
lean_dec(x_9);
x_70 = l_Lean_Syntax_getId(x_69);
lean_inc(x_25);
x_71 = lean_local_ctx_mk_local_decl(x_35, x_30, x_70, x_25, x_14);
lean_inc(x_4);
lean_inc(x_25);
x_72 = l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(x_69, x_32, x_25, x_24, x_4, x_31);
lean_dec(x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 2);
x_78 = lean_ctor_get(x_73, 3);
x_79 = lean_ctor_get_uint8(x_73, sizeof(void*)*4);
x_80 = lean_ctor_get(x_73, 1);
lean_dec(x_80);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_71);
lean_inc(x_76);
lean_ctor_set(x_73, 1, x_71);
lean_inc(x_4);
x_81 = l_Lean_Elab_Term_isClass(x_17, x_25, x_4, x_74);
lean_dec(x_17);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_71);
lean_dec(x_32);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_2, x_84);
lean_dec(x_2);
x_2 = x_85;
x_3 = x_73;
x_5 = x_83;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_73);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_87);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_32);
x_92 = lean_array_push(x_77, x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_2, x_93);
lean_dec(x_2);
x_95 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_95, 0, x_76);
lean_ctor_set(x_95, 1, x_71);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_78);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_79);
x_2 = x_94;
x_3 = x_95;
x_5 = x_90;
goto _start;
}
}
else
{
uint8_t x_97; 
lean_dec(x_73);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_81);
if (x_97 == 0)
{
return x_81;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_81, 0);
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_81);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_73, 0);
x_102 = lean_ctor_get(x_73, 2);
x_103 = lean_ctor_get(x_73, 3);
x_104 = lean_ctor_get_uint8(x_73, sizeof(void*)*4);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_73);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_71);
lean_inc(x_101);
x_105 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_71);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*4, x_104);
lean_inc(x_4);
x_106 = l_Lean_Elab_Term_isClass(x_17, x_25, x_4, x_74);
lean_dec(x_17);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_71);
lean_dec(x_32);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_add(x_2, x_109);
lean_dec(x_2);
x_2 = x_110;
x_3 = x_105;
x_5 = x_108;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_105);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
lean_dec(x_107);
x_114 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_112);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_32);
x_117 = lean_array_push(x_102, x_116);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_2, x_118);
lean_dec(x_2);
x_120 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set(x_120, 1, x_71);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_103);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_104);
x_2 = x_119;
x_3 = x_120;
x_5 = x_115;
goto _start;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_122 = lean_ctor_get(x_106, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_106, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_124 = x_106;
} else {
 lean_dec_ref(x_106);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_72);
if (x_126 == 0)
{
return x_72;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_72, 0);
x_128 = lean_ctor_get(x_72, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_72);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_24, 0);
x_131 = lean_ctor_get(x_24, 1);
x_132 = lean_ctor_get(x_24, 2);
x_133 = lean_ctor_get(x_24, 3);
x_134 = lean_ctor_get_uint8(x_24, sizeof(void*)*4);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_24);
lean_inc(x_32);
x_135 = lean_array_push(x_130, x_32);
if (x_134 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_136 = lean_ctor_get(x_9, 0);
lean_inc(x_136);
lean_dec(x_9);
lean_inc(x_25);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_25);
x_138 = 0;
x_139 = lean_box(0);
lean_inc(x_4);
x_140 = l_Lean_Elab_Term_mkFreshExprMVar(x_136, x_137, x_138, x_139, x_4, x_31);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Syntax_getId(x_136);
lean_dec(x_136);
lean_inc(x_25);
x_144 = lean_local_ctx_mk_let_decl(x_131, x_30, x_143, x_25, x_141);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_144);
lean_inc(x_135);
x_145 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_132);
lean_ctor_set(x_145, 3, x_133);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_134);
lean_inc(x_4);
x_146 = l_Lean_Elab_Term_isClass(x_17, x_25, x_4, x_142);
lean_dec(x_17);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_144);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_32);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_add(x_2, x_149);
lean_dec(x_2);
x_2 = x_150;
x_3 = x_145;
x_5 = x_148;
goto _start;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_145);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
lean_dec(x_146);
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
lean_dec(x_147);
x_154 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_152);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_32);
x_157 = lean_array_push(x_132, x_156);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_add(x_2, x_158);
lean_dec(x_2);
x_160 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_160, 0, x_135);
lean_ctor_set(x_160, 1, x_144);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_133);
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_134);
x_2 = x_159;
x_3 = x_160;
x_5 = x_155;
goto _start;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_162 = lean_ctor_get(x_146, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_146, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_164 = x_146;
} else {
 lean_dec_ref(x_146);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_inc(x_131);
x_166 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_166, 0, x_135);
lean_ctor_set(x_166, 1, x_131);
lean_ctor_set(x_166, 2, x_132);
lean_ctor_set(x_166, 3, x_133);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_134);
x_167 = lean_ctor_get(x_9, 0);
lean_inc(x_167);
lean_dec(x_9);
x_168 = l_Lean_Syntax_getId(x_167);
lean_inc(x_25);
x_169 = lean_local_ctx_mk_local_decl(x_131, x_30, x_168, x_25, x_14);
lean_inc(x_4);
lean_inc(x_25);
x_170 = l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(x_167, x_32, x_25, x_166, x_4, x_31);
lean_dec(x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_171, sizeof(void*)*4);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 x_177 = x_171;
} else {
 lean_dec_ref(x_171);
 x_177 = lean_box(0);
}
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_169);
lean_inc(x_173);
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 4, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_174);
lean_ctor_set(x_178, 3, x_175);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_176);
lean_inc(x_4);
x_179 = l_Lean_Elab_Term_isClass(x_17, x_25, x_4, x_172);
lean_dec(x_17);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_32);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_add(x_2, x_182);
lean_dec(x_2);
x_2 = x_183;
x_3 = x_178;
x_5 = x_181;
goto _start;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_178);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec(x_179);
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
lean_dec(x_180);
x_187 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_185);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_32);
x_190 = lean_array_push(x_174, x_189);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_add(x_2, x_191);
lean_dec(x_2);
x_193 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_193, 0, x_173);
lean_ctor_set(x_193, 1, x_169);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_175);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_176);
x_2 = x_192;
x_3 = x_193;
x_5 = x_188;
goto _start;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_195 = lean_ctor_get(x_179, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_179, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_197 = x_179;
} else {
 lean_dec_ref(x_179);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_169);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_2);
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
}
else
{
uint8_t x_203; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_27);
if (x_203 == 0)
{
return x_27;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_27, 0);
x_205 = lean_ctor_get(x_27, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_27);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_234 = lean_ctor_get(x_16, 0);
x_235 = lean_ctor_get(x_16, 3);
x_236 = lean_ctor_get(x_16, 4);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
x_237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_11);
lean_ctor_set(x_237, 2, x_12);
lean_ctor_set(x_237, 3, x_235);
lean_ctor_set(x_237, 4, x_236);
lean_ctor_set(x_4, 0, x_237);
lean_inc(x_4);
lean_inc(x_17);
x_238 = l_Lean_Elab_Term_elabType(x_17, x_4, x_5);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_238, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_238, 1);
lean_inc(x_328);
lean_dec(x_238);
x_239 = x_3;
x_240 = x_327;
x_241 = x_328;
goto block_326;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_329 = lean_ctor_get(x_238, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_238, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_331 = x_238;
} else {
 lean_dec_ref(x_238);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
lean_object* x_333; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_333 = x_3;
} else {
 lean_dec_ref(x_3);
 x_333 = lean_box(0);
}
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_238, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_238, 1);
lean_inc(x_335);
lean_dec(x_238);
x_336 = 1;
if (lean_is_scalar(x_333)) {
 x_337 = lean_alloc_ctor(0, 4, 1);
} else {
 x_337 = x_333;
}
lean_ctor_set(x_337, 0, x_10);
lean_ctor_set(x_337, 1, x_11);
lean_ctor_set(x_337, 2, x_12);
lean_ctor_set(x_337, 3, x_13);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
x_239 = x_337;
x_240 = x_334;
x_241 = x_335;
goto block_326;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_333);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_338 = lean_ctor_get(x_238, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_238, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_340 = x_238;
} else {
 lean_dec_ref(x_238);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
block_326:
{
lean_object* x_242; 
lean_inc(x_4);
lean_inc(x_240);
x_242 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(x_17, x_240, x_4, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; 
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
lean_inc(x_245);
x_247 = l_Lean_mkFVar(x_245);
x_248 = lean_ctor_get(x_239, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_239, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_239, 2);
lean_inc(x_250);
x_251 = lean_ctor_get(x_239, 3);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_239, sizeof(void*)*4);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 x_253 = x_239;
} else {
 lean_dec_ref(x_239);
 x_253 = lean_box(0);
}
lean_inc(x_247);
x_254 = lean_array_push(x_248, x_247);
if (x_252 == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_255 = lean_ctor_get(x_9, 0);
lean_inc(x_255);
lean_dec(x_9);
lean_inc(x_240);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_240);
x_257 = 0;
x_258 = lean_box(0);
lean_inc(x_4);
x_259 = l_Lean_Elab_Term_mkFreshExprMVar(x_255, x_256, x_257, x_258, x_4, x_246);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_Syntax_getId(x_255);
lean_dec(x_255);
lean_inc(x_240);
x_263 = lean_local_ctx_mk_let_decl(x_249, x_245, x_262, x_240, x_260);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_263);
lean_inc(x_254);
if (lean_is_scalar(x_253)) {
 x_264 = lean_alloc_ctor(0, 4, 1);
} else {
 x_264 = x_253;
}
lean_ctor_set(x_264, 0, x_254);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_250);
lean_ctor_set(x_264, 3, x_251);
lean_ctor_set_uint8(x_264, sizeof(void*)*4, x_252);
lean_inc(x_4);
x_265 = l_Lean_Elab_Term_isClass(x_17, x_240, x_4, x_261);
lean_dec(x_17);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_263);
lean_dec(x_254);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_247);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_unsigned_to_nat(1u);
x_269 = lean_nat_add(x_2, x_268);
lean_dec(x_2);
x_2 = x_269;
x_3 = x_264;
x_5 = x_267;
goto _start;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_264);
x_271 = lean_ctor_get(x_265, 1);
lean_inc(x_271);
lean_dec(x_265);
x_272 = lean_ctor_get(x_266, 0);
lean_inc(x_272);
lean_dec(x_266);
x_273 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_271);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_247);
x_276 = lean_array_push(x_250, x_275);
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_nat_add(x_2, x_277);
lean_dec(x_2);
x_279 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_279, 0, x_254);
lean_ctor_set(x_279, 1, x_263);
lean_ctor_set(x_279, 2, x_276);
lean_ctor_set(x_279, 3, x_251);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_252);
x_2 = x_278;
x_3 = x_279;
x_5 = x_274;
goto _start;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_254);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_247);
lean_dec(x_4);
lean_dec(x_2);
x_281 = lean_ctor_get(x_265, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_265, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_283 = x_265;
} else {
 lean_dec_ref(x_265);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_inc(x_249);
if (lean_is_scalar(x_253)) {
 x_285 = lean_alloc_ctor(0, 4, 1);
} else {
 x_285 = x_253;
}
lean_ctor_set(x_285, 0, x_254);
lean_ctor_set(x_285, 1, x_249);
lean_ctor_set(x_285, 2, x_250);
lean_ctor_set(x_285, 3, x_251);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_252);
x_286 = lean_ctor_get(x_9, 0);
lean_inc(x_286);
lean_dec(x_9);
x_287 = l_Lean_Syntax_getId(x_286);
lean_inc(x_240);
x_288 = lean_local_ctx_mk_local_decl(x_249, x_245, x_287, x_240, x_14);
lean_inc(x_4);
lean_inc(x_240);
x_289 = l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(x_286, x_247, x_240, x_285, x_4, x_246);
lean_dec(x_286);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_290, 2);
lean_inc(x_293);
x_294 = lean_ctor_get(x_290, 3);
lean_inc(x_294);
x_295 = lean_ctor_get_uint8(x_290, sizeof(void*)*4);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 x_296 = x_290;
} else {
 lean_dec_ref(x_290);
 x_296 = lean_box(0);
}
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_288);
lean_inc(x_292);
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(0, 4, 1);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_292);
lean_ctor_set(x_297, 1, x_288);
lean_ctor_set(x_297, 2, x_293);
lean_ctor_set(x_297, 3, x_294);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_295);
lean_inc(x_4);
x_298 = l_Lean_Elab_Term_isClass(x_17, x_240, x_4, x_291);
lean_dec(x_17);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_288);
lean_dec(x_247);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_nat_add(x_2, x_301);
lean_dec(x_2);
x_2 = x_302;
x_3 = x_297;
x_5 = x_300;
goto _start;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_297);
x_304 = lean_ctor_get(x_298, 1);
lean_inc(x_304);
lean_dec(x_298);
x_305 = lean_ctor_get(x_299, 0);
lean_inc(x_305);
lean_dec(x_299);
x_306 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_304);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_247);
x_309 = lean_array_push(x_293, x_308);
x_310 = lean_unsigned_to_nat(1u);
x_311 = lean_nat_add(x_2, x_310);
lean_dec(x_2);
x_312 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_312, 0, x_292);
lean_ctor_set(x_312, 1, x_288);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_294);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_295);
x_2 = x_311;
x_3 = x_312;
x_5 = x_307;
goto _start;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_297);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_288);
lean_dec(x_247);
lean_dec(x_4);
lean_dec(x_2);
x_314 = lean_ctor_get(x_298, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_298, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_316 = x_298;
} else {
 lean_dec_ref(x_298);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_288);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_2);
x_318 = lean_ctor_get(x_289, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_289, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_320 = x_289;
} else {
 lean_dec_ref(x_289);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_2);
x_322 = lean_ctor_get(x_242, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_242, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_324 = x_242;
} else {
 lean_dec_ref(x_242);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; uint8_t x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_342 = lean_ctor_get(x_4, 1);
x_343 = lean_ctor_get(x_4, 2);
x_344 = lean_ctor_get(x_4, 3);
x_345 = lean_ctor_get(x_4, 4);
x_346 = lean_ctor_get(x_4, 5);
x_347 = lean_ctor_get(x_4, 6);
x_348 = lean_ctor_get(x_4, 7);
x_349 = lean_ctor_get(x_4, 8);
x_350 = lean_ctor_get(x_4, 9);
x_351 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_352 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_353 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_4);
x_354 = lean_ctor_get(x_16, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_16, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_16, 4);
lean_inc(x_356);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 x_357 = x_16;
} else {
 lean_dec_ref(x_16);
 x_357 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(0, 5, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_354);
lean_ctor_set(x_358, 1, x_11);
lean_ctor_set(x_358, 2, x_12);
lean_ctor_set(x_358, 3, x_355);
lean_ctor_set(x_358, 4, x_356);
x_359 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_342);
lean_ctor_set(x_359, 2, x_343);
lean_ctor_set(x_359, 3, x_344);
lean_ctor_set(x_359, 4, x_345);
lean_ctor_set(x_359, 5, x_346);
lean_ctor_set(x_359, 6, x_347);
lean_ctor_set(x_359, 7, x_348);
lean_ctor_set(x_359, 8, x_349);
lean_ctor_set(x_359, 9, x_350);
lean_ctor_set_uint8(x_359, sizeof(void*)*10, x_351);
lean_ctor_set_uint8(x_359, sizeof(void*)*10 + 1, x_352);
lean_ctor_set_uint8(x_359, sizeof(void*)*10 + 2, x_353);
lean_inc(x_359);
lean_inc(x_17);
x_360 = l_Lean_Elab_Term_elabType(x_17, x_359, x_5);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_360, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_360, 1);
lean_inc(x_450);
lean_dec(x_360);
x_361 = x_3;
x_362 = x_449;
x_363 = x_450;
goto block_448;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_359);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_451 = lean_ctor_get(x_360, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_360, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_453 = x_360;
} else {
 lean_dec_ref(x_360);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
return x_454;
}
}
else
{
lean_object* x_455; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_455 = x_3;
} else {
 lean_dec_ref(x_3);
 x_455 = lean_box(0);
}
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_360, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_360, 1);
lean_inc(x_457);
lean_dec(x_360);
x_458 = 1;
if (lean_is_scalar(x_455)) {
 x_459 = lean_alloc_ctor(0, 4, 1);
} else {
 x_459 = x_455;
}
lean_ctor_set(x_459, 0, x_10);
lean_ctor_set(x_459, 1, x_11);
lean_ctor_set(x_459, 2, x_12);
lean_ctor_set(x_459, 3, x_13);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
x_361 = x_459;
x_362 = x_456;
x_363 = x_457;
goto block_448;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_455);
lean_dec(x_359);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_460 = lean_ctor_get(x_360, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_360, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_462 = x_360;
} else {
 lean_dec_ref(x_360);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
}
block_448:
{
lean_object* x_364; 
lean_inc(x_359);
lean_inc(x_362);
x_364 = l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam(x_17, x_362, x_359, x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
lean_inc(x_367);
x_369 = l_Lean_mkFVar(x_367);
x_370 = lean_ctor_get(x_361, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_361, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_361, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_361, 3);
lean_inc(x_373);
x_374 = lean_ctor_get_uint8(x_361, sizeof(void*)*4);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 lean_ctor_release(x_361, 2);
 lean_ctor_release(x_361, 3);
 x_375 = x_361;
} else {
 lean_dec_ref(x_361);
 x_375 = lean_box(0);
}
lean_inc(x_369);
x_376 = lean_array_push(x_370, x_369);
if (x_374 == 0)
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_377 = lean_ctor_get(x_9, 0);
lean_inc(x_377);
lean_dec(x_9);
lean_inc(x_362);
x_378 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_378, 0, x_362);
x_379 = 0;
x_380 = lean_box(0);
lean_inc(x_359);
x_381 = l_Lean_Elab_Term_mkFreshExprMVar(x_377, x_378, x_379, x_380, x_359, x_368);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = l_Lean_Syntax_getId(x_377);
lean_dec(x_377);
lean_inc(x_362);
x_385 = lean_local_ctx_mk_let_decl(x_371, x_367, x_384, x_362, x_382);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_385);
lean_inc(x_376);
if (lean_is_scalar(x_375)) {
 x_386 = lean_alloc_ctor(0, 4, 1);
} else {
 x_386 = x_375;
}
lean_ctor_set(x_386, 0, x_376);
lean_ctor_set(x_386, 1, x_385);
lean_ctor_set(x_386, 2, x_372);
lean_ctor_set(x_386, 3, x_373);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_374);
lean_inc(x_359);
x_387 = l_Lean_Elab_Term_isClass(x_17, x_362, x_359, x_383);
lean_dec(x_17);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_385);
lean_dec(x_376);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_369);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_unsigned_to_nat(1u);
x_391 = lean_nat_add(x_2, x_390);
lean_dec(x_2);
x_2 = x_391;
x_3 = x_386;
x_4 = x_359;
x_5 = x_389;
goto _start;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_386);
x_393 = lean_ctor_get(x_387, 1);
lean_inc(x_393);
lean_dec(x_387);
x_394 = lean_ctor_get(x_388, 0);
lean_inc(x_394);
lean_dec(x_388);
x_395 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_393);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_369);
x_398 = lean_array_push(x_372, x_397);
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_nat_add(x_2, x_399);
lean_dec(x_2);
x_401 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_401, 0, x_376);
lean_ctor_set(x_401, 1, x_385);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_373);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_374);
x_2 = x_400;
x_3 = x_401;
x_4 = x_359;
x_5 = x_396;
goto _start;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_376);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_369);
lean_dec(x_359);
lean_dec(x_2);
x_403 = lean_ctor_get(x_387, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_387, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_405 = x_387;
} else {
 lean_dec_ref(x_387);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_inc(x_371);
if (lean_is_scalar(x_375)) {
 x_407 = lean_alloc_ctor(0, 4, 1);
} else {
 x_407 = x_375;
}
lean_ctor_set(x_407, 0, x_376);
lean_ctor_set(x_407, 1, x_371);
lean_ctor_set(x_407, 2, x_372);
lean_ctor_set(x_407, 3, x_373);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_374);
x_408 = lean_ctor_get(x_9, 0);
lean_inc(x_408);
lean_dec(x_9);
x_409 = l_Lean_Syntax_getId(x_408);
lean_inc(x_362);
x_410 = lean_local_ctx_mk_local_decl(x_371, x_367, x_409, x_362, x_14);
lean_inc(x_359);
lean_inc(x_362);
x_411 = l___private_Init_Lean_Elab_Binders_12__propagateExpectedType(x_408, x_369, x_362, x_407, x_359, x_368);
lean_dec(x_408);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_412, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_412, 3);
lean_inc(x_416);
x_417 = lean_ctor_get_uint8(x_412, sizeof(void*)*4);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_418 = x_412;
} else {
 lean_dec_ref(x_412);
 x_418 = lean_box(0);
}
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_410);
lean_inc(x_414);
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 4, 1);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_414);
lean_ctor_set(x_419, 1, x_410);
lean_ctor_set(x_419, 2, x_415);
lean_ctor_set(x_419, 3, x_416);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_417);
lean_inc(x_359);
x_420 = l_Lean_Elab_Term_isClass(x_17, x_362, x_359, x_413);
lean_dec(x_17);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_369);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_unsigned_to_nat(1u);
x_424 = lean_nat_add(x_2, x_423);
lean_dec(x_2);
x_2 = x_424;
x_3 = x_419;
x_4 = x_359;
x_5 = x_422;
goto _start;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_419);
x_426 = lean_ctor_get(x_420, 1);
lean_inc(x_426);
lean_dec(x_420);
x_427 = lean_ctor_get(x_421, 0);
lean_inc(x_427);
lean_dec(x_421);
x_428 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_426);
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec(x_428);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_369);
x_431 = lean_array_push(x_415, x_430);
x_432 = lean_unsigned_to_nat(1u);
x_433 = lean_nat_add(x_2, x_432);
lean_dec(x_2);
x_434 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_434, 0, x_414);
lean_ctor_set(x_434, 1, x_410);
lean_ctor_set(x_434, 2, x_431);
lean_ctor_set(x_434, 3, x_416);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_417);
x_2 = x_433;
x_3 = x_434;
x_4 = x_359;
x_5 = x_429;
goto _start;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_419);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_369);
lean_dec(x_359);
lean_dec(x_2);
x_436 = lean_ctor_get(x_420, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_420, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_438 = x_420;
} else {
 lean_dec_ref(x_420);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_410);
lean_dec(x_369);
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_17);
lean_dec(x_2);
x_440 = lean_ctor_get(x_411, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_411, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_442 = x_411;
} else {
 lean_dec_ref(x_411);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_359);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_2);
x_444 = lean_ctor_get(x_364, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_364, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_446 = x_364;
} else {
 lean_dec_ref(x_364);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_445);
return x_447;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_10 = l___private_Init_Lean_Elab_Binders_5__matchBinder(x_9, x_4, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_14 = l___private_Init_Lean_Elab_Binders_13__elabFunBinderViews___main(x_11, x_13, x_3, x_4, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_15;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
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
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_Elab_Term_getLCtx(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Term_getLocalInsts(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Array_empty___closed__1;
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_3);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(x_1, x_16, x_15, x_5, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_12);
lean_dec(x_12);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 3);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_20, x_25);
lean_dec(x_25);
lean_dec(x_20);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 1, x_22);
x_32 = lean_apply_4(x_4, x_21, x_24, x_5, x_19);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 3);
x_35 = lean_ctor_get(x_28, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_5, 0, x_36);
x_37 = lean_apply_4(x_4, x_21, x_24, x_5, x_19);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
x_40 = lean_ctor_get(x_5, 2);
x_41 = lean_ctor_get(x_5, 3);
x_42 = lean_ctor_get(x_5, 4);
x_43 = lean_ctor_get(x_5, 5);
x_44 = lean_ctor_get(x_5, 6);
x_45 = lean_ctor_get(x_5, 7);
x_46 = lean_ctor_get(x_5, 8);
x_47 = lean_ctor_get(x_5, 9);
x_48 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_49 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_50 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_5);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 4);
lean_inc(x_53);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 x_54 = x_38;
} else {
 lean_dec_ref(x_38);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_22);
lean_ctor_set(x_55, 2, x_23);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
x_56 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_39);
lean_ctor_set(x_56, 2, x_40);
lean_ctor_set(x_56, 3, x_41);
lean_ctor_set(x_56, 4, x_42);
lean_ctor_set(x_56, 5, x_43);
lean_ctor_set(x_56, 6, x_44);
lean_ctor_set(x_56, 7, x_45);
lean_ctor_set(x_56, 8, x_46);
lean_ctor_set(x_56, 9, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*10, x_48);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 1, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 2, x_50);
x_57 = lean_apply_4(x_4, x_21, x_24, x_56, x_19);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = lean_ctor_get(x_19, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_19);
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_5);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_5, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_dec(x_68);
lean_ctor_set(x_62, 2, x_23);
lean_ctor_set(x_62, 1, x_22);
x_69 = lean_apply_4(x_4, x_21, x_24, x_5, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 2);
lean_inc(x_72);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_69, 1);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_70, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_71, 2);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_72);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_72, 2);
lean_dec(x_80);
lean_ctor_set(x_72, 2, x_60);
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_60);
lean_ctor_set(x_71, 2, x_83);
return x_69;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_71, 0);
x_85 = lean_ctor_get(x_71, 1);
x_86 = lean_ctor_get(x_71, 3);
x_87 = lean_ctor_get(x_71, 4);
x_88 = lean_ctor_get(x_71, 5);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_71);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_91 = x_72;
} else {
 lean_dec_ref(x_72);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 3, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_60);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_92);
lean_ctor_set(x_93, 3, x_86);
lean_ctor_set(x_93, 4, x_87);
lean_ctor_set(x_93, 5, x_88);
lean_ctor_set(x_70, 0, x_93);
return x_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_94 = lean_ctor_get(x_70, 1);
x_95 = lean_ctor_get(x_70, 2);
x_96 = lean_ctor_get(x_70, 3);
x_97 = lean_ctor_get(x_70, 4);
x_98 = lean_ctor_get(x_70, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_99 = lean_ctor_get(x_71, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_71, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_71, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_71, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_71, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 x_104 = x_71;
} else {
 lean_dec_ref(x_71);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_72, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_72, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_107 = x_72;
} else {
 lean_dec_ref(x_72);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 3, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_60);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(0, 6, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_101);
lean_ctor_set(x_109, 4, x_102);
lean_ctor_set(x_109, 5, x_103);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_94);
lean_ctor_set(x_110, 2, x_95);
lean_ctor_set(x_110, 3, x_96);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_98);
lean_ctor_set(x_69, 1, x_110);
return x_69;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_111 = lean_ctor_get(x_69, 0);
lean_inc(x_111);
lean_dec(x_69);
x_112 = lean_ctor_get(x_70, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_70, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_70, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_70, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_70, 5);
lean_inc(x_116);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 x_117 = x_70;
} else {
 lean_dec_ref(x_70);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_71, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_71, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_71, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_71, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_71, 5);
lean_inc(x_122);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 x_123 = x_71;
} else {
 lean_dec_ref(x_71);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_72, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_72, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_126 = x_72;
} else {
 lean_dec_ref(x_72);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 3, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
lean_ctor_set(x_127, 2, x_60);
if (lean_is_scalar(x_123)) {
 x_128 = lean_alloc_ctor(0, 6, 0);
} else {
 x_128 = x_123;
}
lean_ctor_set(x_128, 0, x_118);
lean_ctor_set(x_128, 1, x_119);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set(x_128, 3, x_120);
lean_ctor_set(x_128, 4, x_121);
lean_ctor_set(x_128, 5, x_122);
if (lean_is_scalar(x_117)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_117;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_112);
lean_ctor_set(x_129, 2, x_113);
lean_ctor_set(x_129, 3, x_114);
lean_ctor_set(x_129, 4, x_115);
lean_ctor_set(x_129, 5, x_116);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_111);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_69, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 2);
lean_inc(x_133);
x_134 = !lean_is_exclusive(x_69);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_69, 1);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_131);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_131, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_132);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_132, 2);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_133);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_133, 2);
lean_dec(x_141);
lean_ctor_set(x_133, 2, x_60);
return x_69;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_133, 0);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_133);
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_60);
lean_ctor_set(x_132, 2, x_144);
return x_69;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_145 = lean_ctor_get(x_132, 0);
x_146 = lean_ctor_get(x_132, 1);
x_147 = lean_ctor_get(x_132, 3);
x_148 = lean_ctor_get(x_132, 4);
x_149 = lean_ctor_get(x_132, 5);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_132);
x_150 = lean_ctor_get(x_133, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_133, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 x_152 = x_133;
} else {
 lean_dec_ref(x_133);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 3, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_60);
x_154 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_147);
lean_ctor_set(x_154, 4, x_148);
lean_ctor_set(x_154, 5, x_149);
lean_ctor_set(x_131, 0, x_154);
return x_69;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_155 = lean_ctor_get(x_131, 1);
x_156 = lean_ctor_get(x_131, 2);
x_157 = lean_ctor_get(x_131, 3);
x_158 = lean_ctor_get(x_131, 4);
x_159 = lean_ctor_get(x_131, 5);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_131);
x_160 = lean_ctor_get(x_132, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_132, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_132, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_132, 4);
lean_inc(x_163);
x_164 = lean_ctor_get(x_132, 5);
lean_inc(x_164);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 lean_ctor_release(x_132, 5);
 x_165 = x_132;
} else {
 lean_dec_ref(x_132);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_133, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_133, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 x_168 = x_133;
} else {
 lean_dec_ref(x_133);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
lean_ctor_set(x_169, 2, x_60);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 6, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_160);
lean_ctor_set(x_170, 1, x_161);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_162);
lean_ctor_set(x_170, 4, x_163);
lean_ctor_set(x_170, 5, x_164);
x_171 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_155);
lean_ctor_set(x_171, 2, x_156);
lean_ctor_set(x_171, 3, x_157);
lean_ctor_set(x_171, 4, x_158);
lean_ctor_set(x_171, 5, x_159);
lean_ctor_set(x_69, 1, x_171);
return x_69;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_172 = lean_ctor_get(x_69, 0);
lean_inc(x_172);
lean_dec(x_69);
x_173 = lean_ctor_get(x_131, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_131, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_131, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_131, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_131, 5);
lean_inc(x_177);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_178 = x_131;
} else {
 lean_dec_ref(x_131);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_132, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_132, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_132, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_132, 4);
lean_inc(x_182);
x_183 = lean_ctor_get(x_132, 5);
lean_inc(x_183);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 lean_ctor_release(x_132, 5);
 x_184 = x_132;
} else {
 lean_dec_ref(x_132);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_133, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_133, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 x_187 = x_133;
} else {
 lean_dec_ref(x_133);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 3, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set(x_188, 2, x_60);
if (lean_is_scalar(x_184)) {
 x_189 = lean_alloc_ctor(0, 6, 0);
} else {
 x_189 = x_184;
}
lean_ctor_set(x_189, 0, x_179);
lean_ctor_set(x_189, 1, x_180);
lean_ctor_set(x_189, 2, x_188);
lean_ctor_set(x_189, 3, x_181);
lean_ctor_set(x_189, 4, x_182);
lean_ctor_set(x_189, 5, x_183);
if (lean_is_scalar(x_178)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_178;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_173);
lean_ctor_set(x_190, 2, x_174);
lean_ctor_set(x_190, 3, x_175);
lean_ctor_set(x_190, 4, x_176);
lean_ctor_set(x_190, 5, x_177);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_172);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_62, 0);
x_193 = lean_ctor_get(x_62, 3);
x_194 = lean_ctor_get(x_62, 4);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_62);
x_195 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_22);
lean_ctor_set(x_195, 2, x_23);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_194);
lean_ctor_set(x_5, 0, x_195);
x_196 = lean_apply_4(x_4, x_21, x_24, x_5, x_63);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_201 = x_196;
} else {
 lean_dec_ref(x_196);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_197, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_197, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_197, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_197, 5);
lean_inc(x_206);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 lean_ctor_release(x_197, 4);
 lean_ctor_release(x_197, 5);
 x_207 = x_197;
} else {
 lean_dec_ref(x_197);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_198, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_198, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_198, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_198, 4);
lean_inc(x_211);
x_212 = lean_ctor_get(x_198, 5);
lean_inc(x_212);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 lean_ctor_release(x_198, 5);
 x_213 = x_198;
} else {
 lean_dec_ref(x_198);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_199, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_199, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 x_216 = x_199;
} else {
 lean_dec_ref(x_199);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 3, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
lean_ctor_set(x_217, 2, x_60);
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(0, 6, 0);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_209);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_210);
lean_ctor_set(x_218, 4, x_211);
lean_ctor_set(x_218, 5, x_212);
if (lean_is_scalar(x_207)) {
 x_219 = lean_alloc_ctor(0, 6, 0);
} else {
 x_219 = x_207;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_202);
lean_ctor_set(x_219, 2, x_203);
lean_ctor_set(x_219, 3, x_204);
lean_ctor_set(x_219, 4, x_205);
lean_ctor_set(x_219, 5, x_206);
if (lean_is_scalar(x_201)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_201;
}
lean_ctor_set(x_220, 0, x_200);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_221 = lean_ctor_get(x_196, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_196, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_225 = x_196;
} else {
 lean_dec_ref(x_196);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_221, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_221, 3);
lean_inc(x_228);
x_229 = lean_ctor_get(x_221, 4);
lean_inc(x_229);
x_230 = lean_ctor_get(x_221, 5);
lean_inc(x_230);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 lean_ctor_release(x_221, 2);
 lean_ctor_release(x_221, 3);
 lean_ctor_release(x_221, 4);
 lean_ctor_release(x_221, 5);
 x_231 = x_221;
} else {
 lean_dec_ref(x_221);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_222, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_222, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_222, 3);
lean_inc(x_234);
x_235 = lean_ctor_get(x_222, 4);
lean_inc(x_235);
x_236 = lean_ctor_get(x_222, 5);
lean_inc(x_236);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 lean_ctor_release(x_222, 5);
 x_237 = x_222;
} else {
 lean_dec_ref(x_222);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_223, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_223, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 x_240 = x_223;
} else {
 lean_dec_ref(x_223);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 3, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
lean_ctor_set(x_241, 2, x_60);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 6, 0);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_232);
lean_ctor_set(x_242, 1, x_233);
lean_ctor_set(x_242, 2, x_241);
lean_ctor_set(x_242, 3, x_234);
lean_ctor_set(x_242, 4, x_235);
lean_ctor_set(x_242, 5, x_236);
if (lean_is_scalar(x_231)) {
 x_243 = lean_alloc_ctor(0, 6, 0);
} else {
 x_243 = x_231;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_226);
lean_ctor_set(x_243, 2, x_227);
lean_ctor_set(x_243, 3, x_228);
lean_ctor_set(x_243, 4, x_229);
lean_ctor_set(x_243, 5, x_230);
if (lean_is_scalar(x_225)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_225;
}
lean_ctor_set(x_244, 0, x_224);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_245 = lean_ctor_get(x_5, 1);
x_246 = lean_ctor_get(x_5, 2);
x_247 = lean_ctor_get(x_5, 3);
x_248 = lean_ctor_get(x_5, 4);
x_249 = lean_ctor_get(x_5, 5);
x_250 = lean_ctor_get(x_5, 6);
x_251 = lean_ctor_get(x_5, 7);
x_252 = lean_ctor_get(x_5, 8);
x_253 = lean_ctor_get(x_5, 9);
x_254 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_255 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_256 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_5);
x_257 = lean_ctor_get(x_62, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_62, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_62, 4);
lean_inc(x_259);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 x_260 = x_62;
} else {
 lean_dec_ref(x_62);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(0, 5, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_257);
lean_ctor_set(x_261, 1, x_22);
lean_ctor_set(x_261, 2, x_23);
lean_ctor_set(x_261, 3, x_258);
lean_ctor_set(x_261, 4, x_259);
x_262 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_245);
lean_ctor_set(x_262, 2, x_246);
lean_ctor_set(x_262, 3, x_247);
lean_ctor_set(x_262, 4, x_248);
lean_ctor_set(x_262, 5, x_249);
lean_ctor_set(x_262, 6, x_250);
lean_ctor_set(x_262, 7, x_251);
lean_ctor_set(x_262, 8, x_252);
lean_ctor_set(x_262, 9, x_253);
lean_ctor_set_uint8(x_262, sizeof(void*)*10, x_254);
lean_ctor_set_uint8(x_262, sizeof(void*)*10 + 1, x_255);
lean_ctor_set_uint8(x_262, sizeof(void*)*10 + 2, x_256);
x_263 = lean_apply_4(x_4, x_21, x_24, x_262, x_63);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_265, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_268 = x_263;
} else {
 lean_dec_ref(x_263);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_264, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_264, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_264, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_264, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_264, 5);
lean_inc(x_273);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 lean_ctor_release(x_264, 5);
 x_274 = x_264;
} else {
 lean_dec_ref(x_264);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_265, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_265, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_265, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_265, 4);
lean_inc(x_278);
x_279 = lean_ctor_get(x_265, 5);
lean_inc(x_279);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 lean_ctor_release(x_265, 5);
 x_280 = x_265;
} else {
 lean_dec_ref(x_265);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_266, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_266, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 x_283 = x_266;
} else {
 lean_dec_ref(x_266);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 3, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
lean_ctor_set(x_284, 2, x_60);
if (lean_is_scalar(x_280)) {
 x_285 = lean_alloc_ctor(0, 6, 0);
} else {
 x_285 = x_280;
}
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_276);
lean_ctor_set(x_285, 2, x_284);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set(x_285, 4, x_278);
lean_ctor_set(x_285, 5, x_279);
if (lean_is_scalar(x_274)) {
 x_286 = lean_alloc_ctor(0, 6, 0);
} else {
 x_286 = x_274;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_269);
lean_ctor_set(x_286, 2, x_270);
lean_ctor_set(x_286, 3, x_271);
lean_ctor_set(x_286, 4, x_272);
lean_ctor_set(x_286, 5, x_273);
if (lean_is_scalar(x_268)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_268;
}
lean_ctor_set(x_287, 0, x_267);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_288 = lean_ctor_get(x_263, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_289, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_263, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_292 = x_263;
} else {
 lean_dec_ref(x_263);
 x_292 = lean_box(0);
}
x_293 = lean_ctor_get(x_288, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_288, 2);
lean_inc(x_294);
x_295 = lean_ctor_get(x_288, 3);
lean_inc(x_295);
x_296 = lean_ctor_get(x_288, 4);
lean_inc(x_296);
x_297 = lean_ctor_get(x_288, 5);
lean_inc(x_297);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 lean_ctor_release(x_288, 4);
 lean_ctor_release(x_288, 5);
 x_298 = x_288;
} else {
 lean_dec_ref(x_288);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_289, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_289, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_289, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_289, 4);
lean_inc(x_302);
x_303 = lean_ctor_get(x_289, 5);
lean_inc(x_303);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 lean_ctor_release(x_289, 2);
 lean_ctor_release(x_289, 3);
 lean_ctor_release(x_289, 4);
 lean_ctor_release(x_289, 5);
 x_304 = x_289;
} else {
 lean_dec_ref(x_289);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_290, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_290, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 x_307 = x_290;
} else {
 lean_dec_ref(x_290);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 3, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
lean_ctor_set(x_308, 2, x_60);
if (lean_is_scalar(x_304)) {
 x_309 = lean_alloc_ctor(0, 6, 0);
} else {
 x_309 = x_304;
}
lean_ctor_set(x_309, 0, x_299);
lean_ctor_set(x_309, 1, x_300);
lean_ctor_set(x_309, 2, x_308);
lean_ctor_set(x_309, 3, x_301);
lean_ctor_set(x_309, 4, x_302);
lean_ctor_set(x_309, 5, x_303);
if (lean_is_scalar(x_298)) {
 x_310 = lean_alloc_ctor(0, 6, 0);
} else {
 x_310 = x_298;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_293);
lean_ctor_set(x_310, 2, x_294);
lean_ctor_set(x_310, 3, x_295);
lean_ctor_set(x_310, 4, x_296);
lean_ctor_set(x_310, 5, x_297);
if (lean_is_scalar(x_292)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_292;
}
lean_ctor_set(x_311, 0, x_291);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_312 = !lean_is_exclusive(x_17);
if (x_312 == 0)
{
return x_17;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_17, 0);
x_314 = lean_ctor_get(x_17, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_17);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = l_Array_empty___closed__1;
x_317 = lean_apply_4(x_4, x_316, x_2, x_5, x_6);
return x_317;
}
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFunBinders___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_Term_elabFunBinders___rarg(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabFunCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
x_8 = l_Lean_Elab_Term_elabTerm(x_1, x_4, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Term_mkLambda(x_2, x_3, x_9, x_5, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabFunCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_expandFunBinders(x_8, x_10, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFunCore___lambda__1___boxed), 6, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = l_Lean_Elab_Term_elabFunBinders___rarg(x_14, x_2, x_3, x_16, x_4, x_13);
lean_dec(x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Term_elabFunCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabFunCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabFunCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_elabFunCore(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_Term_elabFunCore(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabFun___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
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
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Elab_Term_elabType(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = 1;
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_2);
x_12 = l_Lean_Elab_Term_elabTerm(x_2, x_10, x_11, x_5, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_ensureHasType(x_2, x_10, x_13, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_mkForall(x_3, x_4, x_8, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_mkLambda(x_3, x_4, x_16, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
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
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
return x_12;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
x_8 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_instantiateMVars(x_3, x_9, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkOptionalNode___closed__2;
x_15 = lean_array_push(x_14, x_4);
x_16 = l_Lean_Elab_Term_mkLambda(x_3, x_15, x_12, x_5, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
x_8 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_instantiateMVars(x_3, x_9, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_mkLet(x_3, x_4, x_12, x_5, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Parser_Term_let___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decl");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___closed__1;
x_2 = l_Lean_Elab_Term_elabLetDeclAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed), 6, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_1);
lean_inc(x_9);
x_12 = l_Lean_Elab_Term_elabBinders___rarg(x_3, x_11, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
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
x_35 = l_Lean_Elab_Term_getOptions(x_9, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_39 = l_Lean_checkTraceOption(x_36, x_38);
lean_dec(x_36);
if (x_39 == 0)
{
x_17 = x_37;
goto block_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_2);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_41 = l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__7;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_15);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_15);
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__8;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_16);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_16);
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Term_logTrace(x_38, x_1, x_48, x_9, x_37);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_17 = x_50;
goto block_34;
}
block_34:
{
if (x_8 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__2___boxed), 6, 3);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_7);
lean_closure_set(x_18, 2, x_1);
x_19 = 0;
x_20 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_2, x_19, x_15, x_18, x_9, x_17);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkApp(x_22, x_16);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = l_Lean_mkApp(x_24, x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
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
else
{
lean_object* x_32; lean_object* x_33; 
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__3___boxed), 6, 3);
lean_closure_set(x_32, 0, x_6);
lean_closure_set(x_32, 1, x_7);
lean_closure_set(x_32, 2, x_1);
x_33 = l_Lean_Elab_Term_withLetDecl___rarg(x_1, x_2, x_15, x_16, x_32, x_9, x_17);
lean_dec(x_1);
return x_33;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabLetDeclAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabLetDeclAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
x_12 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabLetDecl___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_268; uint8_t x_269; 
x_268 = l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_inc(x_1);
x_269 = l_Lean_Syntax_isOfKind(x_1, x_268);
if (x_269 == 0)
{
uint8_t x_270; 
x_270 = 0;
x_5 = x_270;
goto block_267;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = l_Lean_Syntax_getArgs(x_1);
x_272 = lean_array_get_size(x_271);
lean_dec(x_271);
x_273 = lean_unsigned_to_nat(4u);
x_274 = lean_nat_dec_eq(x_272, x_273);
lean_dec(x_272);
x_5 = x_274;
goto block_267;
}
block_267:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_260; uint8_t x_261; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_260 = l_Lean_Parser_Term_letIdDecl___closed__2;
lean_inc(x_8);
x_261 = l_Lean_Syntax_isOfKind(x_8, x_260);
if (x_261 == 0)
{
uint8_t x_262; 
x_262 = 0;
x_9 = x_262;
goto block_259;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = l_Lean_Syntax_getArgs(x_8);
x_264 = lean_array_get_size(x_263);
lean_dec(x_263);
x_265 = lean_unsigned_to_nat(5u);
x_266 = lean_nat_dec_eq(x_264, x_265);
lean_dec(x_264);
x_9 = x_266;
goto block_259;
}
block_259:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_8, x_11);
x_13 = l_Lean_identKind___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_214; uint8_t x_215; 
x_15 = l_Lean_Syntax_getArg(x_8, x_7);
x_214 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_215 = l_Lean_Syntax_isOfKind(x_15, x_214);
if (x_215 == 0)
{
uint8_t x_216; 
lean_dec(x_15);
x_216 = 0;
x_16 = x_216;
goto block_213;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_218 = lean_array_get_size(x_217);
lean_dec(x_217);
x_219 = lean_nat_dec_eq(x_218, x_11);
lean_dec(x_218);
x_16 = x_219;
goto block_213;
}
block_213:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_121; uint8_t x_122; uint8_t x_123; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_8, x_18);
x_121 = l_Lean_nullKind___closed__2;
lean_inc(x_19);
x_122 = l_Lean_Syntax_isOfKind(x_19, x_121);
if (x_122 == 0)
{
uint8_t x_209; 
x_209 = 0;
x_123 = x_209;
goto block_208;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = l_Lean_Syntax_getArgs(x_19);
x_211 = lean_array_get_size(x_210);
lean_dec(x_210);
x_212 = lean_nat_dec_eq(x_211, x_11);
lean_dec(x_211);
x_123 = x_212;
goto block_208;
}
block_120:
{
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_114; uint8_t x_115; 
x_22 = l_Lean_Syntax_getArg(x_19, x_11);
lean_dec(x_19);
x_114 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_22);
x_115 = l_Lean_Syntax_isOfKind(x_22, x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = 0;
x_23 = x_116;
goto block_113;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = l_Lean_Syntax_getArgs(x_22);
x_118 = lean_array_get_size(x_117);
lean_dec(x_117);
x_119 = lean_nat_dec_eq(x_118, x_18);
lean_dec(x_118);
x_23 = x_119;
goto block_113;
}
block_113:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_25 = l_Lean_Syntax_getArg(x_22, x_7);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_8, x_26);
lean_dec(x_8);
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_getMainModule___rarg(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_38 = l_Lean_addMacroScope(x_34, x_37, x_31);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_39);
x_42 = l_Array_empty___closed__1;
x_43 = lean_array_push(x_42, x_41);
x_44 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_47 = lean_array_push(x_46, x_25);
x_48 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_42, x_49);
x_51 = l_Lean_nullKind___closed__2;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_45);
x_53 = lean_array_push(x_45, x_52);
x_54 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_27);
x_57 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_60 = lean_array_push(x_59, x_58);
x_61 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_62 = lean_array_push(x_60, x_61);
x_63 = l_Lean_mkTermIdFromIdent___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
x_65 = lean_array_push(x_42, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_array_push(x_68, x_44);
x_70 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_71 = lean_array_push(x_69, x_70);
x_72 = lean_array_push(x_71, x_44);
x_73 = lean_array_push(x_42, x_12);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_51);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_42, x_74);
x_76 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_array_push(x_77, x_29);
x_79 = l_Lean_Parser_Term_matchAlt___closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_42, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_51);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_push(x_72, x_82);
x_84 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_array_push(x_62, x_85);
x_87 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_3, 8);
lean_inc(x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_3, 8, x_92);
x_93 = 1;
x_94 = l_Lean_Elab_Term_elabTerm(x_88, x_2, x_93, x_3, x_35);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = lean_ctor_get(x_3, 2);
x_98 = lean_ctor_get(x_3, 3);
x_99 = lean_ctor_get(x_3, 4);
x_100 = lean_ctor_get(x_3, 5);
x_101 = lean_ctor_get(x_3, 6);
x_102 = lean_ctor_get(x_3, 7);
x_103 = lean_ctor_get(x_3, 8);
x_104 = lean_ctor_get(x_3, 9);
x_105 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_106 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_107 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_3);
lean_inc(x_88);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_88);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
x_110 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_96);
lean_ctor_set(x_110, 2, x_97);
lean_ctor_set(x_110, 3, x_98);
lean_ctor_set(x_110, 4, x_99);
lean_ctor_set(x_110, 5, x_100);
lean_ctor_set(x_110, 6, x_101);
lean_ctor_set(x_110, 7, x_102);
lean_ctor_set(x_110, 8, x_109);
lean_ctor_set(x_110, 9, x_104);
lean_ctor_set_uint8(x_110, sizeof(void*)*10, x_105);
lean_ctor_set_uint8(x_110, sizeof(void*)*10 + 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*10 + 2, x_107);
x_111 = 1;
x_112 = l_Lean_Elab_Term_elabTerm(x_88, x_2, x_111, x_110, x_35);
return x_112;
}
}
}
}
}
block_208:
{
if (x_123 == 0)
{
if (x_122 == 0)
{
uint8_t x_124; 
x_124 = 0;
x_20 = x_124;
goto block_120;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Lean_Syntax_getArgs(x_19);
x_126 = lean_array_get_size(x_125);
lean_dec(x_125);
x_127 = lean_nat_dec_eq(x_126, x_7);
lean_dec(x_126);
x_20 = x_127;
goto block_120;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_19);
x_128 = lean_unsigned_to_nat(4u);
x_129 = l_Lean_Syntax_getArg(x_8, x_128);
lean_dec(x_8);
x_130 = lean_unsigned_to_nat(3u);
x_131 = l_Lean_Syntax_getArg(x_1, x_130);
x_132 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Elab_Term_getMainModule___rarg(x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_box(0);
x_139 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_140 = l_Lean_addMacroScope(x_136, x_139, x_133);
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_140);
lean_ctor_set(x_143, 3, x_141);
x_144 = l_Array_empty___closed__1;
x_145 = lean_array_push(x_144, x_143);
x_146 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
x_147 = lean_array_push(x_145, x_146);
lean_inc(x_147);
x_148 = lean_array_push(x_147, x_146);
x_149 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_150 = lean_array_push(x_148, x_149);
x_151 = lean_array_push(x_150, x_129);
x_152 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_155 = lean_array_push(x_154, x_153);
x_156 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_157 = lean_array_push(x_155, x_156);
x_158 = l_Lean_mkTermIdFromIdent___closed__2;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_147);
x_160 = lean_array_push(x_144, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_121);
lean_ctor_set(x_161, 1, x_160);
x_162 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_163 = lean_array_push(x_162, x_161);
x_164 = lean_array_push(x_163, x_146);
x_165 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_166 = lean_array_push(x_164, x_165);
x_167 = lean_array_push(x_166, x_146);
x_168 = lean_array_push(x_144, x_12);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_121);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_144, x_169);
x_171 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_172 = lean_array_push(x_170, x_171);
x_173 = lean_array_push(x_172, x_131);
x_174 = l_Lean_Parser_Term_matchAlt___closed__2;
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_array_push(x_144, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_121);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_array_push(x_167, x_177);
x_179 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_array_push(x_157, x_180);
x_182 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = !lean_is_exclusive(x_3);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_3, 8);
lean_inc(x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_183);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_3, 8, x_187);
x_188 = 1;
x_189 = l_Lean_Elab_Term_elabTerm(x_183, x_2, x_188, x_3, x_137);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_190 = lean_ctor_get(x_3, 0);
x_191 = lean_ctor_get(x_3, 1);
x_192 = lean_ctor_get(x_3, 2);
x_193 = lean_ctor_get(x_3, 3);
x_194 = lean_ctor_get(x_3, 4);
x_195 = lean_ctor_get(x_3, 5);
x_196 = lean_ctor_get(x_3, 6);
x_197 = lean_ctor_get(x_3, 7);
x_198 = lean_ctor_get(x_3, 8);
x_199 = lean_ctor_get(x_3, 9);
x_200 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_201 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_202 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_3);
lean_inc(x_183);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_183);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
x_205 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_205, 0, x_190);
lean_ctor_set(x_205, 1, x_191);
lean_ctor_set(x_205, 2, x_192);
lean_ctor_set(x_205, 3, x_193);
lean_ctor_set(x_205, 4, x_194);
lean_ctor_set(x_205, 5, x_195);
lean_ctor_set(x_205, 6, x_196);
lean_ctor_set(x_205, 7, x_197);
lean_ctor_set(x_205, 8, x_204);
lean_ctor_set(x_205, 9, x_199);
lean_ctor_set_uint8(x_205, sizeof(void*)*10, x_200);
lean_ctor_set_uint8(x_205, sizeof(void*)*10 + 1, x_201);
lean_ctor_set_uint8(x_205, sizeof(void*)*10 + 2, x_202);
x_206 = 1;
x_207 = l_Lean_Elab_Term_elabTerm(x_183, x_2, x_206, x_205, x_137);
return x_207;
}
}
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_243; uint8_t x_244; 
x_220 = l_Lean_Syntax_getArg(x_8, x_7);
x_221 = lean_unsigned_to_nat(2u);
x_222 = l_Lean_Syntax_getArg(x_8, x_221);
x_243 = l_Lean_nullKind___closed__2;
lean_inc(x_222);
x_244 = l_Lean_Syntax_isOfKind(x_222, x_243);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = 0;
x_223 = x_245;
goto block_242;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = l_Lean_Syntax_getArgs(x_222);
x_247 = lean_array_get_size(x_246);
lean_dec(x_246);
x_248 = lean_nat_dec_eq(x_247, x_11);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = lean_nat_dec_eq(x_247, x_7);
lean_dec(x_247);
x_223 = x_249;
goto block_242;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
lean_dec(x_247);
lean_dec(x_222);
x_250 = lean_unsigned_to_nat(4u);
x_251 = l_Lean_Syntax_getArg(x_8, x_250);
lean_dec(x_8);
x_252 = lean_unsigned_to_nat(3u);
x_253 = l_Lean_Syntax_getArg(x_1, x_252);
x_254 = l_Lean_Syntax_getArgs(x_220);
lean_dec(x_220);
x_255 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_256 = l_Lean_mkHole(x_1);
x_257 = 1;
x_258 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_255, x_254, x_256, x_251, x_253, x_2, x_257, x_3, x_4);
lean_dec(x_254);
return x_258;
}
}
block_242:
{
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = l_Lean_Syntax_getArg(x_222, x_11);
lean_dec(x_222);
x_226 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_225);
x_227 = l_Lean_Syntax_isOfKind(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = l_Lean_Syntax_getArgs(x_225);
x_230 = lean_array_get_size(x_229);
lean_dec(x_229);
x_231 = lean_nat_dec_eq(x_230, x_221);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_232 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
x_233 = l_Lean_Syntax_getArg(x_225, x_7);
lean_dec(x_225);
x_234 = lean_unsigned_to_nat(4u);
x_235 = l_Lean_Syntax_getArg(x_8, x_234);
lean_dec(x_8);
x_236 = lean_unsigned_to_nat(3u);
x_237 = l_Lean_Syntax_getArg(x_1, x_236);
x_238 = l_Lean_Syntax_getArgs(x_220);
lean_dec(x_220);
x_239 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_240 = 1;
x_241 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_239, x_238, x_233, x_235, x_237, x_2, x_240, x_3, x_4);
lean_dec(x_238);
return x_241;
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDecl), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetBangDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetBangDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_elabLetBangDecl___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabLetBangDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_268; uint8_t x_269; 
x_268 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
lean_inc(x_1);
x_269 = l_Lean_Syntax_isOfKind(x_1, x_268);
if (x_269 == 0)
{
uint8_t x_270; 
x_270 = 0;
x_5 = x_270;
goto block_267;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = l_Lean_Syntax_getArgs(x_1);
x_272 = lean_array_get_size(x_271);
lean_dec(x_271);
x_273 = lean_unsigned_to_nat(4u);
x_274 = lean_nat_dec_eq(x_272, x_273);
lean_dec(x_272);
x_5 = x_274;
goto block_267;
}
block_267:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_260; uint8_t x_261; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_260 = l_Lean_Parser_Term_letIdDecl___closed__2;
lean_inc(x_8);
x_261 = l_Lean_Syntax_isOfKind(x_8, x_260);
if (x_261 == 0)
{
uint8_t x_262; 
x_262 = 0;
x_9 = x_262;
goto block_259;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = l_Lean_Syntax_getArgs(x_8);
x_264 = lean_array_get_size(x_263);
lean_dec(x_263);
x_265 = lean_unsigned_to_nat(5u);
x_266 = lean_nat_dec_eq(x_264, x_265);
lean_dec(x_264);
x_9 = x_266;
goto block_259;
}
block_259:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_8, x_11);
x_13 = l_Lean_identKind___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_214; uint8_t x_215; 
x_15 = l_Lean_Syntax_getArg(x_8, x_7);
x_214 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_215 = l_Lean_Syntax_isOfKind(x_15, x_214);
if (x_215 == 0)
{
uint8_t x_216; 
lean_dec(x_15);
x_216 = 0;
x_16 = x_216;
goto block_213;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_218 = lean_array_get_size(x_217);
lean_dec(x_217);
x_219 = lean_nat_dec_eq(x_218, x_11);
lean_dec(x_218);
x_16 = x_219;
goto block_213;
}
block_213:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_121; uint8_t x_122; uint8_t x_123; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_8, x_18);
x_121 = l_Lean_nullKind___closed__2;
lean_inc(x_19);
x_122 = l_Lean_Syntax_isOfKind(x_19, x_121);
if (x_122 == 0)
{
uint8_t x_209; 
x_209 = 0;
x_123 = x_209;
goto block_208;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = l_Lean_Syntax_getArgs(x_19);
x_211 = lean_array_get_size(x_210);
lean_dec(x_210);
x_212 = lean_nat_dec_eq(x_211, x_11);
lean_dec(x_211);
x_123 = x_212;
goto block_208;
}
block_120:
{
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_114; uint8_t x_115; 
x_22 = l_Lean_Syntax_getArg(x_19, x_11);
lean_dec(x_19);
x_114 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_22);
x_115 = l_Lean_Syntax_isOfKind(x_22, x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = 0;
x_23 = x_116;
goto block_113;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = l_Lean_Syntax_getArgs(x_22);
x_118 = lean_array_get_size(x_117);
lean_dec(x_117);
x_119 = lean_nat_dec_eq(x_118, x_18);
lean_dec(x_118);
x_23 = x_119;
goto block_113;
}
block_113:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_25 = l_Lean_Syntax_getArg(x_22, x_7);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_8, x_26);
lean_dec(x_8);
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_getMainModule___rarg(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_38 = l_Lean_addMacroScope(x_34, x_37, x_31);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_39);
x_42 = l_Array_empty___closed__1;
x_43 = lean_array_push(x_42, x_41);
x_44 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_47 = lean_array_push(x_46, x_25);
x_48 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_42, x_49);
x_51 = l_Lean_nullKind___closed__2;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_45);
x_53 = lean_array_push(x_45, x_52);
x_54 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_27);
x_57 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Elab_Term_elabLetBangDecl___closed__2;
x_60 = lean_array_push(x_59, x_58);
x_61 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_62 = lean_array_push(x_60, x_61);
x_63 = l_Lean_mkTermIdFromIdent___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
x_65 = lean_array_push(x_42, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_array_push(x_68, x_44);
x_70 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_71 = lean_array_push(x_69, x_70);
x_72 = lean_array_push(x_71, x_44);
x_73 = lean_array_push(x_42, x_12);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_51);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_42, x_74);
x_76 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_array_push(x_77, x_29);
x_79 = l_Lean_Parser_Term_matchAlt___closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_42, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_51);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_push(x_72, x_82);
x_84 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_array_push(x_62, x_85);
x_87 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_3, 8);
lean_inc(x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_3, 8, x_92);
x_93 = 1;
x_94 = l_Lean_Elab_Term_elabTerm(x_88, x_2, x_93, x_3, x_35);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = lean_ctor_get(x_3, 2);
x_98 = lean_ctor_get(x_3, 3);
x_99 = lean_ctor_get(x_3, 4);
x_100 = lean_ctor_get(x_3, 5);
x_101 = lean_ctor_get(x_3, 6);
x_102 = lean_ctor_get(x_3, 7);
x_103 = lean_ctor_get(x_3, 8);
x_104 = lean_ctor_get(x_3, 9);
x_105 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_106 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_107 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_3);
lean_inc(x_88);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_88);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
x_110 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_96);
lean_ctor_set(x_110, 2, x_97);
lean_ctor_set(x_110, 3, x_98);
lean_ctor_set(x_110, 4, x_99);
lean_ctor_set(x_110, 5, x_100);
lean_ctor_set(x_110, 6, x_101);
lean_ctor_set(x_110, 7, x_102);
lean_ctor_set(x_110, 8, x_109);
lean_ctor_set(x_110, 9, x_104);
lean_ctor_set_uint8(x_110, sizeof(void*)*10, x_105);
lean_ctor_set_uint8(x_110, sizeof(void*)*10 + 1, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*10 + 2, x_107);
x_111 = 1;
x_112 = l_Lean_Elab_Term_elabTerm(x_88, x_2, x_111, x_110, x_35);
return x_112;
}
}
}
}
}
block_208:
{
if (x_123 == 0)
{
if (x_122 == 0)
{
uint8_t x_124; 
x_124 = 0;
x_20 = x_124;
goto block_120;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Lean_Syntax_getArgs(x_19);
x_126 = lean_array_get_size(x_125);
lean_dec(x_125);
x_127 = lean_nat_dec_eq(x_126, x_7);
lean_dec(x_126);
x_20 = x_127;
goto block_120;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_19);
x_128 = lean_unsigned_to_nat(4u);
x_129 = l_Lean_Syntax_getArg(x_8, x_128);
lean_dec(x_8);
x_130 = lean_unsigned_to_nat(3u);
x_131 = l_Lean_Syntax_getArg(x_1, x_130);
x_132 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Elab_Term_getMainModule___rarg(x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_box(0);
x_139 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_140 = l_Lean_addMacroScope(x_136, x_139, x_133);
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_140);
lean_ctor_set(x_143, 3, x_141);
x_144 = l_Array_empty___closed__1;
x_145 = lean_array_push(x_144, x_143);
x_146 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
x_147 = lean_array_push(x_145, x_146);
lean_inc(x_147);
x_148 = lean_array_push(x_147, x_146);
x_149 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_150 = lean_array_push(x_148, x_149);
x_151 = lean_array_push(x_150, x_129);
x_152 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_Elab_Term_elabLetBangDecl___closed__2;
x_155 = lean_array_push(x_154, x_153);
x_156 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_157 = lean_array_push(x_155, x_156);
x_158 = l_Lean_mkTermIdFromIdent___closed__2;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_147);
x_160 = lean_array_push(x_144, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_121);
lean_ctor_set(x_161, 1, x_160);
x_162 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2;
x_163 = lean_array_push(x_162, x_161);
x_164 = lean_array_push(x_163, x_146);
x_165 = l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4;
x_166 = lean_array_push(x_164, x_165);
x_167 = lean_array_push(x_166, x_146);
x_168 = lean_array_push(x_144, x_12);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_121);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_144, x_169);
x_171 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_172 = lean_array_push(x_170, x_171);
x_173 = lean_array_push(x_172, x_131);
x_174 = l_Lean_Parser_Term_matchAlt___closed__2;
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_array_push(x_144, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_121);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_array_push(x_167, x_177);
x_179 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_array_push(x_157, x_180);
x_182 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = !lean_is_exclusive(x_3);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_3, 8);
lean_inc(x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_183);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_3, 8, x_187);
x_188 = 1;
x_189 = l_Lean_Elab_Term_elabTerm(x_183, x_2, x_188, x_3, x_137);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_190 = lean_ctor_get(x_3, 0);
x_191 = lean_ctor_get(x_3, 1);
x_192 = lean_ctor_get(x_3, 2);
x_193 = lean_ctor_get(x_3, 3);
x_194 = lean_ctor_get(x_3, 4);
x_195 = lean_ctor_get(x_3, 5);
x_196 = lean_ctor_get(x_3, 6);
x_197 = lean_ctor_get(x_3, 7);
x_198 = lean_ctor_get(x_3, 8);
x_199 = lean_ctor_get(x_3, 9);
x_200 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_201 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_202 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_3);
lean_inc(x_183);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_183);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
x_205 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_205, 0, x_190);
lean_ctor_set(x_205, 1, x_191);
lean_ctor_set(x_205, 2, x_192);
lean_ctor_set(x_205, 3, x_193);
lean_ctor_set(x_205, 4, x_194);
lean_ctor_set(x_205, 5, x_195);
lean_ctor_set(x_205, 6, x_196);
lean_ctor_set(x_205, 7, x_197);
lean_ctor_set(x_205, 8, x_204);
lean_ctor_set(x_205, 9, x_199);
lean_ctor_set_uint8(x_205, sizeof(void*)*10, x_200);
lean_ctor_set_uint8(x_205, sizeof(void*)*10 + 1, x_201);
lean_ctor_set_uint8(x_205, sizeof(void*)*10 + 2, x_202);
x_206 = 1;
x_207 = l_Lean_Elab_Term_elabTerm(x_183, x_2, x_206, x_205, x_137);
return x_207;
}
}
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_243; uint8_t x_244; 
x_220 = l_Lean_Syntax_getArg(x_8, x_7);
x_221 = lean_unsigned_to_nat(2u);
x_222 = l_Lean_Syntax_getArg(x_8, x_221);
x_243 = l_Lean_nullKind___closed__2;
lean_inc(x_222);
x_244 = l_Lean_Syntax_isOfKind(x_222, x_243);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = 0;
x_223 = x_245;
goto block_242;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = l_Lean_Syntax_getArgs(x_222);
x_247 = lean_array_get_size(x_246);
lean_dec(x_246);
x_248 = lean_nat_dec_eq(x_247, x_11);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = lean_nat_dec_eq(x_247, x_7);
lean_dec(x_247);
x_223 = x_249;
goto block_242;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
lean_dec(x_247);
lean_dec(x_222);
x_250 = lean_unsigned_to_nat(4u);
x_251 = l_Lean_Syntax_getArg(x_8, x_250);
lean_dec(x_8);
x_252 = lean_unsigned_to_nat(3u);
x_253 = l_Lean_Syntax_getArg(x_1, x_252);
x_254 = l_Lean_Syntax_getArgs(x_220);
lean_dec(x_220);
x_255 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_256 = l_Lean_mkHole(x_1);
x_257 = 0;
x_258 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_255, x_254, x_256, x_251, x_253, x_2, x_257, x_3, x_4);
lean_dec(x_254);
return x_258;
}
}
block_242:
{
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = l_Lean_Syntax_getArg(x_222, x_11);
lean_dec(x_222);
x_226 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_225);
x_227 = l_Lean_Syntax_isOfKind(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = l_Lean_Syntax_getArgs(x_225);
x_230 = lean_array_get_size(x_229);
lean_dec(x_229);
x_231 = lean_nat_dec_eq(x_230, x_221);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_232 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
x_233 = l_Lean_Syntax_getArg(x_225, x_7);
lean_dec(x_225);
x_234 = lean_unsigned_to_nat(4u);
x_235 = l_Lean_Syntax_getArg(x_8, x_234);
lean_dec(x_8);
x_236 = lean_unsigned_to_nat(3u);
x_237 = l_Lean_Syntax_getArg(x_1, x_236);
x_238 = l_Lean_Syntax_getArgs(x_220);
lean_dec(x_220);
x_239 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_240 = 0;
x_241 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_239, x_238, x_233, x_235, x_237, x_2, x_240, x_3, x_4);
lean_dec(x_238);
return x_241;
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetBangDecl), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Binders_14__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabLetDeclAux___closed__1;
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
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Binders(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1);
l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__1 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__1);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__2 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__2);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__3 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__3);
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
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__1 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__1);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__2);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__3 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__3);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__4);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__5 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__5);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__6);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__7 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__7);
l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8 = _init_l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_4__expandBinderModifier___closed__8);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabArrow___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___lambda__1___closed__1);
l_Lean_Elab_Term_elabArrow___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___lambda__1___closed__2);
l_Lean_Elab_Term_elabArrow___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___lambda__1___closed__3);
l_Lean_Elab_Term_elabArrow___lambda__1___closed__4 = _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___lambda__1___closed__4);
l_Lean_Elab_Term_elabArrow___lambda__1___closed__5 = _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___lambda__1___closed__5);
l_Lean_Elab_Term_elabArrow___closed__1 = _init_l_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__1 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__1);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__2);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__3 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__3);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__4);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__5 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__5);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__6 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__6);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__7);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__8 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__8);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__9 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__9);
l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10 = _init_l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_10__expandFunBindersAux___main___closed__10);
l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__1 = _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__1);
l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__2 = _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__2);
l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3 = _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__3);
l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__4 = _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__4);
l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__5 = _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__5);
l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6 = _init_l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Binders_11__checkNoOptAutoParam___closed__6);
l___regBuiltinTermElab_Lean_Elab_Term_elabFun___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabFun___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabFun___closed__1);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabLetDeclAux___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__3);
l_Lean_Elab_Term_elabLetDecl___closed__1 = _init_l_Lean_Elab_Term_elabLetDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___closed__1);
l_Lean_Elab_Term_elabLetDecl___closed__2 = _init_l_Lean_Elab_Term_elabLetDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl___closed__1);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabLetDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabLetBangDecl___closed__1 = _init_l_Lean_Elab_Term_elabLetBangDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetBangDecl___closed__1);
l_Lean_Elab_Term_elabLetBangDecl___closed__2 = _init_l_Lean_Elab_Term_elabLetBangDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetBangDecl___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl___closed__1);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabLetBangDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Init_Lean_Elab_Binders_14__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
