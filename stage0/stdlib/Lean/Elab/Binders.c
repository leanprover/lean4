// Lean compiler output
// Module: Lean.Elab.Binders
// Imports: Init Lean.Elab.Term Lean.Elab.Quotation
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
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__12;
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_2__expandBinderIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__13;
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__12;
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__10;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Syntax_7__quoteName___main(lean_object*);
lean_object* l___private_Lean_Elab_Binders_5__getBinderIds(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1;
extern lean_object* l_Lean_List_format___rarg___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_18__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
lean_object* l___private_Lean_Elab_Binders_6__matchBinder(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_15__expandLetIdLhs___boxed(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_compileDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object*);
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_letDecl___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__10;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_3__expandOptIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_binderTactic___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object*);
lean_object* l_Lean_Elab_Term_mkLet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isSimpleTermId_x3f(lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Binders_15__expandLetIdLhs(lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__3;
extern lean_object* l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__5;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__2;
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshFVarId___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__9;
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__1;
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkEqNDRec___closed__6;
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__11;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__7;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetBangDecl(lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__10;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*);
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__21;
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
extern lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__5;
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_2__expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_13__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRelaxedId(lean_object*);
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__6;
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__2;
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Quotation_2__quoteSyntax___main___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Binders_6__matchBinder___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Binders_16__getMatchAltNumPatterns___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg(lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Lean_Elab_Term_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_Quotation_isAntiquot(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_3__expandOptIdent(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_String_HasQuote___closed__2;
lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__25;
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetBangDecl___closed__1;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_identKind;
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Elab_Term_elabFun___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_16__getMatchAltNumPatterns(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
extern lean_object* l_Lean_Parser_Term_letPatDecl___elambda__1___closed__2;
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4;
lean_object* lean_environment_main_module(lean_object*);
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__8;
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__4;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
lean_object* l_Lean_Syntax_isTermId_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__5;
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__5;
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__5;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__15;
extern lean_object* l_Lean_Parser_Term_letEqnsDecl___elambda__1___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__3;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_Quotation_isAntiquotSplice(lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetBangDecl(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
extern lean_object* l_Lean_Parser_Term_binderDefault___elambda__1___closed__2;
extern lean_object* l_Std_PersistentHashMap_Stats_toString___closed__5;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__22;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__7;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__9;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__4;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__7;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayToExpr___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__3;
lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Quotation_2__quoteSyntax___main___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_1__expandBinderType___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__7;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_1__expandBinderType(lean_object*);
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
lean_object* l___private_Lean_Elab_Binders_5__getBinderIds___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Lean_Elab_Binders_13__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l_Lean_Elab_Term_elabBinder(lean_object*);
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_1__expandBinderType(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Binders_1__expandBinderType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Binders_1__expandBinderType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_2__expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Binders_2__expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_2__expandBinderIdent(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Binders_3__expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Binders_3__expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_3__expandOptIdent(x_1, x_2, x_3);
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
x_63 = l_Lean_Elab_Term_throwErrorAt___rarg(x_20, x_62, x_15, x_16);
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
x_35 = l_Array_iterateMAux___main___at___private_Lean_Elab_Quotation_2__quoteSyntax___main___spec__1___closed__4;
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
x_40 = l_Array_iterateMAux___main___at___private_Lean_Elab_Quotation_2__quoteSyntax___main___spec__1___closed__3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_addParenHeuristic___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__5;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Std_PersistentHashMap_Stats_toString___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__6;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_structInst___elambda__1___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalic auto tactic, identifier is not allowed");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__12;
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
x_4 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
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
x_19 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__5;
x_20 = l_Lean_addMacroScope(x_17, x_19, x_14);
x_21 = lean_box(0);
x_22 = l_Lean_SourceInfo_inhabited___closed__1;
x_23 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__3;
x_24 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__7;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_29 = lean_array_push(x_27, x_28);
x_30 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_30);
x_31 = l_Lean_mkAppStx___closed__6;
x_32 = l_Lean_arrayToExpr___rarg___closed__2;
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_35 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(x_7, x_8, x_31, x_30, x_26, x_22, x_32, x_21, x_21, x_33, x_28, x_8, x_34, x_1, x_2, x_18);
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
x_44 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__12;
x_45 = l_Lean_addMacroScope(x_43, x_44, x_39);
x_46 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__10;
x_47 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__15;
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_22);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_array_push(x_26, x_48);
x_50 = lean_array_push(x_49, x_28);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_30);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_26, x_51);
x_53 = l___private_Lean_Syntax_7__quoteName___main(x_7);
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
x_62 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__12;
x_63 = l_Lean_addMacroScope(x_60, x_62, x_39);
x_64 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__10;
x_65 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__15;
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_22);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_63);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_array_push(x_26, x_66);
x_68 = lean_array_push(x_67, x_28);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_30);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_26, x_69);
x_71 = l___private_Lean_Syntax_7__quoteName___main(x_7);
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
x_89 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__5;
x_90 = l_Lean_addMacroScope(x_87, x_89, x_84);
x_91 = lean_box(0);
x_92 = l_Lean_SourceInfo_inhabited___closed__1;
x_93 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__3;
x_94 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__7;
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_94);
x_96 = l_Array_empty___closed__1;
x_97 = lean_array_push(x_96, x_95);
x_98 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_99 = lean_array_push(x_97, x_98);
x_100 = l_Lean_mkTermIdFromIdent___closed__2;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_mkAppStx___closed__6;
x_103 = l_Lean_arrayToExpr___rarg___closed__2;
x_104 = l_Lean_nullKind___closed__2;
x_105 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_106 = l_Array_iterateMAux___main___at_Lean_Elab_Term_quoteAutoTactic___main___spec__1(x_7, x_8, x_102, x_100, x_96, x_92, x_103, x_91, x_91, x_104, x_98, x_8, x_105, x_101, x_2, x_88);
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
x_116 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__12;
x_117 = l_Lean_addMacroScope(x_113, x_116, x_110);
x_118 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__10;
x_119 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__15;
x_120 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_120, 0, x_92);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_array_push(x_96, x_120);
x_122 = lean_array_push(x_121, x_98);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_100);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_push(x_96, x_123);
x_125 = l___private_Lean_Syntax_7__quoteName___main(x_7);
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
x_138 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1, x_137, x_2, x_3);
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
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__22;
x_149 = l_Lean_addMacroScope(x_147, x_148, x_143);
x_150 = l_Lean_SourceInfo_inhabited___closed__1;
x_151 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__21;
x_152 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__25;
x_153 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_149);
lean_ctor_set(x_153, 3, x_152);
x_154 = l_Array_empty___closed__1;
x_155 = lean_array_push(x_154, x_153);
x_156 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_157 = lean_array_push(x_155, x_156);
x_158 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_157);
lean_ctor_set(x_1, 0, x_158);
x_159 = lean_array_push(x_154, x_1);
x_160 = l_Lean_mkStxStrLit(x_140, x_150);
x_161 = l_Lean_mkOptionalNode___closed__2;
x_162 = lean_array_push(x_161, x_160);
x_163 = l_Lean_String_HasQuote___closed__2;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__10;
x_166 = lean_array_push(x_165, x_164);
x_167 = l_Lean_nullKind___closed__2;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_push(x_159, x_168);
x_170 = l_Lean_mkAppStx___closed__8;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_145, 0, x_171);
return x_145;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_172 = lean_ctor_get(x_145, 0);
x_173 = lean_ctor_get(x_145, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_145);
x_174 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__22;
x_175 = l_Lean_addMacroScope(x_172, x_174, x_143);
x_176 = l_Lean_SourceInfo_inhabited___closed__1;
x_177 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__21;
x_178 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__25;
x_179 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_175);
lean_ctor_set(x_179, 3, x_178);
x_180 = l_Array_empty___closed__1;
x_181 = lean_array_push(x_180, x_179);
x_182 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_183 = lean_array_push(x_181, x_182);
x_184 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_183);
lean_ctor_set(x_1, 0, x_184);
x_185 = lean_array_push(x_180, x_1);
x_186 = l_Lean_mkStxStrLit(x_140, x_176);
x_187 = l_Lean_mkOptionalNode___closed__2;
x_188 = lean_array_push(x_187, x_186);
x_189 = l_Lean_String_HasQuote___closed__2;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__10;
x_192 = lean_array_push(x_191, x_190);
x_193 = l_Lean_nullKind___closed__2;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_array_push(x_185, x_194);
x_196 = l_Lean_mkAppStx___closed__8;
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_173);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_199 = lean_ctor_get(x_1, 1);
lean_inc(x_199);
lean_dec(x_1);
x_200 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
lean_dec(x_2);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Elab_Term_getMainModule___rarg(x_202);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__22;
x_208 = l_Lean_addMacroScope(x_204, x_207, x_201);
x_209 = l_Lean_SourceInfo_inhabited___closed__1;
x_210 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__21;
x_211 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__25;
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
lean_ctor_set(x_212, 2, x_208);
lean_ctor_set(x_212, 3, x_211);
x_213 = l_Array_empty___closed__1;
x_214 = lean_array_push(x_213, x_212);
x_215 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_216 = lean_array_push(x_214, x_215);
x_217 = l_Lean_mkTermIdFromIdent___closed__2;
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_array_push(x_213, x_218);
x_220 = l_Lean_mkStxStrLit(x_199, x_209);
x_221 = l_Lean_mkOptionalNode___closed__2;
x_222 = lean_array_push(x_221, x_220);
x_223 = l_Lean_String_HasQuote___closed__2;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__10;
x_226 = lean_array_push(x_225, x_224);
x_227 = l_Lean_nullKind___closed__2;
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_array_push(x_219, x_228);
x_230 = l_Lean_mkAppStx___closed__8;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
if (lean_is_scalar(x_206)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_206;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_205);
return x_232;
}
}
default: 
{
lean_object* x_233; lean_object* x_234; 
x_233 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__13;
x_234 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1, x_233, x_2, x_3);
lean_dec(x_1);
return x_234;
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
x_2 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe___closed__1;
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
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
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
x_9 = lean_ctor_get(x_2, 8);
lean_dec(x_9);
lean_ctor_set(x_2, 8, x_5);
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
x_27 = l_Lean_Elab_Term_instantiateMVars(x_25, x_2, x_26);
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
x_59 = l_Lean_Elab_Term_logTrace(x_56, x_58, x_2, x_55);
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
x_37 = l_Lean_Elab_Term_addDecl(x_36, x_2, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Term_compileDecl(x_36, x_2, x_38);
lean_dec(x_36);
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
x_73 = lean_ctor_get(x_2, 4);
x_74 = lean_ctor_get(x_2, 5);
x_75 = lean_ctor_get(x_2, 6);
x_76 = lean_ctor_get(x_2, 7);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_78 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_80 = lean_ctor_get(x_2, 9);
lean_inc(x_80);
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
lean_ctor_set(x_81, 8, x_5);
lean_ctor_set(x_81, 9, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*10, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 1, x_78);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 2, x_79);
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
x_99 = l_Lean_Elab_Term_instantiateMVars(x_97, x_81, x_98);
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
x_130 = l_Lean_Elab_Term_logTrace(x_127, x_129, x_81, x_126);
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
x_109 = l_Lean_Elab_Term_addDecl(x_108, x_81, x_102);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_Elab_Term_compileDecl(x_108, x_81, x_110);
lean_dec(x_108);
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
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
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
x_157 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_158 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_159 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_160 = lean_ctor_get(x_2, 9);
lean_inc(x_160);
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
lean_ctor_set(x_162, 8, x_145);
lean_ctor_set(x_162, 9, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*10, x_157);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 1, x_158);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 2, x_159);
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
x_180 = l_Lean_Elab_Term_instantiateMVars(x_178, x_162, x_179);
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
x_211 = l_Lean_Elab_Term_logTrace(x_208, x_210, x_162, x_207);
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
x_190 = l_Lean_Elab_Term_addDecl(x_189, x_162, x_183);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_Elab_Term_compileDecl(x_189, x_162, x_191);
lean_dec(x_189);
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
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__3() {
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
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__7() {
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
lean_object* _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_25 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_26 = l_Lean_addMacroScope(x_24, x_25, x_20);
x_27 = l_Lean_SourceInfo_inhabited___closed__1;
x_28 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2;
x_29 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4;
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Array_empty___closed__1;
x_32 = lean_array_push(x_31, x_30);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
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
x_48 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_49 = l_Lean_addMacroScope(x_46, x_48, x_20);
x_50 = l_Lean_SourceInfo_inhabited___closed__1;
x_51 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2;
x_52 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4;
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_52);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
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
x_82 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_83 = l_Lean_addMacroScope(x_81, x_82, x_77);
x_84 = l_Lean_SourceInfo_inhabited___closed__1;
x_85 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6;
x_86 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8;
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_86);
x_88 = l_Array_empty___closed__1;
x_89 = lean_array_push(x_88, x_87);
x_90 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
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
x_104 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_105 = l_Lean_addMacroScope(x_102, x_104, x_77);
x_106 = l_Lean_SourceInfo_inhabited___closed__1;
x_107 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6;
x_108 = l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8;
x_109 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_105);
lean_ctor_set(x_109, 3, x_108);
x_110 = l_Array_empty___closed__1;
x_111 = lean_array_push(x_110, x_109);
x_112 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
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
lean_object* l___private_Lean_Elab_Binders_4__expandBinderModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Binders_4__expandBinderModifier(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier or `_` expected");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_12);
x_13 = l_Lean_Syntax_getKind(x_12);
x_14 = l_Lean_identKind;
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_mkHole___closed__2;
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_mkTermIdFromIdent___closed__2;
x_19 = lean_name_eq(x_13, x_18);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_1);
x_20 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3;
x_21 = l_Lean_Elab_Term_throwErrorAt___rarg(x_12, x_20, x_3, x_4);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Lean_Syntax_getArgs(x_12);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_1);
x_30 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3;
x_31 = l_Lean_Elab_Term_throwErrorAt___rarg(x_12, x_30, x_3, x_4);
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Lean_Syntax_getArg(x_12, x_36);
x_38 = l_Lean_Syntax_isNone(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_1);
x_39 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3;
x_40 = l_Lean_Elab_Term_throwErrorAt___rarg(x_12, x_39, x_3, x_4);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_Syntax_getArg(x_12, x_10);
lean_dec(x_12);
x_46 = lean_nat_add(x_1, x_36);
x_47 = x_45;
x_48 = lean_array_fset(x_11, x_1, x_47);
lean_dec(x_1);
x_1 = x_46;
x_2 = x_48;
goto _start;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_1, x_50);
x_52 = x_12;
x_53 = lean_array_fset(x_11, x_1, x_52);
lean_dec(x_1);
x_1 = x_51;
x_2 = x_53;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_1, x_55);
x_57 = x_12;
x_58 = lean_array_fset(x_11, x_1, x_57);
lean_dec(x_1);
x_1 = x_56;
x_2 = x_58;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_5__getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = x_4;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = x_7;
x_9 = lean_apply_2(x_8, x_2, x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Binders_5__getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_5__getBinderIds(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
x_14 = l___private_Lean_Elab_Binders_2__expandBinderIdent(x_13, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = x_18;
x_22 = lean_array_fset(x_12, x_2, x_21);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_22;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
x_14 = l___private_Lean_Elab_Binders_2__expandBinderIdent(x_13, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = x_18;
x_22 = lean_array_fset(x_12, x_2, x_21);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_22;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
x_14 = l___private_Lean_Elab_Binders_2__expandBinderIdent(x_13, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = x_18;
x_22 = lean_array_fset(x_12, x_2, x_21);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_22;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Binders_6__matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_18 = l___private_Lean_Elab_Binders_3__expandOptIdent(x_17, x_2, x_3);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Syntax_inhabited;
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_array_get(x_36, x_5, x_37);
lean_inc(x_2);
x_39 = l___private_Lean_Elab_Binders_5__getBinderIds(x_38, x_2, x_3);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_array_get(x_36, x_5, x_42);
x_44 = l___private_Lean_Elab_Binders_1__expandBinderType(x_43);
lean_dec(x_43);
x_45 = x_40;
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__1___boxed), 5, 3);
lean_closure_set(x_47, 0, x_44);
lean_closure_set(x_47, 1, x_46);
lean_closure_set(x_47, 2, x_45);
x_48 = x_47;
x_49 = lean_apply_2(x_48, x_2, x_41);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = l_Lean_Syntax_inhabited;
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_array_get(x_54, x_5, x_55);
lean_inc(x_2);
x_57 = l___private_Lean_Elab_Binders_5__getBinderIds(x_56, x_2, x_3);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_array_get(x_54, x_5, x_60);
x_62 = l___private_Lean_Elab_Binders_1__expandBinderType(x_61);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_array_get(x_54, x_5, x_63);
lean_inc(x_2);
x_65 = l___private_Lean_Elab_Binders_4__expandBinderModifier(x_62, x_64, x_2, x_59);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = x_58;
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__2___boxed), 5, 3);
lean_closure_set(x_70, 0, x_66);
lean_closure_set(x_70, 1, x_69);
lean_closure_set(x_70, 2, x_68);
x_71 = x_70;
x_72 = lean_apply_2(x_71, x_2, x_67);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_58);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_65);
if (x_73 == 0)
{
return x_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_65, 0);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_65);
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
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_57);
if (x_77 == 0)
{
return x_57;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_57, 0);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_57);
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
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Lean_Syntax_inhabited;
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get(x_81, x_5, x_82);
lean_inc(x_2);
x_84 = l___private_Lean_Elab_Binders_5__getBinderIds(x_83, x_2, x_3);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_mkHole(x_1);
x_88 = x_85;
x_89 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__3___boxed), 5, 3);
lean_closure_set(x_89, 0, x_87);
lean_closure_set(x_89, 1, x_82);
lean_closure_set(x_89, 2, x_88);
x_90 = x_89;
x_91 = lean_apply_2(x_90, x_2, x_86);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_84);
if (x_92 == 0)
{
return x_84;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_84, 0);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_84);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_2);
x_96 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_96;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_6__matchBinder___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_6__matchBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_6__matchBinder(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 9);
x_18 = l_Lean_Elab_replaceRef(x_14, x_17);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_6, 9, x_18);
lean_inc(x_6);
x_22 = l_Lean_Elab_Term_elabType(x_14, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_mkFVar(x_26);
lean_inc(x_28);
x_29 = lean_array_push(x_3, x_28);
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
x_31 = l_Lean_Syntax_getId(x_30);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_23);
x_33 = lean_local_ctx_mk_local_decl(x_4, x_26, x_31, x_23, x_32);
lean_inc(x_6);
x_34 = l_Lean_Elab_Term_isClass(x_23, x_6, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_2, x_37);
lean_dec(x_2);
x_2 = x_38;
x_3 = x_29;
x_4 = x_33;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_28);
x_45 = lean_array_push(x_5, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_2, x_46);
lean_dec(x_2);
x_2 = x_47;
x_3 = x_29;
x_4 = x_33;
x_5 = x_45;
x_7 = x_43;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
return x_22;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_22, 0);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_16, 0);
x_58 = lean_ctor_get(x_16, 3);
x_59 = lean_ctor_get(x_16, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_4);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_4);
lean_ctor_set(x_60, 2, x_5);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_6, 9, x_18);
lean_ctor_set(x_6, 0, x_60);
lean_inc(x_6);
x_61 = l_Lean_Elab_Term_elabType(x_14, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_65);
x_67 = l_Lean_mkFVar(x_65);
lean_inc(x_67);
x_68 = lean_array_push(x_3, x_67);
x_69 = lean_ctor_get(x_13, 0);
lean_inc(x_69);
x_70 = l_Lean_Syntax_getId(x_69);
lean_dec(x_69);
x_71 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_62);
x_72 = lean_local_ctx_mk_local_decl(x_4, x_65, x_70, x_62, x_71);
lean_inc(x_6);
x_73 = l_Lean_Elab_Term_isClass(x_62, x_6, x_66);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_67);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_2, x_76);
lean_dec(x_2);
x_2 = x_77;
x_3 = x_68;
x_4 = x_72;
x_7 = x_75;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
lean_dec(x_74);
x_81 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_79);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_67);
x_84 = lean_array_push(x_5, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_2, x_85);
lean_dec(x_2);
x_2 = x_86;
x_3 = x_68;
x_4 = x_72;
x_5 = x_84;
x_7 = x_82;
goto _start;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_88 = lean_ctor_get(x_73, 0);
lean_inc(x_88);
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
lean_dec(x_6);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_ctor_get(x_61, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_61, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_94 = x_61;
} else {
 lean_dec_ref(x_61);
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
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_96 = lean_ctor_get(x_6, 0);
x_97 = lean_ctor_get(x_6, 1);
x_98 = lean_ctor_get(x_6, 2);
x_99 = lean_ctor_get(x_6, 3);
x_100 = lean_ctor_get(x_6, 4);
x_101 = lean_ctor_get(x_6, 5);
x_102 = lean_ctor_get(x_6, 6);
x_103 = lean_ctor_get(x_6, 7);
x_104 = lean_ctor_get(x_6, 8);
x_105 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_106 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_107 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_108 = lean_ctor_get(x_6, 9);
lean_inc(x_108);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_6);
x_109 = l_Lean_Elab_replaceRef(x_14, x_108);
lean_dec(x_108);
x_110 = lean_ctor_get(x_96, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_96, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_96, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 x_113 = x_96;
} else {
 lean_dec_ref(x_96);
 x_113 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 5, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_4);
lean_ctor_set(x_114, 2, x_5);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set(x_114, 4, x_112);
x_115 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_97);
lean_ctor_set(x_115, 2, x_98);
lean_ctor_set(x_115, 3, x_99);
lean_ctor_set(x_115, 4, x_100);
lean_ctor_set(x_115, 5, x_101);
lean_ctor_set(x_115, 6, x_102);
lean_ctor_set(x_115, 7, x_103);
lean_ctor_set(x_115, 8, x_104);
lean_ctor_set(x_115, 9, x_109);
lean_ctor_set_uint8(x_115, sizeof(void*)*10, x_105);
lean_ctor_set_uint8(x_115, sizeof(void*)*10 + 1, x_106);
lean_ctor_set_uint8(x_115, sizeof(void*)*10 + 2, x_107);
lean_inc(x_115);
x_116 = l_Lean_Elab_Term_elabType(x_14, x_115, x_7);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_120);
x_122 = l_Lean_mkFVar(x_120);
lean_inc(x_122);
x_123 = lean_array_push(x_3, x_122);
x_124 = lean_ctor_get(x_13, 0);
lean_inc(x_124);
x_125 = l_Lean_Syntax_getId(x_124);
lean_dec(x_124);
x_126 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_117);
x_127 = lean_local_ctx_mk_local_decl(x_4, x_120, x_125, x_117, x_126);
lean_inc(x_115);
x_128 = l_Lean_Elab_Term_isClass(x_117, x_115, x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_122);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_2, x_131);
lean_dec(x_2);
x_2 = x_132;
x_3 = x_123;
x_4 = x_127;
x_6 = x_115;
x_7 = x_130;
goto _start;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
lean_dec(x_129);
x_136 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_134);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_122);
x_139 = lean_array_push(x_5, x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_add(x_2, x_140);
lean_dec(x_2);
x_2 = x_141;
x_3 = x_123;
x_4 = x_127;
x_5 = x_139;
x_6 = x_115;
x_7 = x_137;
goto _start;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_5);
lean_dec(x_2);
x_143 = lean_ctor_get(x_128, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_128, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_145 = x_128;
} else {
 lean_dec_ref(x_128);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_115);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_7__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_7__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Binders_7__elabBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_7__elabBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l___private_Lean_Elab_Binders_6__matchBinder(x_13, x_6, x_7);
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
x_18 = l___private_Lean_Elab_Binders_7__elabBinderViews___main(x_15, x_17, x_3, x_4, x_5, x_6, x_16);
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
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_8__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_8__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Binders_8__elabBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_8__elabBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l___private_Lean_Elab_Binders_8__elabBindersAux___main(x_1, x_12, x_13, x_7, x_10, x_3, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_array_get_size(x_10);
lean_dec(x_10);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 1, x_20);
x_30 = lean_apply_3(x_2, x_19, x_3, x_17);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 3);
x_33 = lean_ctor_get(x_26, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_3, 0, x_34);
x_35 = lean_apply_3(x_2, x_19, x_3, x_17);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
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
x_49 = lean_ctor_get(x_36, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_36, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_36, 4);
lean_inc(x_51);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 x_52 = x_36;
} else {
 lean_dec_ref(x_36);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 5, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_20);
lean_ctor_set(x_53, 2, x_21);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
x_54 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_37);
lean_ctor_set(x_54, 2, x_38);
lean_ctor_set(x_54, 3, x_39);
lean_ctor_set(x_54, 4, x_40);
lean_ctor_set(x_54, 5, x_41);
lean_ctor_set(x_54, 6, x_42);
lean_ctor_set(x_54, 7, x_43);
lean_ctor_set(x_54, 8, x_44);
lean_ctor_set(x_54, 9, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*10, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*10 + 1, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*10 + 2, x_47);
x_55 = lean_apply_3(x_2, x_19, x_54, x_17);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_56 = lean_ctor_get(x_17, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 2);
lean_inc(x_58);
lean_dec(x_57);
x_160 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_17);
x_161 = lean_ctor_get(x_3, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = !lean_is_exclusive(x_3);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_3, 0);
lean_dec(x_164);
x_165 = !lean_is_exclusive(x_161);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_161, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_161, 1);
lean_dec(x_167);
lean_ctor_set(x_161, 2, x_21);
lean_ctor_set(x_161, 1, x_20);
x_168 = lean_apply_3(x_2, x_19, x_3, x_162);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_169);
x_59 = x_171;
x_60 = x_170;
goto block_159;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_dec(x_168);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_172);
x_59 = x_174;
x_60 = x_173;
goto block_159;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_161, 0);
x_176 = lean_ctor_get(x_161, 3);
x_177 = lean_ctor_get(x_161, 4);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_161);
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_20);
lean_ctor_set(x_178, 2, x_21);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set(x_178, 4, x_177);
lean_ctor_set(x_3, 0, x_178);
x_179 = lean_apply_3(x_2, x_19, x_3, x_162);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_180);
x_59 = x_182;
x_60 = x_181;
goto block_159;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
lean_dec(x_179);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_183);
x_59 = x_185;
x_60 = x_184;
goto block_159;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_186 = lean_ctor_get(x_3, 1);
x_187 = lean_ctor_get(x_3, 2);
x_188 = lean_ctor_get(x_3, 3);
x_189 = lean_ctor_get(x_3, 4);
x_190 = lean_ctor_get(x_3, 5);
x_191 = lean_ctor_get(x_3, 6);
x_192 = lean_ctor_get(x_3, 7);
x_193 = lean_ctor_get(x_3, 8);
x_194 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_195 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_196 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_197 = lean_ctor_get(x_3, 9);
lean_inc(x_197);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_3);
x_198 = lean_ctor_get(x_161, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_161, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_161, 4);
lean_inc(x_200);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 x_201 = x_161;
} else {
 lean_dec_ref(x_161);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 5, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_20);
lean_ctor_set(x_202, 2, x_21);
lean_ctor_set(x_202, 3, x_199);
lean_ctor_set(x_202, 4, x_200);
x_203 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_186);
lean_ctor_set(x_203, 2, x_187);
lean_ctor_set(x_203, 3, x_188);
lean_ctor_set(x_203, 4, x_189);
lean_ctor_set(x_203, 5, x_190);
lean_ctor_set(x_203, 6, x_191);
lean_ctor_set(x_203, 7, x_192);
lean_ctor_set(x_203, 8, x_193);
lean_ctor_set(x_203, 9, x_197);
lean_ctor_set_uint8(x_203, sizeof(void*)*10, x_194);
lean_ctor_set_uint8(x_203, sizeof(void*)*10 + 1, x_195);
lean_ctor_set_uint8(x_203, sizeof(void*)*10 + 2, x_196);
x_204 = lean_apply_3(x_2, x_19, x_203, x_162);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_205);
x_59 = x_207;
x_60 = x_206;
goto block_159;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_204, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_dec(x_204);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_208);
x_59 = x_210;
x_60 = x_209;
goto block_159;
}
}
block_159:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_61, 2);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_62);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_62, 2);
lean_dec(x_69);
lean_ctor_set(x_62, 2, x_58);
if (lean_is_scalar(x_18)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_18;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_60);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
x_73 = lean_ctor_get(x_62, 3);
x_74 = lean_ctor_get(x_62, 4);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_75, 2, x_58);
lean_ctor_set(x_75, 3, x_73);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_61, 2, x_75);
if (lean_is_scalar(x_18)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_18;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_61, 0);
x_78 = lean_ctor_get(x_61, 1);
x_79 = lean_ctor_get(x_61, 3);
x_80 = lean_ctor_get(x_61, 4);
x_81 = lean_ctor_get(x_61, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_61);
x_82 = lean_ctor_get(x_62, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_62, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_62, 4);
lean_inc(x_85);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 x_86 = x_62;
} else {
 lean_dec_ref(x_62);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 5, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_58);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_85);
x_88 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_78);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_79);
lean_ctor_set(x_88, 4, x_80);
lean_ctor_set(x_88, 5, x_81);
lean_ctor_set(x_60, 0, x_88);
if (lean_is_scalar(x_18)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_18;
 lean_ctor_set_tag(x_89, 1);
}
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_60);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_90 = lean_ctor_get(x_60, 1);
x_91 = lean_ctor_get(x_60, 2);
x_92 = lean_ctor_get(x_60, 3);
x_93 = lean_ctor_get(x_60, 4);
x_94 = lean_ctor_get(x_60, 5);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_60);
x_95 = lean_ctor_get(x_61, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_61, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_61, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_61, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_61, 5);
lean_inc(x_99);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 x_100 = x_61;
} else {
 lean_dec_ref(x_61);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_62, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_62, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_62, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_62, 4);
lean_inc(x_104);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 x_105 = x_62;
} else {
 lean_dec_ref(x_62);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 5, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_102);
lean_ctor_set(x_106, 2, x_58);
lean_ctor_set(x_106, 3, x_103);
lean_ctor_set(x_106, 4, x_104);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(0, 6, 0);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_97);
lean_ctor_set(x_107, 4, x_98);
lean_ctor_set(x_107, 5, x_99);
x_108 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_90);
lean_ctor_set(x_108, 2, x_91);
lean_ctor_set(x_108, 3, x_92);
lean_ctor_set(x_108, 4, x_93);
lean_ctor_set(x_108, 5, x_94);
if (lean_is_scalar(x_18)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_18;
 lean_ctor_set_tag(x_109, 1);
}
lean_ctor_set(x_109, 0, x_63);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_60, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_59, 0);
lean_inc(x_112);
lean_dec(x_59);
x_113 = !lean_is_exclusive(x_60);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_60, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_110, 2);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_111);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_111, 2);
lean_dec(x_118);
lean_ctor_set(x_111, 2, x_58);
if (lean_is_scalar(x_18)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_18;
}
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_60);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_111, 0);
x_121 = lean_ctor_get(x_111, 1);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_58);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
lean_ctor_set(x_110, 2, x_124);
if (lean_is_scalar(x_18)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_18;
}
lean_ctor_set(x_125, 0, x_112);
lean_ctor_set(x_125, 1, x_60);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_126 = lean_ctor_get(x_110, 0);
x_127 = lean_ctor_get(x_110, 1);
x_128 = lean_ctor_get(x_110, 3);
x_129 = lean_ctor_get(x_110, 4);
x_130 = lean_ctor_get(x_110, 5);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_110);
x_131 = lean_ctor_get(x_111, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_111, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_111, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_111, 4);
lean_inc(x_134);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_135 = x_111;
} else {
 lean_dec_ref(x_111);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_58);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set(x_136, 4, x_134);
x_137 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_127);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set(x_137, 4, x_129);
lean_ctor_set(x_137, 5, x_130);
lean_ctor_set(x_60, 0, x_137);
if (lean_is_scalar(x_18)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_18;
}
lean_ctor_set(x_138, 0, x_112);
lean_ctor_set(x_138, 1, x_60);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_139 = lean_ctor_get(x_60, 1);
x_140 = lean_ctor_get(x_60, 2);
x_141 = lean_ctor_get(x_60, 3);
x_142 = lean_ctor_get(x_60, 4);
x_143 = lean_ctor_get(x_60, 5);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_60);
x_144 = lean_ctor_get(x_110, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_110, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_110, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_110, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_110, 5);
lean_inc(x_148);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_149 = x_110;
} else {
 lean_dec_ref(x_110);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_111, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_111, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_111, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_111, 4);
lean_inc(x_153);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_154 = x_111;
} else {
 lean_dec_ref(x_111);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 5, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_151);
lean_ctor_set(x_155, 2, x_58);
lean_ctor_set(x_155, 3, x_152);
lean_ctor_set(x_155, 4, x_153);
if (lean_is_scalar(x_149)) {
 x_156 = lean_alloc_ctor(0, 6, 0);
} else {
 x_156 = x_149;
}
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_145);
lean_ctor_set(x_156, 2, x_155);
lean_ctor_set(x_156, 3, x_146);
lean_ctor_set(x_156, 4, x_147);
lean_ctor_set(x_156, 5, x_148);
x_157 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_139);
lean_ctor_set(x_157, 2, x_140);
lean_ctor_set(x_157, 3, x_141);
lean_ctor_set(x_157, 4, x_142);
lean_ctor_set(x_157, 5, x_143);
if (lean_is_scalar(x_18)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_18;
}
lean_ctor_set(x_158, 0, x_112);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_211 = !lean_is_exclusive(x_14);
if (x_211 == 0)
{
return x_14;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_14, 0);
x_213 = lean_ctor_get(x_14, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_14);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = l_Array_empty___closed__1;
x_216 = lean_apply_3(x_2, x_215, x_3, x_4);
return x_216;
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
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_elabType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_mkForall(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
lean_dec(x_1);
x_17 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 4, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = l_Lean_Elab_Term_elabBinders___rarg(x_17, x_18, x_3, x_4);
lean_dec(x_17);
return x_19;
}
}
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 4, 0);
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
lean_object* _init_l_Lean_Elab_Term_elabArrow___lambda__1___closed__1() {
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
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
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
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
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
x_16 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_17 = l_Lean_addMacroScope(x_15, x_16, x_11);
x_18 = lean_box(0);
x_19 = l_Lean_SourceInfo_inhabited___closed__1;
x_20 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_nullKind___closed__2;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_29 = lean_array_push(x_28, x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_27, x_30);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_33 = lean_array_push(x_31, x_32);
x_34 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
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
x_49 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_50 = l_Lean_addMacroScope(x_47, x_49, x_11);
x_51 = lean_box(0);
x_52 = l_Lean_SourceInfo_inhabited___closed__1;
x_53 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
x_55 = l_Array_empty___closed__1;
x_56 = lean_array_push(x_55, x_54);
x_57 = l_Lean_nullKind___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_60 = lean_array_push(x_59, x_58);
x_61 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_62 = lean_array_push(x_61, x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_60, x_63);
x_65 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_66 = lean_array_push(x_64, x_65);
x_67 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
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
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 4, 1);
lean_closure_set(x_11, 0, x_8);
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
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 4, 0);
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
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_82 = l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main(x_81, x_48, x_3, x_4, x_5);
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
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Lean_Elab_Binders_9__getFunBinderIdsAux_x3f___main(x_4, x_1, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_mkExplicitBinder(x_10, x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_match___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Parser_Basic_2__sepByFnAux___main___at_Lean_Parser_Term_matchAlts___elambda__1___spec__2___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid binder, simple identifier expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
case 1:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_16, 1);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_17, 1);
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 0);
lean_dec(x_32);
x_33 = l_Lean_mkAppStx___closed__1;
x_34 = lean_string_dec_eq(x_31, x_33);
lean_dec(x_31);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_dec(x_28);
lean_free_object(x_16);
lean_dec(x_25);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_35 = 1;
lean_inc(x_14);
x_36 = l_Lean_Syntax_isTermId_x3f(x_14, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_3, x_40);
lean_dec(x_3);
x_42 = l_Lean_mkHole(x_14);
lean_inc(x_38);
x_43 = l_Lean_Elab_Term_mkExplicitBinder(x_38, x_42);
x_44 = lean_array_push(x_4, x_43);
lean_inc(x_5);
x_45 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_41, x_44, x_5, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_46, 1);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_dec(x_53);
x_54 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_48);
lean_dec(x_5);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Elab_Term_getMainModule___rarg(x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = l_Array_empty___closed__1;
x_60 = lean_array_push(x_59, x_38);
x_61 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_62 = lean_array_push(x_60, x_61);
x_63 = l_Lean_mkTermIdFromIdent___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_66 = lean_array_push(x_65, x_64);
x_67 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_59, x_68);
x_70 = l_Lean_nullKind___closed__2;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_73 = lean_array_push(x_72, x_71);
x_74 = lean_array_push(x_73, x_61);
x_75 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_76 = lean_array_push(x_74, x_75);
x_77 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_78 = lean_array_push(x_76, x_77);
lean_inc(x_14);
x_79 = lean_array_push(x_59, x_14);
x_80 = !lean_is_exclusive(x_14);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_14, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_14, 0);
lean_dec(x_82);
lean_ctor_set(x_14, 1, x_79);
lean_ctor_set(x_14, 0, x_70);
x_83 = lean_array_push(x_59, x_14);
x_84 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_85 = lean_array_push(x_83, x_84);
x_86 = lean_array_push(x_85, x_52);
x_87 = l_Lean_Parser_Term_matchAlt___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_array_push(x_59, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_70);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_push(x_78, x_90);
x_92 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_box(x_35);
lean_ctor_set(x_47, 1, x_94);
lean_ctor_set(x_47, 0, x_93);
lean_ctor_set(x_56, 0, x_46);
return x_56;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_14);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_70);
lean_ctor_set(x_95, 1, x_79);
x_96 = lean_array_push(x_59, x_95);
x_97 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_98 = lean_array_push(x_96, x_97);
x_99 = lean_array_push(x_98, x_52);
x_100 = l_Lean_Parser_Term_matchAlt___closed__2;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_array_push(x_59, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_70);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_push(x_78, x_103);
x_105 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_box(x_35);
lean_ctor_set(x_47, 1, x_107);
lean_ctor_set(x_47, 0, x_106);
lean_ctor_set(x_56, 0, x_46);
return x_56;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_108 = lean_ctor_get(x_56, 1);
lean_inc(x_108);
lean_dec(x_56);
x_109 = l_Array_empty___closed__1;
x_110 = lean_array_push(x_109, x_38);
x_111 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_112 = lean_array_push(x_110, x_111);
x_113 = l_Lean_mkTermIdFromIdent___closed__2;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_116 = lean_array_push(x_115, x_114);
x_117 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_109, x_118);
x_120 = l_Lean_nullKind___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_123 = lean_array_push(x_122, x_121);
x_124 = lean_array_push(x_123, x_111);
x_125 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_126 = lean_array_push(x_124, x_125);
x_127 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_128 = lean_array_push(x_126, x_127);
lean_inc(x_14);
x_129 = lean_array_push(x_109, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_130 = x_14;
} else {
 lean_dec_ref(x_14);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_120);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_109, x_131);
x_133 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_134 = lean_array_push(x_132, x_133);
x_135 = lean_array_push(x_134, x_52);
x_136 = l_Lean_Parser_Term_matchAlt___closed__2;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_array_push(x_109, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_120);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_128, x_139);
x_141 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_box(x_35);
lean_ctor_set(x_47, 1, x_143);
lean_ctor_set(x_47, 0, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_46);
lean_ctor_set(x_144, 1, x_108);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_145 = lean_ctor_get(x_47, 0);
lean_inc(x_145);
lean_dec(x_47);
x_146 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_48);
lean_dec(x_5);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_Elab_Term_getMainModule___rarg(x_147);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = l_Array_empty___closed__1;
x_152 = lean_array_push(x_151, x_38);
x_153 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_154 = lean_array_push(x_152, x_153);
x_155 = l_Lean_mkTermIdFromIdent___closed__2;
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_158 = lean_array_push(x_157, x_156);
x_159 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_array_push(x_151, x_160);
x_162 = l_Lean_nullKind___closed__2;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_165 = lean_array_push(x_164, x_163);
x_166 = lean_array_push(x_165, x_153);
x_167 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_168 = lean_array_push(x_166, x_167);
x_169 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_170 = lean_array_push(x_168, x_169);
lean_inc(x_14);
x_171 = lean_array_push(x_151, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_172 = x_14;
} else {
 lean_dec_ref(x_14);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_array_push(x_151, x_173);
x_175 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_176 = lean_array_push(x_174, x_175);
x_177 = lean_array_push(x_176, x_145);
x_178 = l_Lean_Parser_Term_matchAlt___closed__2;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = lean_array_push(x_151, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_162);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_push(x_170, x_181);
x_183 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_box(x_35);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set(x_46, 1, x_186);
if (lean_is_scalar(x_150)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_150;
}
lean_ctor_set(x_187, 0, x_46);
lean_ctor_set(x_187, 1, x_149);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_188 = lean_ctor_get(x_46, 0);
lean_inc(x_188);
lean_dec(x_46);
x_189 = lean_ctor_get(x_47, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_190 = x_47;
} else {
 lean_dec_ref(x_47);
 x_190 = lean_box(0);
}
x_191 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_48);
lean_dec(x_5);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = l_Lean_Elab_Term_getMainModule___rarg(x_192);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = l_Array_empty___closed__1;
x_197 = lean_array_push(x_196, x_38);
x_198 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_199 = lean_array_push(x_197, x_198);
x_200 = l_Lean_mkTermIdFromIdent___closed__2;
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_203 = lean_array_push(x_202, x_201);
x_204 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_array_push(x_196, x_205);
x_207 = l_Lean_nullKind___closed__2;
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_210 = lean_array_push(x_209, x_208);
x_211 = lean_array_push(x_210, x_198);
x_212 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_213 = lean_array_push(x_211, x_212);
x_214 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_215 = lean_array_push(x_213, x_214);
lean_inc(x_14);
x_216 = lean_array_push(x_196, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_217 = x_14;
} else {
 lean_dec_ref(x_14);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_207);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_array_push(x_196, x_218);
x_220 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_221 = lean_array_push(x_219, x_220);
x_222 = lean_array_push(x_221, x_189);
x_223 = l_Lean_Parser_Term_matchAlt___closed__2;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_array_push(x_196, x_224);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_207);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_215, x_226);
x_228 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_box(x_35);
if (lean_is_scalar(x_190)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_190;
}
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_188);
lean_ctor_set(x_232, 1, x_231);
if (lean_is_scalar(x_195)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_195;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_194);
return x_233;
}
}
else
{
uint8_t x_234; 
lean_dec(x_38);
lean_dec(x_14);
lean_dec(x_5);
x_234 = !lean_is_exclusive(x_45);
if (x_234 == 0)
{
return x_45;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_45, 0);
x_236 = lean_ctor_get(x_45, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_45);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_238 = lean_ctor_get(x_36, 0);
lean_inc(x_238);
lean_dec(x_36);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Syntax_isNone(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_dec(x_239);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_243 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_242, x_5, x_6);
lean_dec(x_14);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
return x_243;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_243);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_nat_add(x_3, x_249);
lean_dec(x_3);
x_251 = l_Lean_Elab_Term_mkExplicitBinder(x_239, x_248);
x_252 = lean_array_push(x_4, x_251);
x_3 = x_250;
x_4 = x_252;
goto _start;
}
}
}
else
{
lean_object* x_254; uint8_t x_255; 
x_254 = l_Lean_mkAppStx___closed__3;
x_255 = lean_string_dec_eq(x_28, x_254);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; 
lean_ctor_set(x_18, 1, x_33);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_15);
lean_ctor_set(x_256, 1, x_20);
x_257 = 1;
lean_inc(x_256);
x_258 = l_Lean_Syntax_isTermId_x3f(x_256, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_256);
x_259 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_nat_add(x_3, x_262);
lean_dec(x_3);
x_264 = l_Lean_mkHole(x_14);
lean_inc(x_260);
x_265 = l_Lean_Elab_Term_mkExplicitBinder(x_260, x_264);
x_266 = lean_array_push(x_4, x_265);
lean_inc(x_5);
x_267 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_263, x_266, x_5, x_261);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_dec(x_267);
x_271 = !lean_is_exclusive(x_268);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_268, 1);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_269);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_274 = lean_ctor_get(x_269, 0);
x_275 = lean_ctor_get(x_269, 1);
lean_dec(x_275);
x_276 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_270);
lean_dec(x_5);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_278 = l_Lean_Elab_Term_getMainModule___rarg(x_277);
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_280 = lean_ctor_get(x_278, 0);
lean_dec(x_280);
x_281 = l_Array_empty___closed__1;
x_282 = lean_array_push(x_281, x_260);
x_283 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_284 = lean_array_push(x_282, x_283);
x_285 = l_Lean_mkTermIdFromIdent___closed__2;
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_284);
x_287 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_288 = lean_array_push(x_287, x_286);
x_289 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = lean_array_push(x_281, x_290);
x_292 = l_Lean_nullKind___closed__2;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_295 = lean_array_push(x_294, x_293);
x_296 = lean_array_push(x_295, x_283);
x_297 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_298 = lean_array_push(x_296, x_297);
x_299 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_300 = lean_array_push(x_298, x_299);
lean_inc(x_14);
x_301 = lean_array_push(x_281, x_14);
x_302 = !lean_is_exclusive(x_14);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_303 = lean_ctor_get(x_14, 1);
lean_dec(x_303);
x_304 = lean_ctor_get(x_14, 0);
lean_dec(x_304);
lean_ctor_set(x_14, 1, x_301);
lean_ctor_set(x_14, 0, x_292);
x_305 = lean_array_push(x_281, x_14);
x_306 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_307 = lean_array_push(x_305, x_306);
x_308 = lean_array_push(x_307, x_274);
x_309 = l_Lean_Parser_Term_matchAlt___closed__2;
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_308);
x_311 = lean_array_push(x_281, x_310);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_292);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_array_push(x_300, x_312);
x_314 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = lean_box(x_257);
lean_ctor_set(x_269, 1, x_316);
lean_ctor_set(x_269, 0, x_315);
lean_ctor_set(x_278, 0, x_268);
return x_278;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_14);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_292);
lean_ctor_set(x_317, 1, x_301);
x_318 = lean_array_push(x_281, x_317);
x_319 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_320 = lean_array_push(x_318, x_319);
x_321 = lean_array_push(x_320, x_274);
x_322 = l_Lean_Parser_Term_matchAlt___closed__2;
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
x_324 = lean_array_push(x_281, x_323);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_292);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_array_push(x_300, x_325);
x_327 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
x_329 = lean_box(x_257);
lean_ctor_set(x_269, 1, x_329);
lean_ctor_set(x_269, 0, x_328);
lean_ctor_set(x_278, 0, x_268);
return x_278;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_330 = lean_ctor_get(x_278, 1);
lean_inc(x_330);
lean_dec(x_278);
x_331 = l_Array_empty___closed__1;
x_332 = lean_array_push(x_331, x_260);
x_333 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_334 = lean_array_push(x_332, x_333);
x_335 = l_Lean_mkTermIdFromIdent___closed__2;
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
x_337 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_338 = lean_array_push(x_337, x_336);
x_339 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = lean_array_push(x_331, x_340);
x_342 = l_Lean_nullKind___closed__2;
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
x_344 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_345 = lean_array_push(x_344, x_343);
x_346 = lean_array_push(x_345, x_333);
x_347 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_348 = lean_array_push(x_346, x_347);
x_349 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_350 = lean_array_push(x_348, x_349);
lean_inc(x_14);
x_351 = lean_array_push(x_331, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_352 = x_14;
} else {
 lean_dec_ref(x_14);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_array_push(x_331, x_353);
x_355 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_356 = lean_array_push(x_354, x_355);
x_357 = lean_array_push(x_356, x_274);
x_358 = l_Lean_Parser_Term_matchAlt___closed__2;
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = lean_array_push(x_331, x_359);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_342);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_array_push(x_350, x_361);
x_363 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = lean_box(x_257);
lean_ctor_set(x_269, 1, x_365);
lean_ctor_set(x_269, 0, x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_268);
lean_ctor_set(x_366, 1, x_330);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_367 = lean_ctor_get(x_269, 0);
lean_inc(x_367);
lean_dec(x_269);
x_368 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_270);
lean_dec(x_5);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_370 = l_Lean_Elab_Term_getMainModule___rarg(x_369);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_372 = x_370;
} else {
 lean_dec_ref(x_370);
 x_372 = lean_box(0);
}
x_373 = l_Array_empty___closed__1;
x_374 = lean_array_push(x_373, x_260);
x_375 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_376 = lean_array_push(x_374, x_375);
x_377 = l_Lean_mkTermIdFromIdent___closed__2;
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_380 = lean_array_push(x_379, x_378);
x_381 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = lean_array_push(x_373, x_382);
x_384 = l_Lean_nullKind___closed__2;
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_387 = lean_array_push(x_386, x_385);
x_388 = lean_array_push(x_387, x_375);
x_389 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_390 = lean_array_push(x_388, x_389);
x_391 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_392 = lean_array_push(x_390, x_391);
lean_inc(x_14);
x_393 = lean_array_push(x_373, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_394 = x_14;
} else {
 lean_dec_ref(x_14);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_384);
lean_ctor_set(x_395, 1, x_393);
x_396 = lean_array_push(x_373, x_395);
x_397 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_398 = lean_array_push(x_396, x_397);
x_399 = lean_array_push(x_398, x_367);
x_400 = l_Lean_Parser_Term_matchAlt___closed__2;
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
x_402 = lean_array_push(x_373, x_401);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_384);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_array_push(x_392, x_403);
x_405 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_404);
x_407 = lean_box(x_257);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_268, 1, x_408);
if (lean_is_scalar(x_372)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_372;
}
lean_ctor_set(x_409, 0, x_268);
lean_ctor_set(x_409, 1, x_371);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_410 = lean_ctor_get(x_268, 0);
lean_inc(x_410);
lean_dec(x_268);
x_411 = lean_ctor_get(x_269, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_412 = x_269;
} else {
 lean_dec_ref(x_269);
 x_412 = lean_box(0);
}
x_413 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_270);
lean_dec(x_5);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_415 = l_Lean_Elab_Term_getMainModule___rarg(x_414);
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
x_418 = l_Array_empty___closed__1;
x_419 = lean_array_push(x_418, x_260);
x_420 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_421 = lean_array_push(x_419, x_420);
x_422 = l_Lean_mkTermIdFromIdent___closed__2;
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_421);
x_424 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_425 = lean_array_push(x_424, x_423);
x_426 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
x_428 = lean_array_push(x_418, x_427);
x_429 = l_Lean_nullKind___closed__2;
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_432 = lean_array_push(x_431, x_430);
x_433 = lean_array_push(x_432, x_420);
x_434 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_435 = lean_array_push(x_433, x_434);
x_436 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_437 = lean_array_push(x_435, x_436);
lean_inc(x_14);
x_438 = lean_array_push(x_418, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_439 = x_14;
} else {
 lean_dec_ref(x_14);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_429);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_array_push(x_418, x_440);
x_442 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_443 = lean_array_push(x_441, x_442);
x_444 = lean_array_push(x_443, x_411);
x_445 = l_Lean_Parser_Term_matchAlt___closed__2;
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_444);
x_447 = lean_array_push(x_418, x_446);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_429);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_array_push(x_437, x_448);
x_450 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
x_452 = lean_box(x_257);
if (lean_is_scalar(x_412)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_412;
}
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_410);
lean_ctor_set(x_454, 1, x_453);
if (lean_is_scalar(x_417)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_417;
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_416);
return x_455;
}
}
else
{
uint8_t x_456; 
lean_dec(x_260);
lean_dec(x_14);
lean_dec(x_5);
x_456 = !lean_is_exclusive(x_267);
if (x_456 == 0)
{
return x_267;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_267, 0);
x_458 = lean_ctor_get(x_267, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_267);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_14);
x_460 = lean_ctor_get(x_258, 0);
lean_inc(x_460);
lean_dec(x_258);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = l_Lean_Syntax_isNone(x_462);
lean_dec(x_462);
if (x_463 == 0)
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
lean_dec(x_461);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_464 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_465 = l_Lean_Elab_Term_throwErrorAt___rarg(x_256, x_464, x_5, x_6);
lean_dec(x_256);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
return x_465;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_465, 0);
x_468 = lean_ctor_get(x_465, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_465);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_470 = l_Lean_mkHole(x_256);
lean_dec(x_256);
x_471 = lean_unsigned_to_nat(1u);
x_472 = lean_nat_add(x_3, x_471);
lean_dec(x_3);
x_473 = l_Lean_Elab_Term_mkExplicitBinder(x_461, x_470);
x_474 = lean_array_push(x_4, x_473);
x_3 = x_472;
x_4 = x_474;
goto _start;
}
}
}
else
{
lean_object* x_476; uint8_t x_477; 
lean_dec(x_28);
x_476 = l_Lean_mkAppStx___closed__5;
x_477 = lean_string_dec_eq(x_25, x_476);
if (x_477 == 0)
{
lean_object* x_478; uint8_t x_479; lean_object* x_480; 
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_17, 1, x_254);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_15);
lean_ctor_set(x_478, 1, x_20);
x_479 = 1;
lean_inc(x_478);
x_480 = l_Lean_Syntax_isTermId_x3f(x_478, x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_478);
x_481 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_unsigned_to_nat(1u);
x_485 = lean_nat_add(x_3, x_484);
lean_dec(x_3);
x_486 = l_Lean_mkHole(x_14);
lean_inc(x_482);
x_487 = l_Lean_Elab_Term_mkExplicitBinder(x_482, x_486);
x_488 = lean_array_push(x_4, x_487);
lean_inc(x_5);
x_489 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_485, x_488, x_5, x_483);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
lean_dec(x_489);
x_493 = !lean_is_exclusive(x_490);
if (x_493 == 0)
{
lean_object* x_494; uint8_t x_495; 
x_494 = lean_ctor_get(x_490, 1);
lean_dec(x_494);
x_495 = !lean_is_exclusive(x_491);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_496 = lean_ctor_get(x_491, 0);
x_497 = lean_ctor_get(x_491, 1);
lean_dec(x_497);
x_498 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_492);
lean_dec(x_5);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
x_500 = l_Lean_Elab_Term_getMainModule___rarg(x_499);
x_501 = !lean_is_exclusive(x_500);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; 
x_502 = lean_ctor_get(x_500, 0);
lean_dec(x_502);
x_503 = l_Array_empty___closed__1;
x_504 = lean_array_push(x_503, x_482);
x_505 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_506 = lean_array_push(x_504, x_505);
x_507 = l_Lean_mkTermIdFromIdent___closed__2;
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_506);
x_509 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_510 = lean_array_push(x_509, x_508);
x_511 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_510);
x_513 = lean_array_push(x_503, x_512);
x_514 = l_Lean_nullKind___closed__2;
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
x_516 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_517 = lean_array_push(x_516, x_515);
x_518 = lean_array_push(x_517, x_505);
x_519 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_520 = lean_array_push(x_518, x_519);
x_521 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_522 = lean_array_push(x_520, x_521);
lean_inc(x_14);
x_523 = lean_array_push(x_503, x_14);
x_524 = !lean_is_exclusive(x_14);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_525 = lean_ctor_get(x_14, 1);
lean_dec(x_525);
x_526 = lean_ctor_get(x_14, 0);
lean_dec(x_526);
lean_ctor_set(x_14, 1, x_523);
lean_ctor_set(x_14, 0, x_514);
x_527 = lean_array_push(x_503, x_14);
x_528 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_529 = lean_array_push(x_527, x_528);
x_530 = lean_array_push(x_529, x_496);
x_531 = l_Lean_Parser_Term_matchAlt___closed__2;
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_530);
x_533 = lean_array_push(x_503, x_532);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_514);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_array_push(x_522, x_534);
x_536 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_535);
x_538 = lean_box(x_479);
lean_ctor_set(x_491, 1, x_538);
lean_ctor_set(x_491, 0, x_537);
lean_ctor_set(x_500, 0, x_490);
return x_500;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_14);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_514);
lean_ctor_set(x_539, 1, x_523);
x_540 = lean_array_push(x_503, x_539);
x_541 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_542 = lean_array_push(x_540, x_541);
x_543 = lean_array_push(x_542, x_496);
x_544 = l_Lean_Parser_Term_matchAlt___closed__2;
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = lean_array_push(x_503, x_545);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_514);
lean_ctor_set(x_547, 1, x_546);
x_548 = lean_array_push(x_522, x_547);
x_549 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
x_551 = lean_box(x_479);
lean_ctor_set(x_491, 1, x_551);
lean_ctor_set(x_491, 0, x_550);
lean_ctor_set(x_500, 0, x_490);
return x_500;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_552 = lean_ctor_get(x_500, 1);
lean_inc(x_552);
lean_dec(x_500);
x_553 = l_Array_empty___closed__1;
x_554 = lean_array_push(x_553, x_482);
x_555 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_556 = lean_array_push(x_554, x_555);
x_557 = l_Lean_mkTermIdFromIdent___closed__2;
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_560 = lean_array_push(x_559, x_558);
x_561 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_560);
x_563 = lean_array_push(x_553, x_562);
x_564 = l_Lean_nullKind___closed__2;
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_563);
x_566 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_567 = lean_array_push(x_566, x_565);
x_568 = lean_array_push(x_567, x_555);
x_569 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_570 = lean_array_push(x_568, x_569);
x_571 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_572 = lean_array_push(x_570, x_571);
lean_inc(x_14);
x_573 = lean_array_push(x_553, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_574 = x_14;
} else {
 lean_dec_ref(x_14);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(1, 2, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_564);
lean_ctor_set(x_575, 1, x_573);
x_576 = lean_array_push(x_553, x_575);
x_577 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_578 = lean_array_push(x_576, x_577);
x_579 = lean_array_push(x_578, x_496);
x_580 = l_Lean_Parser_Term_matchAlt___closed__2;
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_579);
x_582 = lean_array_push(x_553, x_581);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_564);
lean_ctor_set(x_583, 1, x_582);
x_584 = lean_array_push(x_572, x_583);
x_585 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_584);
x_587 = lean_box(x_479);
lean_ctor_set(x_491, 1, x_587);
lean_ctor_set(x_491, 0, x_586);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_490);
lean_ctor_set(x_588, 1, x_552);
return x_588;
}
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_589 = lean_ctor_get(x_491, 0);
lean_inc(x_589);
lean_dec(x_491);
x_590 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_492);
lean_dec(x_5);
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
lean_dec(x_590);
x_592 = l_Lean_Elab_Term_getMainModule___rarg(x_591);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_594 = x_592;
} else {
 lean_dec_ref(x_592);
 x_594 = lean_box(0);
}
x_595 = l_Array_empty___closed__1;
x_596 = lean_array_push(x_595, x_482);
x_597 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_598 = lean_array_push(x_596, x_597);
x_599 = l_Lean_mkTermIdFromIdent___closed__2;
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_598);
x_601 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_602 = lean_array_push(x_601, x_600);
x_603 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_602);
x_605 = lean_array_push(x_595, x_604);
x_606 = l_Lean_nullKind___closed__2;
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_605);
x_608 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_609 = lean_array_push(x_608, x_607);
x_610 = lean_array_push(x_609, x_597);
x_611 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_612 = lean_array_push(x_610, x_611);
x_613 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_614 = lean_array_push(x_612, x_613);
lean_inc(x_14);
x_615 = lean_array_push(x_595, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_616 = x_14;
} else {
 lean_dec_ref(x_14);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_606);
lean_ctor_set(x_617, 1, x_615);
x_618 = lean_array_push(x_595, x_617);
x_619 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_620 = lean_array_push(x_618, x_619);
x_621 = lean_array_push(x_620, x_589);
x_622 = l_Lean_Parser_Term_matchAlt___closed__2;
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
x_624 = lean_array_push(x_595, x_623);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_606);
lean_ctor_set(x_625, 1, x_624);
x_626 = lean_array_push(x_614, x_625);
x_627 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_626);
x_629 = lean_box(x_479);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
lean_ctor_set(x_490, 1, x_630);
if (lean_is_scalar(x_594)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_594;
}
lean_ctor_set(x_631, 0, x_490);
lean_ctor_set(x_631, 1, x_593);
return x_631;
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_632 = lean_ctor_get(x_490, 0);
lean_inc(x_632);
lean_dec(x_490);
x_633 = lean_ctor_get(x_491, 0);
lean_inc(x_633);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_634 = x_491;
} else {
 lean_dec_ref(x_491);
 x_634 = lean_box(0);
}
x_635 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_492);
lean_dec(x_5);
x_636 = lean_ctor_get(x_635, 1);
lean_inc(x_636);
lean_dec(x_635);
x_637 = l_Lean_Elab_Term_getMainModule___rarg(x_636);
x_638 = lean_ctor_get(x_637, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_639 = x_637;
} else {
 lean_dec_ref(x_637);
 x_639 = lean_box(0);
}
x_640 = l_Array_empty___closed__1;
x_641 = lean_array_push(x_640, x_482);
x_642 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_643 = lean_array_push(x_641, x_642);
x_644 = l_Lean_mkTermIdFromIdent___closed__2;
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_643);
x_646 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_647 = lean_array_push(x_646, x_645);
x_648 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_647);
x_650 = lean_array_push(x_640, x_649);
x_651 = l_Lean_nullKind___closed__2;
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_650);
x_653 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_654 = lean_array_push(x_653, x_652);
x_655 = lean_array_push(x_654, x_642);
x_656 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_657 = lean_array_push(x_655, x_656);
x_658 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_659 = lean_array_push(x_657, x_658);
lean_inc(x_14);
x_660 = lean_array_push(x_640, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_661 = x_14;
} else {
 lean_dec_ref(x_14);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(1, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_651);
lean_ctor_set(x_662, 1, x_660);
x_663 = lean_array_push(x_640, x_662);
x_664 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_665 = lean_array_push(x_663, x_664);
x_666 = lean_array_push(x_665, x_633);
x_667 = l_Lean_Parser_Term_matchAlt___closed__2;
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_666);
x_669 = lean_array_push(x_640, x_668);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_651);
lean_ctor_set(x_670, 1, x_669);
x_671 = lean_array_push(x_659, x_670);
x_672 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_671);
x_674 = lean_box(x_479);
if (lean_is_scalar(x_634)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_634;
}
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_632);
lean_ctor_set(x_676, 1, x_675);
if (lean_is_scalar(x_639)) {
 x_677 = lean_alloc_ctor(0, 2, 0);
} else {
 x_677 = x_639;
}
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_638);
return x_677;
}
}
else
{
uint8_t x_678; 
lean_dec(x_482);
lean_dec(x_14);
lean_dec(x_5);
x_678 = !lean_is_exclusive(x_489);
if (x_678 == 0)
{
return x_489;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_489, 0);
x_680 = lean_ctor_get(x_489, 1);
lean_inc(x_680);
lean_inc(x_679);
lean_dec(x_489);
x_681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set(x_681, 1, x_680);
return x_681;
}
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
lean_dec(x_14);
x_682 = lean_ctor_get(x_480, 0);
lean_inc(x_682);
lean_dec(x_480);
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
x_685 = l_Lean_Syntax_isNone(x_684);
lean_dec(x_684);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; uint8_t x_688; 
lean_dec(x_683);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_686 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_687 = l_Lean_Elab_Term_throwErrorAt___rarg(x_478, x_686, x_5, x_6);
lean_dec(x_478);
x_688 = !lean_is_exclusive(x_687);
if (x_688 == 0)
{
return x_687;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_687, 0);
x_690 = lean_ctor_get(x_687, 1);
lean_inc(x_690);
lean_inc(x_689);
lean_dec(x_687);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
return x_691;
}
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_692 = l_Lean_mkHole(x_478);
lean_dec(x_478);
x_693 = lean_unsigned_to_nat(1u);
x_694 = lean_nat_add(x_3, x_693);
lean_dec(x_3);
x_695 = l_Lean_Elab_Term_mkExplicitBinder(x_683, x_692);
x_696 = lean_array_push(x_4, x_695);
x_3 = x_694;
x_4 = x_696;
goto _start;
}
}
}
else
{
lean_object* x_698; uint8_t x_699; 
lean_dec(x_25);
x_698 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_699 = lean_string_dec_eq(x_22, x_698);
if (x_699 == 0)
{
lean_object* x_700; uint8_t x_701; 
x_700 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_701 = lean_string_dec_eq(x_22, x_700);
if (x_701 == 0)
{
lean_object* x_702; uint8_t x_703; 
x_702 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_703 = lean_string_dec_eq(x_22, x_702);
if (x_703 == 0)
{
lean_object* x_704; uint8_t x_705; 
x_704 = l_Lean_mkHole___closed__1;
x_705 = lean_string_dec_eq(x_22, x_704);
if (x_705 == 0)
{
lean_object* x_706; uint8_t x_707; 
x_706 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_707 = lean_string_dec_eq(x_22, x_706);
if (x_707 == 0)
{
lean_object* x_708; uint8_t x_709; lean_object* x_710; 
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_17, 1, x_254);
lean_ctor_set(x_16, 1, x_476);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_15);
lean_ctor_set(x_708, 1, x_20);
x_709 = 1;
lean_inc(x_708);
x_710 = l_Lean_Syntax_isTermId_x3f(x_708, x_709);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_708);
x_711 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_714 = lean_unsigned_to_nat(1u);
x_715 = lean_nat_add(x_3, x_714);
lean_dec(x_3);
x_716 = l_Lean_mkHole(x_14);
lean_inc(x_712);
x_717 = l_Lean_Elab_Term_mkExplicitBinder(x_712, x_716);
x_718 = lean_array_push(x_4, x_717);
lean_inc(x_5);
x_719 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_715, x_718, x_5, x_713);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; uint8_t x_723; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
x_722 = lean_ctor_get(x_719, 1);
lean_inc(x_722);
lean_dec(x_719);
x_723 = !lean_is_exclusive(x_720);
if (x_723 == 0)
{
lean_object* x_724; uint8_t x_725; 
x_724 = lean_ctor_get(x_720, 1);
lean_dec(x_724);
x_725 = !lean_is_exclusive(x_721);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
x_726 = lean_ctor_get(x_721, 0);
x_727 = lean_ctor_get(x_721, 1);
lean_dec(x_727);
x_728 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_722);
lean_dec(x_5);
x_729 = lean_ctor_get(x_728, 1);
lean_inc(x_729);
lean_dec(x_728);
x_730 = l_Lean_Elab_Term_getMainModule___rarg(x_729);
x_731 = !lean_is_exclusive(x_730);
if (x_731 == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; 
x_732 = lean_ctor_get(x_730, 0);
lean_dec(x_732);
x_733 = l_Array_empty___closed__1;
x_734 = lean_array_push(x_733, x_712);
x_735 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_736 = lean_array_push(x_734, x_735);
x_737 = l_Lean_mkTermIdFromIdent___closed__2;
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_736);
x_739 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_740 = lean_array_push(x_739, x_738);
x_741 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_740);
x_743 = lean_array_push(x_733, x_742);
x_744 = l_Lean_nullKind___closed__2;
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_743);
x_746 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_747 = lean_array_push(x_746, x_745);
x_748 = lean_array_push(x_747, x_735);
x_749 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_750 = lean_array_push(x_748, x_749);
x_751 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_752 = lean_array_push(x_750, x_751);
lean_inc(x_14);
x_753 = lean_array_push(x_733, x_14);
x_754 = !lean_is_exclusive(x_14);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_755 = lean_ctor_get(x_14, 1);
lean_dec(x_755);
x_756 = lean_ctor_get(x_14, 0);
lean_dec(x_756);
lean_ctor_set(x_14, 1, x_753);
lean_ctor_set(x_14, 0, x_744);
x_757 = lean_array_push(x_733, x_14);
x_758 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_759 = lean_array_push(x_757, x_758);
x_760 = lean_array_push(x_759, x_726);
x_761 = l_Lean_Parser_Term_matchAlt___closed__2;
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_760);
x_763 = lean_array_push(x_733, x_762);
x_764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_764, 0, x_744);
lean_ctor_set(x_764, 1, x_763);
x_765 = lean_array_push(x_752, x_764);
x_766 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_765);
x_768 = lean_box(x_709);
lean_ctor_set(x_721, 1, x_768);
lean_ctor_set(x_721, 0, x_767);
lean_ctor_set(x_730, 0, x_720);
return x_730;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_14);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_744);
lean_ctor_set(x_769, 1, x_753);
x_770 = lean_array_push(x_733, x_769);
x_771 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_772 = lean_array_push(x_770, x_771);
x_773 = lean_array_push(x_772, x_726);
x_774 = l_Lean_Parser_Term_matchAlt___closed__2;
x_775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_773);
x_776 = lean_array_push(x_733, x_775);
x_777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_777, 0, x_744);
lean_ctor_set(x_777, 1, x_776);
x_778 = lean_array_push(x_752, x_777);
x_779 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_778);
x_781 = lean_box(x_709);
lean_ctor_set(x_721, 1, x_781);
lean_ctor_set(x_721, 0, x_780);
lean_ctor_set(x_730, 0, x_720);
return x_730;
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_782 = lean_ctor_get(x_730, 1);
lean_inc(x_782);
lean_dec(x_730);
x_783 = l_Array_empty___closed__1;
x_784 = lean_array_push(x_783, x_712);
x_785 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_786 = lean_array_push(x_784, x_785);
x_787 = l_Lean_mkTermIdFromIdent___closed__2;
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_790 = lean_array_push(x_789, x_788);
x_791 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_790);
x_793 = lean_array_push(x_783, x_792);
x_794 = l_Lean_nullKind___closed__2;
x_795 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_793);
x_796 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_797 = lean_array_push(x_796, x_795);
x_798 = lean_array_push(x_797, x_785);
x_799 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_800 = lean_array_push(x_798, x_799);
x_801 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_802 = lean_array_push(x_800, x_801);
lean_inc(x_14);
x_803 = lean_array_push(x_783, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_804 = x_14;
} else {
 lean_dec_ref(x_14);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_794);
lean_ctor_set(x_805, 1, x_803);
x_806 = lean_array_push(x_783, x_805);
x_807 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_808 = lean_array_push(x_806, x_807);
x_809 = lean_array_push(x_808, x_726);
x_810 = l_Lean_Parser_Term_matchAlt___closed__2;
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_809);
x_812 = lean_array_push(x_783, x_811);
x_813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_813, 0, x_794);
lean_ctor_set(x_813, 1, x_812);
x_814 = lean_array_push(x_802, x_813);
x_815 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_816 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_816, 0, x_815);
lean_ctor_set(x_816, 1, x_814);
x_817 = lean_box(x_709);
lean_ctor_set(x_721, 1, x_817);
lean_ctor_set(x_721, 0, x_816);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_720);
lean_ctor_set(x_818, 1, x_782);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_819 = lean_ctor_get(x_721, 0);
lean_inc(x_819);
lean_dec(x_721);
x_820 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_722);
lean_dec(x_5);
x_821 = lean_ctor_get(x_820, 1);
lean_inc(x_821);
lean_dec(x_820);
x_822 = l_Lean_Elab_Term_getMainModule___rarg(x_821);
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_824 = x_822;
} else {
 lean_dec_ref(x_822);
 x_824 = lean_box(0);
}
x_825 = l_Array_empty___closed__1;
x_826 = lean_array_push(x_825, x_712);
x_827 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_828 = lean_array_push(x_826, x_827);
x_829 = l_Lean_mkTermIdFromIdent___closed__2;
x_830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_828);
x_831 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_832 = lean_array_push(x_831, x_830);
x_833 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_832);
x_835 = lean_array_push(x_825, x_834);
x_836 = l_Lean_nullKind___closed__2;
x_837 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_835);
x_838 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_839 = lean_array_push(x_838, x_837);
x_840 = lean_array_push(x_839, x_827);
x_841 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_842 = lean_array_push(x_840, x_841);
x_843 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_844 = lean_array_push(x_842, x_843);
lean_inc(x_14);
x_845 = lean_array_push(x_825, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_846 = x_14;
} else {
 lean_dec_ref(x_14);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_836);
lean_ctor_set(x_847, 1, x_845);
x_848 = lean_array_push(x_825, x_847);
x_849 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_850 = lean_array_push(x_848, x_849);
x_851 = lean_array_push(x_850, x_819);
x_852 = l_Lean_Parser_Term_matchAlt___closed__2;
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_851);
x_854 = lean_array_push(x_825, x_853);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_836);
lean_ctor_set(x_855, 1, x_854);
x_856 = lean_array_push(x_844, x_855);
x_857 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_858 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_856);
x_859 = lean_box(x_709);
x_860 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_860, 1, x_859);
lean_ctor_set(x_720, 1, x_860);
if (lean_is_scalar(x_824)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_824;
}
lean_ctor_set(x_861, 0, x_720);
lean_ctor_set(x_861, 1, x_823);
return x_861;
}
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_862 = lean_ctor_get(x_720, 0);
lean_inc(x_862);
lean_dec(x_720);
x_863 = lean_ctor_get(x_721, 0);
lean_inc(x_863);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_864 = x_721;
} else {
 lean_dec_ref(x_721);
 x_864 = lean_box(0);
}
x_865 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_722);
lean_dec(x_5);
x_866 = lean_ctor_get(x_865, 1);
lean_inc(x_866);
lean_dec(x_865);
x_867 = l_Lean_Elab_Term_getMainModule___rarg(x_866);
x_868 = lean_ctor_get(x_867, 1);
lean_inc(x_868);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_869 = x_867;
} else {
 lean_dec_ref(x_867);
 x_869 = lean_box(0);
}
x_870 = l_Array_empty___closed__1;
x_871 = lean_array_push(x_870, x_712);
x_872 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_873 = lean_array_push(x_871, x_872);
x_874 = l_Lean_mkTermIdFromIdent___closed__2;
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_873);
x_876 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_877 = lean_array_push(x_876, x_875);
x_878 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_878);
lean_ctor_set(x_879, 1, x_877);
x_880 = lean_array_push(x_870, x_879);
x_881 = l_Lean_nullKind___closed__2;
x_882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_880);
x_883 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_884 = lean_array_push(x_883, x_882);
x_885 = lean_array_push(x_884, x_872);
x_886 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_887 = lean_array_push(x_885, x_886);
x_888 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_889 = lean_array_push(x_887, x_888);
lean_inc(x_14);
x_890 = lean_array_push(x_870, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_891 = x_14;
} else {
 lean_dec_ref(x_14);
 x_891 = lean_box(0);
}
if (lean_is_scalar(x_891)) {
 x_892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_892 = x_891;
}
lean_ctor_set(x_892, 0, x_881);
lean_ctor_set(x_892, 1, x_890);
x_893 = lean_array_push(x_870, x_892);
x_894 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_895 = lean_array_push(x_893, x_894);
x_896 = lean_array_push(x_895, x_863);
x_897 = l_Lean_Parser_Term_matchAlt___closed__2;
x_898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_898, 0, x_897);
lean_ctor_set(x_898, 1, x_896);
x_899 = lean_array_push(x_870, x_898);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_881);
lean_ctor_set(x_900, 1, x_899);
x_901 = lean_array_push(x_889, x_900);
x_902 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_901);
x_904 = lean_box(x_709);
if (lean_is_scalar(x_864)) {
 x_905 = lean_alloc_ctor(0, 2, 0);
} else {
 x_905 = x_864;
}
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
x_906 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_906, 0, x_862);
lean_ctor_set(x_906, 1, x_905);
if (lean_is_scalar(x_869)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_869;
}
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_868);
return x_907;
}
}
else
{
uint8_t x_908; 
lean_dec(x_712);
lean_dec(x_14);
lean_dec(x_5);
x_908 = !lean_is_exclusive(x_719);
if (x_908 == 0)
{
return x_719;
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_909 = lean_ctor_get(x_719, 0);
x_910 = lean_ctor_get(x_719, 1);
lean_inc(x_910);
lean_inc(x_909);
lean_dec(x_719);
x_911 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_911, 0, x_909);
lean_ctor_set(x_911, 1, x_910);
return x_911;
}
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; uint8_t x_915; 
lean_dec(x_14);
x_912 = lean_ctor_get(x_710, 0);
lean_inc(x_912);
lean_dec(x_710);
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = l_Lean_Syntax_isNone(x_914);
lean_dec(x_914);
if (x_915 == 0)
{
lean_object* x_916; lean_object* x_917; uint8_t x_918; 
lean_dec(x_913);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_916 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_917 = l_Lean_Elab_Term_throwErrorAt___rarg(x_708, x_916, x_5, x_6);
lean_dec(x_708);
x_918 = !lean_is_exclusive(x_917);
if (x_918 == 0)
{
return x_917;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_917, 0);
x_920 = lean_ctor_get(x_917, 1);
lean_inc(x_920);
lean_inc(x_919);
lean_dec(x_917);
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_922 = l_Lean_mkHole(x_708);
lean_dec(x_708);
x_923 = lean_unsigned_to_nat(1u);
x_924 = lean_nat_add(x_3, x_923);
lean_dec(x_3);
x_925 = l_Lean_Elab_Term_mkExplicitBinder(x_913, x_922);
x_926 = lean_array_push(x_4, x_925);
x_3 = x_924;
x_4 = x_926;
goto _start;
}
}
}
else
{
lean_object* x_928; lean_object* x_929; uint8_t x_930; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_928 = lean_unsigned_to_nat(1u);
x_929 = l_Lean_Syntax_getArg(x_14, x_928);
x_930 = l_Lean_Syntax_isNone(x_929);
if (x_930 == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; 
x_931 = lean_unsigned_to_nat(0u);
x_932 = l_Lean_Syntax_getArg(x_929, x_931);
x_933 = l_Lean_Syntax_getArg(x_929, x_928);
lean_dec(x_929);
x_934 = l_Lean_Syntax_isNone(x_933);
if (x_934 == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; uint8_t x_942; 
x_935 = l_Lean_Syntax_getArg(x_933, x_931);
lean_dec(x_933);
lean_inc(x_935);
x_936 = l_Lean_Syntax_getKind(x_935);
x_937 = lean_name_mk_string(x_19, x_33);
x_938 = lean_name_mk_string(x_937, x_254);
x_939 = lean_name_mk_string(x_938, x_476);
x_940 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_941 = lean_name_mk_string(x_939, x_940);
x_942 = lean_name_eq(x_936, x_941);
lean_dec(x_941);
lean_dec(x_936);
if (x_942 == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec(x_935);
lean_dec(x_932);
x_943 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_943, 1);
lean_inc(x_945);
lean_dec(x_943);
x_946 = lean_nat_add(x_3, x_928);
lean_dec(x_3);
x_947 = l_Lean_mkHole(x_14);
lean_inc(x_944);
x_948 = l_Lean_Elab_Term_mkExplicitBinder(x_944, x_947);
x_949 = lean_array_push(x_4, x_948);
lean_inc(x_5);
x_950 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_946, x_949, x_5, x_945);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_951, 1);
lean_inc(x_952);
x_953 = lean_ctor_get(x_950, 1);
lean_inc(x_953);
lean_dec(x_950);
x_954 = !lean_is_exclusive(x_951);
if (x_954 == 0)
{
lean_object* x_955; uint8_t x_956; 
x_955 = lean_ctor_get(x_951, 1);
lean_dec(x_955);
x_956 = !lean_is_exclusive(x_952);
if (x_956 == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; 
x_957 = lean_ctor_get(x_952, 0);
x_958 = lean_ctor_get(x_952, 1);
lean_dec(x_958);
x_959 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_953);
lean_dec(x_5);
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
lean_dec(x_959);
x_961 = l_Lean_Elab_Term_getMainModule___rarg(x_960);
x_962 = !lean_is_exclusive(x_961);
if (x_962 == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; uint8_t x_985; 
x_963 = lean_ctor_get(x_961, 0);
lean_dec(x_963);
x_964 = l_Array_empty___closed__1;
x_965 = lean_array_push(x_964, x_944);
x_966 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_967 = lean_array_push(x_965, x_966);
x_968 = l_Lean_mkTermIdFromIdent___closed__2;
x_969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_969, 0, x_968);
lean_ctor_set(x_969, 1, x_967);
x_970 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_971 = lean_array_push(x_970, x_969);
x_972 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_972);
lean_ctor_set(x_973, 1, x_971);
x_974 = lean_array_push(x_964, x_973);
x_975 = l_Lean_nullKind___closed__2;
x_976 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_976, 0, x_975);
lean_ctor_set(x_976, 1, x_974);
x_977 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_978 = lean_array_push(x_977, x_976);
x_979 = lean_array_push(x_978, x_966);
x_980 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_981 = lean_array_push(x_979, x_980);
x_982 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_983 = lean_array_push(x_981, x_982);
lean_inc(x_14);
x_984 = lean_array_push(x_964, x_14);
x_985 = !lean_is_exclusive(x_14);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; lean_object* x_1000; 
x_986 = lean_ctor_get(x_14, 1);
lean_dec(x_986);
x_987 = lean_ctor_get(x_14, 0);
lean_dec(x_987);
lean_ctor_set(x_14, 1, x_984);
lean_ctor_set(x_14, 0, x_975);
x_988 = lean_array_push(x_964, x_14);
x_989 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_990 = lean_array_push(x_988, x_989);
x_991 = lean_array_push(x_990, x_957);
x_992 = l_Lean_Parser_Term_matchAlt___closed__2;
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_991);
x_994 = lean_array_push(x_964, x_993);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_975);
lean_ctor_set(x_995, 1, x_994);
x_996 = lean_array_push(x_983, x_995);
x_997 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_996);
x_999 = 1;
x_1000 = lean_box(x_999);
lean_ctor_set(x_952, 1, x_1000);
lean_ctor_set(x_952, 0, x_998);
lean_ctor_set(x_961, 0, x_951);
return x_961;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; lean_object* x_1014; 
lean_dec(x_14);
x_1001 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1001, 0, x_975);
lean_ctor_set(x_1001, 1, x_984);
x_1002 = lean_array_push(x_964, x_1001);
x_1003 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1004 = lean_array_push(x_1002, x_1003);
x_1005 = lean_array_push(x_1004, x_957);
x_1006 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1007 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_1005);
x_1008 = lean_array_push(x_964, x_1007);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_975);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = lean_array_push(x_983, x_1009);
x_1011 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_1010);
x_1013 = 1;
x_1014 = lean_box(x_1013);
lean_ctor_set(x_952, 1, x_1014);
lean_ctor_set(x_952, 0, x_1012);
lean_ctor_set(x_961, 0, x_951);
return x_961;
}
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; uint8_t x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1015 = lean_ctor_get(x_961, 1);
lean_inc(x_1015);
lean_dec(x_961);
x_1016 = l_Array_empty___closed__1;
x_1017 = lean_array_push(x_1016, x_944);
x_1018 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1019 = lean_array_push(x_1017, x_1018);
x_1020 = l_Lean_mkTermIdFromIdent___closed__2;
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1020);
lean_ctor_set(x_1021, 1, x_1019);
x_1022 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1023 = lean_array_push(x_1022, x_1021);
x_1024 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1024);
lean_ctor_set(x_1025, 1, x_1023);
x_1026 = lean_array_push(x_1016, x_1025);
x_1027 = l_Lean_nullKind___closed__2;
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1027);
lean_ctor_set(x_1028, 1, x_1026);
x_1029 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1030 = lean_array_push(x_1029, x_1028);
x_1031 = lean_array_push(x_1030, x_1018);
x_1032 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1033 = lean_array_push(x_1031, x_1032);
x_1034 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1035 = lean_array_push(x_1033, x_1034);
lean_inc(x_14);
x_1036 = lean_array_push(x_1016, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1037 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1037 = lean_box(0);
}
if (lean_is_scalar(x_1037)) {
 x_1038 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1038 = x_1037;
}
lean_ctor_set(x_1038, 0, x_1027);
lean_ctor_set(x_1038, 1, x_1036);
x_1039 = lean_array_push(x_1016, x_1038);
x_1040 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1041 = lean_array_push(x_1039, x_1040);
x_1042 = lean_array_push(x_1041, x_957);
x_1043 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1044 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_1042);
x_1045 = lean_array_push(x_1016, x_1044);
x_1046 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1046, 0, x_1027);
lean_ctor_set(x_1046, 1, x_1045);
x_1047 = lean_array_push(x_1035, x_1046);
x_1048 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1049 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_1047);
x_1050 = 1;
x_1051 = lean_box(x_1050);
lean_ctor_set(x_952, 1, x_1051);
lean_ctor_set(x_952, 0, x_1049);
x_1052 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1052, 0, x_951);
lean_ctor_set(x_1052, 1, x_1015);
return x_1052;
}
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; uint8_t x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1053 = lean_ctor_get(x_952, 0);
lean_inc(x_1053);
lean_dec(x_952);
x_1054 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_953);
lean_dec(x_5);
x_1055 = lean_ctor_get(x_1054, 1);
lean_inc(x_1055);
lean_dec(x_1054);
x_1056 = l_Lean_Elab_Term_getMainModule___rarg(x_1055);
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1058 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1058 = lean_box(0);
}
x_1059 = l_Array_empty___closed__1;
x_1060 = lean_array_push(x_1059, x_944);
x_1061 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1062 = lean_array_push(x_1060, x_1061);
x_1063 = l_Lean_mkTermIdFromIdent___closed__2;
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1063);
lean_ctor_set(x_1064, 1, x_1062);
x_1065 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1066 = lean_array_push(x_1065, x_1064);
x_1067 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1068 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1068, 0, x_1067);
lean_ctor_set(x_1068, 1, x_1066);
x_1069 = lean_array_push(x_1059, x_1068);
x_1070 = l_Lean_nullKind___closed__2;
x_1071 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1069);
x_1072 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1073 = lean_array_push(x_1072, x_1071);
x_1074 = lean_array_push(x_1073, x_1061);
x_1075 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1076 = lean_array_push(x_1074, x_1075);
x_1077 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1078 = lean_array_push(x_1076, x_1077);
lean_inc(x_14);
x_1079 = lean_array_push(x_1059, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1080 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1080 = lean_box(0);
}
if (lean_is_scalar(x_1080)) {
 x_1081 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1081 = x_1080;
}
lean_ctor_set(x_1081, 0, x_1070);
lean_ctor_set(x_1081, 1, x_1079);
x_1082 = lean_array_push(x_1059, x_1081);
x_1083 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1084 = lean_array_push(x_1082, x_1083);
x_1085 = lean_array_push(x_1084, x_1053);
x_1086 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1087, 0, x_1086);
lean_ctor_set(x_1087, 1, x_1085);
x_1088 = lean_array_push(x_1059, x_1087);
x_1089 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1089, 0, x_1070);
lean_ctor_set(x_1089, 1, x_1088);
x_1090 = lean_array_push(x_1078, x_1089);
x_1091 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1091);
lean_ctor_set(x_1092, 1, x_1090);
x_1093 = 1;
x_1094 = lean_box(x_1093);
x_1095 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1095, 0, x_1092);
lean_ctor_set(x_1095, 1, x_1094);
lean_ctor_set(x_951, 1, x_1095);
if (lean_is_scalar(x_1058)) {
 x_1096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1096 = x_1058;
}
lean_ctor_set(x_1096, 0, x_951);
lean_ctor_set(x_1096, 1, x_1057);
return x_1096;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1097 = lean_ctor_get(x_951, 0);
lean_inc(x_1097);
lean_dec(x_951);
x_1098 = lean_ctor_get(x_952, 0);
lean_inc(x_1098);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_1099 = x_952;
} else {
 lean_dec_ref(x_952);
 x_1099 = lean_box(0);
}
x_1100 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_953);
lean_dec(x_5);
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc(x_1101);
lean_dec(x_1100);
x_1102 = l_Lean_Elab_Term_getMainModule___rarg(x_1101);
x_1103 = lean_ctor_get(x_1102, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_1102)) {
 lean_ctor_release(x_1102, 0);
 lean_ctor_release(x_1102, 1);
 x_1104 = x_1102;
} else {
 lean_dec_ref(x_1102);
 x_1104 = lean_box(0);
}
x_1105 = l_Array_empty___closed__1;
x_1106 = lean_array_push(x_1105, x_944);
x_1107 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1108 = lean_array_push(x_1106, x_1107);
x_1109 = l_Lean_mkTermIdFromIdent___closed__2;
x_1110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1110, 0, x_1109);
lean_ctor_set(x_1110, 1, x_1108);
x_1111 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1112 = lean_array_push(x_1111, x_1110);
x_1113 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1113);
lean_ctor_set(x_1114, 1, x_1112);
x_1115 = lean_array_push(x_1105, x_1114);
x_1116 = l_Lean_nullKind___closed__2;
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1115);
x_1118 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1119 = lean_array_push(x_1118, x_1117);
x_1120 = lean_array_push(x_1119, x_1107);
x_1121 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1122 = lean_array_push(x_1120, x_1121);
x_1123 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1124 = lean_array_push(x_1122, x_1123);
lean_inc(x_14);
x_1125 = lean_array_push(x_1105, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1126 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1126 = lean_box(0);
}
if (lean_is_scalar(x_1126)) {
 x_1127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1127 = x_1126;
}
lean_ctor_set(x_1127, 0, x_1116);
lean_ctor_set(x_1127, 1, x_1125);
x_1128 = lean_array_push(x_1105, x_1127);
x_1129 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1130 = lean_array_push(x_1128, x_1129);
x_1131 = lean_array_push(x_1130, x_1098);
x_1132 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1133, 0, x_1132);
lean_ctor_set(x_1133, 1, x_1131);
x_1134 = lean_array_push(x_1105, x_1133);
x_1135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1135, 0, x_1116);
lean_ctor_set(x_1135, 1, x_1134);
x_1136 = lean_array_push(x_1124, x_1135);
x_1137 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1138, 0, x_1137);
lean_ctor_set(x_1138, 1, x_1136);
x_1139 = 1;
x_1140 = lean_box(x_1139);
if (lean_is_scalar(x_1099)) {
 x_1141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1141 = x_1099;
}
lean_ctor_set(x_1141, 0, x_1138);
lean_ctor_set(x_1141, 1, x_1140);
x_1142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1142, 0, x_1097);
lean_ctor_set(x_1142, 1, x_1141);
if (lean_is_scalar(x_1104)) {
 x_1143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1143 = x_1104;
}
lean_ctor_set(x_1143, 0, x_1142);
lean_ctor_set(x_1143, 1, x_1103);
return x_1143;
}
}
else
{
uint8_t x_1144; 
lean_dec(x_944);
lean_dec(x_14);
lean_dec(x_5);
x_1144 = !lean_is_exclusive(x_950);
if (x_1144 == 0)
{
return x_950;
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_950, 0);
x_1146 = lean_ctor_get(x_950, 1);
lean_inc(x_1146);
lean_inc(x_1145);
lean_dec(x_950);
x_1147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1147, 0, x_1145);
lean_ctor_set(x_1147, 1, x_1146);
return x_1147;
}
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = l_Lean_Syntax_getArg(x_935, x_928);
lean_dec(x_935);
x_1149 = l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(x_932, x_5, x_6);
x_1150 = lean_ctor_get(x_1149, 0);
lean_inc(x_1150);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1148);
x_1151 = lean_ctor_get(x_1149, 1);
lean_inc(x_1151);
lean_dec(x_1149);
x_1152 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_1151);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_nat_add(x_3, x_928);
lean_dec(x_3);
x_1156 = l_Lean_mkHole(x_14);
lean_inc(x_1153);
x_1157 = l_Lean_Elab_Term_mkExplicitBinder(x_1153, x_1156);
x_1158 = lean_array_push(x_4, x_1157);
lean_inc(x_5);
x_1159 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_1155, x_1158, x_5, x_1154);
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; uint8_t x_1163; 
x_1160 = lean_ctor_get(x_1159, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1160, 1);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1159, 1);
lean_inc(x_1162);
lean_dec(x_1159);
x_1163 = !lean_is_exclusive(x_1160);
if (x_1163 == 0)
{
lean_object* x_1164; uint8_t x_1165; 
x_1164 = lean_ctor_get(x_1160, 1);
lean_dec(x_1164);
x_1165 = !lean_is_exclusive(x_1161);
if (x_1165 == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; uint8_t x_1171; 
x_1166 = lean_ctor_get(x_1161, 0);
x_1167 = lean_ctor_get(x_1161, 1);
lean_dec(x_1167);
x_1168 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1162);
lean_dec(x_5);
x_1169 = lean_ctor_get(x_1168, 1);
lean_inc(x_1169);
lean_dec(x_1168);
x_1170 = l_Lean_Elab_Term_getMainModule___rarg(x_1169);
x_1171 = !lean_is_exclusive(x_1170);
if (x_1171 == 0)
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; uint8_t x_1194; 
x_1172 = lean_ctor_get(x_1170, 0);
lean_dec(x_1172);
x_1173 = l_Array_empty___closed__1;
x_1174 = lean_array_push(x_1173, x_1153);
x_1175 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1176 = lean_array_push(x_1174, x_1175);
x_1177 = l_Lean_mkTermIdFromIdent___closed__2;
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1176);
x_1179 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1180 = lean_array_push(x_1179, x_1178);
x_1181 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1181);
lean_ctor_set(x_1182, 1, x_1180);
x_1183 = lean_array_push(x_1173, x_1182);
x_1184 = l_Lean_nullKind___closed__2;
x_1185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1185, 0, x_1184);
lean_ctor_set(x_1185, 1, x_1183);
x_1186 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1187 = lean_array_push(x_1186, x_1185);
x_1188 = lean_array_push(x_1187, x_1175);
x_1189 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1190 = lean_array_push(x_1188, x_1189);
x_1191 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1192 = lean_array_push(x_1190, x_1191);
lean_inc(x_14);
x_1193 = lean_array_push(x_1173, x_14);
x_1194 = !lean_is_exclusive(x_14);
if (x_1194 == 0)
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; lean_object* x_1209; 
x_1195 = lean_ctor_get(x_14, 1);
lean_dec(x_1195);
x_1196 = lean_ctor_get(x_14, 0);
lean_dec(x_1196);
lean_ctor_set(x_14, 1, x_1193);
lean_ctor_set(x_14, 0, x_1184);
x_1197 = lean_array_push(x_1173, x_14);
x_1198 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1199 = lean_array_push(x_1197, x_1198);
x_1200 = lean_array_push(x_1199, x_1166);
x_1201 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1202, 0, x_1201);
lean_ctor_set(x_1202, 1, x_1200);
x_1203 = lean_array_push(x_1173, x_1202);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1184);
lean_ctor_set(x_1204, 1, x_1203);
x_1205 = lean_array_push(x_1192, x_1204);
x_1206 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1206);
lean_ctor_set(x_1207, 1, x_1205);
x_1208 = 1;
x_1209 = lean_box(x_1208);
lean_ctor_set(x_1161, 1, x_1209);
lean_ctor_set(x_1161, 0, x_1207);
lean_ctor_set(x_1170, 0, x_1160);
return x_1170;
}
else
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; lean_object* x_1223; 
lean_dec(x_14);
x_1210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1210, 0, x_1184);
lean_ctor_set(x_1210, 1, x_1193);
x_1211 = lean_array_push(x_1173, x_1210);
x_1212 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1213 = lean_array_push(x_1211, x_1212);
x_1214 = lean_array_push(x_1213, x_1166);
x_1215 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1216, 0, x_1215);
lean_ctor_set(x_1216, 1, x_1214);
x_1217 = lean_array_push(x_1173, x_1216);
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1184);
lean_ctor_set(x_1218, 1, x_1217);
x_1219 = lean_array_push(x_1192, x_1218);
x_1220 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = 1;
x_1223 = lean_box(x_1222);
lean_ctor_set(x_1161, 1, x_1223);
lean_ctor_set(x_1161, 0, x_1221);
lean_ctor_set(x_1170, 0, x_1160);
return x_1170;
}
}
else
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; uint8_t x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1224 = lean_ctor_get(x_1170, 1);
lean_inc(x_1224);
lean_dec(x_1170);
x_1225 = l_Array_empty___closed__1;
x_1226 = lean_array_push(x_1225, x_1153);
x_1227 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1228 = lean_array_push(x_1226, x_1227);
x_1229 = l_Lean_mkTermIdFromIdent___closed__2;
x_1230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1230, 0, x_1229);
lean_ctor_set(x_1230, 1, x_1228);
x_1231 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1232 = lean_array_push(x_1231, x_1230);
x_1233 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1234, 0, x_1233);
lean_ctor_set(x_1234, 1, x_1232);
x_1235 = lean_array_push(x_1225, x_1234);
x_1236 = l_Lean_nullKind___closed__2;
x_1237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1237, 0, x_1236);
lean_ctor_set(x_1237, 1, x_1235);
x_1238 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1239 = lean_array_push(x_1238, x_1237);
x_1240 = lean_array_push(x_1239, x_1227);
x_1241 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1242 = lean_array_push(x_1240, x_1241);
x_1243 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1244 = lean_array_push(x_1242, x_1243);
lean_inc(x_14);
x_1245 = lean_array_push(x_1225, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1246 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1246 = lean_box(0);
}
if (lean_is_scalar(x_1246)) {
 x_1247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1247 = x_1246;
}
lean_ctor_set(x_1247, 0, x_1236);
lean_ctor_set(x_1247, 1, x_1245);
x_1248 = lean_array_push(x_1225, x_1247);
x_1249 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1250 = lean_array_push(x_1248, x_1249);
x_1251 = lean_array_push(x_1250, x_1166);
x_1252 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1253, 0, x_1252);
lean_ctor_set(x_1253, 1, x_1251);
x_1254 = lean_array_push(x_1225, x_1253);
x_1255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1255, 0, x_1236);
lean_ctor_set(x_1255, 1, x_1254);
x_1256 = lean_array_push(x_1244, x_1255);
x_1257 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1258, 0, x_1257);
lean_ctor_set(x_1258, 1, x_1256);
x_1259 = 1;
x_1260 = lean_box(x_1259);
lean_ctor_set(x_1161, 1, x_1260);
lean_ctor_set(x_1161, 0, x_1258);
x_1261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1261, 0, x_1160);
lean_ctor_set(x_1261, 1, x_1224);
return x_1261;
}
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; uint8_t x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1262 = lean_ctor_get(x_1161, 0);
lean_inc(x_1262);
lean_dec(x_1161);
x_1263 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1162);
lean_dec(x_5);
x_1264 = lean_ctor_get(x_1263, 1);
lean_inc(x_1264);
lean_dec(x_1263);
x_1265 = l_Lean_Elab_Term_getMainModule___rarg(x_1264);
x_1266 = lean_ctor_get(x_1265, 1);
lean_inc(x_1266);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 x_1267 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1267 = lean_box(0);
}
x_1268 = l_Array_empty___closed__1;
x_1269 = lean_array_push(x_1268, x_1153);
x_1270 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1271 = lean_array_push(x_1269, x_1270);
x_1272 = l_Lean_mkTermIdFromIdent___closed__2;
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1272);
lean_ctor_set(x_1273, 1, x_1271);
x_1274 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1275 = lean_array_push(x_1274, x_1273);
x_1276 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1276);
lean_ctor_set(x_1277, 1, x_1275);
x_1278 = lean_array_push(x_1268, x_1277);
x_1279 = l_Lean_nullKind___closed__2;
x_1280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1280, 0, x_1279);
lean_ctor_set(x_1280, 1, x_1278);
x_1281 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1282 = lean_array_push(x_1281, x_1280);
x_1283 = lean_array_push(x_1282, x_1270);
x_1284 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1285 = lean_array_push(x_1283, x_1284);
x_1286 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1287 = lean_array_push(x_1285, x_1286);
lean_inc(x_14);
x_1288 = lean_array_push(x_1268, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1289 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1289 = lean_box(0);
}
if (lean_is_scalar(x_1289)) {
 x_1290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1290 = x_1289;
}
lean_ctor_set(x_1290, 0, x_1279);
lean_ctor_set(x_1290, 1, x_1288);
x_1291 = lean_array_push(x_1268, x_1290);
x_1292 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1293 = lean_array_push(x_1291, x_1292);
x_1294 = lean_array_push(x_1293, x_1262);
x_1295 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1296, 0, x_1295);
lean_ctor_set(x_1296, 1, x_1294);
x_1297 = lean_array_push(x_1268, x_1296);
x_1298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1298, 0, x_1279);
lean_ctor_set(x_1298, 1, x_1297);
x_1299 = lean_array_push(x_1287, x_1298);
x_1300 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1301, 0, x_1300);
lean_ctor_set(x_1301, 1, x_1299);
x_1302 = 1;
x_1303 = lean_box(x_1302);
x_1304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1304, 0, x_1301);
lean_ctor_set(x_1304, 1, x_1303);
lean_ctor_set(x_1160, 1, x_1304);
if (lean_is_scalar(x_1267)) {
 x_1305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1305 = x_1267;
}
lean_ctor_set(x_1305, 0, x_1160);
lean_ctor_set(x_1305, 1, x_1266);
return x_1305;
}
}
else
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; uint8_t x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1306 = lean_ctor_get(x_1160, 0);
lean_inc(x_1306);
lean_dec(x_1160);
x_1307 = lean_ctor_get(x_1161, 0);
lean_inc(x_1307);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 lean_ctor_release(x_1161, 1);
 x_1308 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1308 = lean_box(0);
}
x_1309 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1162);
lean_dec(x_5);
x_1310 = lean_ctor_get(x_1309, 1);
lean_inc(x_1310);
lean_dec(x_1309);
x_1311 = l_Lean_Elab_Term_getMainModule___rarg(x_1310);
x_1312 = lean_ctor_get(x_1311, 1);
lean_inc(x_1312);
if (lean_is_exclusive(x_1311)) {
 lean_ctor_release(x_1311, 0);
 lean_ctor_release(x_1311, 1);
 x_1313 = x_1311;
} else {
 lean_dec_ref(x_1311);
 x_1313 = lean_box(0);
}
x_1314 = l_Array_empty___closed__1;
x_1315 = lean_array_push(x_1314, x_1153);
x_1316 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1317 = lean_array_push(x_1315, x_1316);
x_1318 = l_Lean_mkTermIdFromIdent___closed__2;
x_1319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1319, 0, x_1318);
lean_ctor_set(x_1319, 1, x_1317);
x_1320 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1321 = lean_array_push(x_1320, x_1319);
x_1322 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1323, 0, x_1322);
lean_ctor_set(x_1323, 1, x_1321);
x_1324 = lean_array_push(x_1314, x_1323);
x_1325 = l_Lean_nullKind___closed__2;
x_1326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1326, 0, x_1325);
lean_ctor_set(x_1326, 1, x_1324);
x_1327 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1328 = lean_array_push(x_1327, x_1326);
x_1329 = lean_array_push(x_1328, x_1316);
x_1330 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1331 = lean_array_push(x_1329, x_1330);
x_1332 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1333 = lean_array_push(x_1331, x_1332);
lean_inc(x_14);
x_1334 = lean_array_push(x_1314, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1335 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1335 = lean_box(0);
}
if (lean_is_scalar(x_1335)) {
 x_1336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1336 = x_1335;
}
lean_ctor_set(x_1336, 0, x_1325);
lean_ctor_set(x_1336, 1, x_1334);
x_1337 = lean_array_push(x_1314, x_1336);
x_1338 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1339 = lean_array_push(x_1337, x_1338);
x_1340 = lean_array_push(x_1339, x_1307);
x_1341 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1342, 0, x_1341);
lean_ctor_set(x_1342, 1, x_1340);
x_1343 = lean_array_push(x_1314, x_1342);
x_1344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1344, 0, x_1325);
lean_ctor_set(x_1344, 1, x_1343);
x_1345 = lean_array_push(x_1333, x_1344);
x_1346 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1347, 0, x_1346);
lean_ctor_set(x_1347, 1, x_1345);
x_1348 = 1;
x_1349 = lean_box(x_1348);
if (lean_is_scalar(x_1308)) {
 x_1350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1350 = x_1308;
}
lean_ctor_set(x_1350, 0, x_1347);
lean_ctor_set(x_1350, 1, x_1349);
x_1351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1351, 0, x_1306);
lean_ctor_set(x_1351, 1, x_1350);
if (lean_is_scalar(x_1313)) {
 x_1352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1352 = x_1313;
}
lean_ctor_set(x_1352, 0, x_1351);
lean_ctor_set(x_1352, 1, x_1312);
return x_1352;
}
}
else
{
uint8_t x_1353; 
lean_dec(x_1153);
lean_dec(x_14);
lean_dec(x_5);
x_1353 = !lean_is_exclusive(x_1159);
if (x_1353 == 0)
{
return x_1159;
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1354 = lean_ctor_get(x_1159, 0);
x_1355 = lean_ctor_get(x_1159, 1);
lean_inc(x_1355);
lean_inc(x_1354);
lean_dec(x_1159);
x_1356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1356, 0, x_1354);
lean_ctor_set(x_1356, 1, x_1355);
return x_1356;
}
}
}
else
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_14);
x_1357 = lean_ctor_get(x_1149, 1);
lean_inc(x_1357);
lean_dec(x_1149);
x_1358 = lean_ctor_get(x_1150, 0);
lean_inc(x_1358);
lean_dec(x_1150);
x_1359 = lean_nat_add(x_3, x_928);
lean_dec(x_3);
x_1360 = x_1358;
x_1361 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(x_1148, x_931, x_1360);
x_1362 = x_1361;
x_1363 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1362, x_1362, x_931, x_4);
lean_dec(x_1362);
x_3 = x_1359;
x_4 = x_1363;
x_6 = x_1357;
goto _start;
}
}
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
lean_dec(x_933);
lean_dec(x_932);
x_1365 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
lean_dec(x_1365);
x_1368 = lean_nat_add(x_3, x_928);
lean_dec(x_3);
x_1369 = l_Lean_mkHole(x_14);
lean_inc(x_1366);
x_1370 = l_Lean_Elab_Term_mkExplicitBinder(x_1366, x_1369);
x_1371 = lean_array_push(x_4, x_1370);
lean_inc(x_5);
x_1372 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_1368, x_1371, x_5, x_1367);
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; uint8_t x_1376; 
x_1373 = lean_ctor_get(x_1372, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1373, 1);
lean_inc(x_1374);
x_1375 = lean_ctor_get(x_1372, 1);
lean_inc(x_1375);
lean_dec(x_1372);
x_1376 = !lean_is_exclusive(x_1373);
if (x_1376 == 0)
{
lean_object* x_1377; uint8_t x_1378; 
x_1377 = lean_ctor_get(x_1373, 1);
lean_dec(x_1377);
x_1378 = !lean_is_exclusive(x_1374);
if (x_1378 == 0)
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; uint8_t x_1384; 
x_1379 = lean_ctor_get(x_1374, 0);
x_1380 = lean_ctor_get(x_1374, 1);
lean_dec(x_1380);
x_1381 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1375);
lean_dec(x_5);
x_1382 = lean_ctor_get(x_1381, 1);
lean_inc(x_1382);
lean_dec(x_1381);
x_1383 = l_Lean_Elab_Term_getMainModule___rarg(x_1382);
x_1384 = !lean_is_exclusive(x_1383);
if (x_1384 == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; uint8_t x_1407; 
x_1385 = lean_ctor_get(x_1383, 0);
lean_dec(x_1385);
x_1386 = l_Array_empty___closed__1;
x_1387 = lean_array_push(x_1386, x_1366);
x_1388 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1389 = lean_array_push(x_1387, x_1388);
x_1390 = l_Lean_mkTermIdFromIdent___closed__2;
x_1391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1391, 0, x_1390);
lean_ctor_set(x_1391, 1, x_1389);
x_1392 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1393 = lean_array_push(x_1392, x_1391);
x_1394 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1395, 0, x_1394);
lean_ctor_set(x_1395, 1, x_1393);
x_1396 = lean_array_push(x_1386, x_1395);
x_1397 = l_Lean_nullKind___closed__2;
x_1398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1396);
x_1399 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1400 = lean_array_push(x_1399, x_1398);
x_1401 = lean_array_push(x_1400, x_1388);
x_1402 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1403 = lean_array_push(x_1401, x_1402);
x_1404 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1405 = lean_array_push(x_1403, x_1404);
lean_inc(x_14);
x_1406 = lean_array_push(x_1386, x_14);
x_1407 = !lean_is_exclusive(x_14);
if (x_1407 == 0)
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; uint8_t x_1421; lean_object* x_1422; 
x_1408 = lean_ctor_get(x_14, 1);
lean_dec(x_1408);
x_1409 = lean_ctor_get(x_14, 0);
lean_dec(x_1409);
lean_ctor_set(x_14, 1, x_1406);
lean_ctor_set(x_14, 0, x_1397);
x_1410 = lean_array_push(x_1386, x_14);
x_1411 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1412 = lean_array_push(x_1410, x_1411);
x_1413 = lean_array_push(x_1412, x_1379);
x_1414 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1415, 0, x_1414);
lean_ctor_set(x_1415, 1, x_1413);
x_1416 = lean_array_push(x_1386, x_1415);
x_1417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1417, 0, x_1397);
lean_ctor_set(x_1417, 1, x_1416);
x_1418 = lean_array_push(x_1405, x_1417);
x_1419 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1420, 0, x_1419);
lean_ctor_set(x_1420, 1, x_1418);
x_1421 = 1;
x_1422 = lean_box(x_1421);
lean_ctor_set(x_1374, 1, x_1422);
lean_ctor_set(x_1374, 0, x_1420);
lean_ctor_set(x_1383, 0, x_1373);
return x_1383;
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; uint8_t x_1435; lean_object* x_1436; 
lean_dec(x_14);
x_1423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1423, 0, x_1397);
lean_ctor_set(x_1423, 1, x_1406);
x_1424 = lean_array_push(x_1386, x_1423);
x_1425 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1426 = lean_array_push(x_1424, x_1425);
x_1427 = lean_array_push(x_1426, x_1379);
x_1428 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1429, 0, x_1428);
lean_ctor_set(x_1429, 1, x_1427);
x_1430 = lean_array_push(x_1386, x_1429);
x_1431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1431, 0, x_1397);
lean_ctor_set(x_1431, 1, x_1430);
x_1432 = lean_array_push(x_1405, x_1431);
x_1433 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1434, 0, x_1433);
lean_ctor_set(x_1434, 1, x_1432);
x_1435 = 1;
x_1436 = lean_box(x_1435);
lean_ctor_set(x_1374, 1, x_1436);
lean_ctor_set(x_1374, 0, x_1434);
lean_ctor_set(x_1383, 0, x_1373);
return x_1383;
}
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; uint8_t x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1437 = lean_ctor_get(x_1383, 1);
lean_inc(x_1437);
lean_dec(x_1383);
x_1438 = l_Array_empty___closed__1;
x_1439 = lean_array_push(x_1438, x_1366);
x_1440 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1441 = lean_array_push(x_1439, x_1440);
x_1442 = l_Lean_mkTermIdFromIdent___closed__2;
x_1443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1443, 1, x_1441);
x_1444 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1445 = lean_array_push(x_1444, x_1443);
x_1446 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_1445);
x_1448 = lean_array_push(x_1438, x_1447);
x_1449 = l_Lean_nullKind___closed__2;
x_1450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1450, 0, x_1449);
lean_ctor_set(x_1450, 1, x_1448);
x_1451 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1452 = lean_array_push(x_1451, x_1450);
x_1453 = lean_array_push(x_1452, x_1440);
x_1454 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1455 = lean_array_push(x_1453, x_1454);
x_1456 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1457 = lean_array_push(x_1455, x_1456);
lean_inc(x_14);
x_1458 = lean_array_push(x_1438, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1459 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1459 = lean_box(0);
}
if (lean_is_scalar(x_1459)) {
 x_1460 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1460 = x_1459;
}
lean_ctor_set(x_1460, 0, x_1449);
lean_ctor_set(x_1460, 1, x_1458);
x_1461 = lean_array_push(x_1438, x_1460);
x_1462 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1463 = lean_array_push(x_1461, x_1462);
x_1464 = lean_array_push(x_1463, x_1379);
x_1465 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1466, 0, x_1465);
lean_ctor_set(x_1466, 1, x_1464);
x_1467 = lean_array_push(x_1438, x_1466);
x_1468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1468, 0, x_1449);
lean_ctor_set(x_1468, 1, x_1467);
x_1469 = lean_array_push(x_1457, x_1468);
x_1470 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1471, 0, x_1470);
lean_ctor_set(x_1471, 1, x_1469);
x_1472 = 1;
x_1473 = lean_box(x_1472);
lean_ctor_set(x_1374, 1, x_1473);
lean_ctor_set(x_1374, 0, x_1471);
x_1474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1474, 0, x_1373);
lean_ctor_set(x_1474, 1, x_1437);
return x_1474;
}
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; uint8_t x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
x_1475 = lean_ctor_get(x_1374, 0);
lean_inc(x_1475);
lean_dec(x_1374);
x_1476 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1375);
lean_dec(x_5);
x_1477 = lean_ctor_get(x_1476, 1);
lean_inc(x_1477);
lean_dec(x_1476);
x_1478 = l_Lean_Elab_Term_getMainModule___rarg(x_1477);
x_1479 = lean_ctor_get(x_1478, 1);
lean_inc(x_1479);
if (lean_is_exclusive(x_1478)) {
 lean_ctor_release(x_1478, 0);
 lean_ctor_release(x_1478, 1);
 x_1480 = x_1478;
} else {
 lean_dec_ref(x_1478);
 x_1480 = lean_box(0);
}
x_1481 = l_Array_empty___closed__1;
x_1482 = lean_array_push(x_1481, x_1366);
x_1483 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1484 = lean_array_push(x_1482, x_1483);
x_1485 = l_Lean_mkTermIdFromIdent___closed__2;
x_1486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1486, 0, x_1485);
lean_ctor_set(x_1486, 1, x_1484);
x_1487 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1488 = lean_array_push(x_1487, x_1486);
x_1489 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1490, 0, x_1489);
lean_ctor_set(x_1490, 1, x_1488);
x_1491 = lean_array_push(x_1481, x_1490);
x_1492 = l_Lean_nullKind___closed__2;
x_1493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1493, 0, x_1492);
lean_ctor_set(x_1493, 1, x_1491);
x_1494 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1495 = lean_array_push(x_1494, x_1493);
x_1496 = lean_array_push(x_1495, x_1483);
x_1497 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1498 = lean_array_push(x_1496, x_1497);
x_1499 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1500 = lean_array_push(x_1498, x_1499);
lean_inc(x_14);
x_1501 = lean_array_push(x_1481, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1502 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1502 = lean_box(0);
}
if (lean_is_scalar(x_1502)) {
 x_1503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1503 = x_1502;
}
lean_ctor_set(x_1503, 0, x_1492);
lean_ctor_set(x_1503, 1, x_1501);
x_1504 = lean_array_push(x_1481, x_1503);
x_1505 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1506 = lean_array_push(x_1504, x_1505);
x_1507 = lean_array_push(x_1506, x_1475);
x_1508 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1509, 0, x_1508);
lean_ctor_set(x_1509, 1, x_1507);
x_1510 = lean_array_push(x_1481, x_1509);
x_1511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1511, 0, x_1492);
lean_ctor_set(x_1511, 1, x_1510);
x_1512 = lean_array_push(x_1500, x_1511);
x_1513 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1514, 0, x_1513);
lean_ctor_set(x_1514, 1, x_1512);
x_1515 = 1;
x_1516 = lean_box(x_1515);
x_1517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1517, 0, x_1514);
lean_ctor_set(x_1517, 1, x_1516);
lean_ctor_set(x_1373, 1, x_1517);
if (lean_is_scalar(x_1480)) {
 x_1518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1518 = x_1480;
}
lean_ctor_set(x_1518, 0, x_1373);
lean_ctor_set(x_1518, 1, x_1479);
return x_1518;
}
}
else
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; uint8_t x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
x_1519 = lean_ctor_get(x_1373, 0);
lean_inc(x_1519);
lean_dec(x_1373);
x_1520 = lean_ctor_get(x_1374, 0);
lean_inc(x_1520);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1521 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1521 = lean_box(0);
}
x_1522 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1375);
lean_dec(x_5);
x_1523 = lean_ctor_get(x_1522, 1);
lean_inc(x_1523);
lean_dec(x_1522);
x_1524 = l_Lean_Elab_Term_getMainModule___rarg(x_1523);
x_1525 = lean_ctor_get(x_1524, 1);
lean_inc(x_1525);
if (lean_is_exclusive(x_1524)) {
 lean_ctor_release(x_1524, 0);
 lean_ctor_release(x_1524, 1);
 x_1526 = x_1524;
} else {
 lean_dec_ref(x_1524);
 x_1526 = lean_box(0);
}
x_1527 = l_Array_empty___closed__1;
x_1528 = lean_array_push(x_1527, x_1366);
x_1529 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1530 = lean_array_push(x_1528, x_1529);
x_1531 = l_Lean_mkTermIdFromIdent___closed__2;
x_1532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1532, 0, x_1531);
lean_ctor_set(x_1532, 1, x_1530);
x_1533 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1534 = lean_array_push(x_1533, x_1532);
x_1535 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1536, 0, x_1535);
lean_ctor_set(x_1536, 1, x_1534);
x_1537 = lean_array_push(x_1527, x_1536);
x_1538 = l_Lean_nullKind___closed__2;
x_1539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1539, 0, x_1538);
lean_ctor_set(x_1539, 1, x_1537);
x_1540 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1541 = lean_array_push(x_1540, x_1539);
x_1542 = lean_array_push(x_1541, x_1529);
x_1543 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1544 = lean_array_push(x_1542, x_1543);
x_1545 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1546 = lean_array_push(x_1544, x_1545);
lean_inc(x_14);
x_1547 = lean_array_push(x_1527, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1548 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1548 = lean_box(0);
}
if (lean_is_scalar(x_1548)) {
 x_1549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1549 = x_1548;
}
lean_ctor_set(x_1549, 0, x_1538);
lean_ctor_set(x_1549, 1, x_1547);
x_1550 = lean_array_push(x_1527, x_1549);
x_1551 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1552 = lean_array_push(x_1550, x_1551);
x_1553 = lean_array_push(x_1552, x_1520);
x_1554 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1555, 0, x_1554);
lean_ctor_set(x_1555, 1, x_1553);
x_1556 = lean_array_push(x_1527, x_1555);
x_1557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1557, 0, x_1538);
lean_ctor_set(x_1557, 1, x_1556);
x_1558 = lean_array_push(x_1546, x_1557);
x_1559 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1560, 0, x_1559);
lean_ctor_set(x_1560, 1, x_1558);
x_1561 = 1;
x_1562 = lean_box(x_1561);
if (lean_is_scalar(x_1521)) {
 x_1563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1563 = x_1521;
}
lean_ctor_set(x_1563, 0, x_1560);
lean_ctor_set(x_1563, 1, x_1562);
x_1564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1564, 0, x_1519);
lean_ctor_set(x_1564, 1, x_1563);
if (lean_is_scalar(x_1526)) {
 x_1565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1565 = x_1526;
}
lean_ctor_set(x_1565, 0, x_1564);
lean_ctor_set(x_1565, 1, x_1525);
return x_1565;
}
}
else
{
uint8_t x_1566; 
lean_dec(x_1366);
lean_dec(x_14);
lean_dec(x_5);
x_1566 = !lean_is_exclusive(x_1372);
if (x_1566 == 0)
{
return x_1372;
}
else
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1567 = lean_ctor_get(x_1372, 0);
x_1568 = lean_ctor_get(x_1372, 1);
lean_inc(x_1568);
lean_inc(x_1567);
lean_dec(x_1372);
x_1569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1569, 0, x_1567);
lean_ctor_set(x_1569, 1, x_1568);
return x_1569;
}
}
}
}
else
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
lean_dec(x_929);
x_1570 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_1571 = lean_ctor_get(x_1570, 0);
lean_inc(x_1571);
x_1572 = lean_ctor_get(x_1570, 1);
lean_inc(x_1572);
lean_dec(x_1570);
x_1573 = lean_nat_add(x_3, x_928);
lean_dec(x_3);
x_1574 = l_Lean_mkHole(x_14);
lean_inc(x_1571);
x_1575 = l_Lean_Elab_Term_mkExplicitBinder(x_1571, x_1574);
x_1576 = lean_array_push(x_4, x_1575);
lean_inc(x_5);
x_1577 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_1573, x_1576, x_5, x_1572);
if (lean_obj_tag(x_1577) == 0)
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; uint8_t x_1581; 
x_1578 = lean_ctor_get(x_1577, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1578, 1);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_1577, 1);
lean_inc(x_1580);
lean_dec(x_1577);
x_1581 = !lean_is_exclusive(x_1578);
if (x_1581 == 0)
{
lean_object* x_1582; uint8_t x_1583; 
x_1582 = lean_ctor_get(x_1578, 1);
lean_dec(x_1582);
x_1583 = !lean_is_exclusive(x_1579);
if (x_1583 == 0)
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; uint8_t x_1589; 
x_1584 = lean_ctor_get(x_1579, 0);
x_1585 = lean_ctor_get(x_1579, 1);
lean_dec(x_1585);
x_1586 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1580);
lean_dec(x_5);
x_1587 = lean_ctor_get(x_1586, 1);
lean_inc(x_1587);
lean_dec(x_1586);
x_1588 = l_Lean_Elab_Term_getMainModule___rarg(x_1587);
x_1589 = !lean_is_exclusive(x_1588);
if (x_1589 == 0)
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; uint8_t x_1612; 
x_1590 = lean_ctor_get(x_1588, 0);
lean_dec(x_1590);
x_1591 = l_Array_empty___closed__1;
x_1592 = lean_array_push(x_1591, x_1571);
x_1593 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1594 = lean_array_push(x_1592, x_1593);
x_1595 = l_Lean_mkTermIdFromIdent___closed__2;
x_1596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1596, 0, x_1595);
lean_ctor_set(x_1596, 1, x_1594);
x_1597 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1598 = lean_array_push(x_1597, x_1596);
x_1599 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1600, 0, x_1599);
lean_ctor_set(x_1600, 1, x_1598);
x_1601 = lean_array_push(x_1591, x_1600);
x_1602 = l_Lean_nullKind___closed__2;
x_1603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1603, 0, x_1602);
lean_ctor_set(x_1603, 1, x_1601);
x_1604 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1605 = lean_array_push(x_1604, x_1603);
x_1606 = lean_array_push(x_1605, x_1593);
x_1607 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1608 = lean_array_push(x_1606, x_1607);
x_1609 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1610 = lean_array_push(x_1608, x_1609);
lean_inc(x_14);
x_1611 = lean_array_push(x_1591, x_14);
x_1612 = !lean_is_exclusive(x_14);
if (x_1612 == 0)
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; uint8_t x_1626; lean_object* x_1627; 
x_1613 = lean_ctor_get(x_14, 1);
lean_dec(x_1613);
x_1614 = lean_ctor_get(x_14, 0);
lean_dec(x_1614);
lean_ctor_set(x_14, 1, x_1611);
lean_ctor_set(x_14, 0, x_1602);
x_1615 = lean_array_push(x_1591, x_14);
x_1616 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1617 = lean_array_push(x_1615, x_1616);
x_1618 = lean_array_push(x_1617, x_1584);
x_1619 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1620, 0, x_1619);
lean_ctor_set(x_1620, 1, x_1618);
x_1621 = lean_array_push(x_1591, x_1620);
x_1622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1622, 0, x_1602);
lean_ctor_set(x_1622, 1, x_1621);
x_1623 = lean_array_push(x_1610, x_1622);
x_1624 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1625, 0, x_1624);
lean_ctor_set(x_1625, 1, x_1623);
x_1626 = 1;
x_1627 = lean_box(x_1626);
lean_ctor_set(x_1579, 1, x_1627);
lean_ctor_set(x_1579, 0, x_1625);
lean_ctor_set(x_1588, 0, x_1578);
return x_1588;
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; uint8_t x_1640; lean_object* x_1641; 
lean_dec(x_14);
x_1628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1628, 0, x_1602);
lean_ctor_set(x_1628, 1, x_1611);
x_1629 = lean_array_push(x_1591, x_1628);
x_1630 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1631 = lean_array_push(x_1629, x_1630);
x_1632 = lean_array_push(x_1631, x_1584);
x_1633 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1634, 0, x_1633);
lean_ctor_set(x_1634, 1, x_1632);
x_1635 = lean_array_push(x_1591, x_1634);
x_1636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1636, 0, x_1602);
lean_ctor_set(x_1636, 1, x_1635);
x_1637 = lean_array_push(x_1610, x_1636);
x_1638 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1639, 0, x_1638);
lean_ctor_set(x_1639, 1, x_1637);
x_1640 = 1;
x_1641 = lean_box(x_1640);
lean_ctor_set(x_1579, 1, x_1641);
lean_ctor_set(x_1579, 0, x_1639);
lean_ctor_set(x_1588, 0, x_1578);
return x_1588;
}
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; uint8_t x_1677; lean_object* x_1678; lean_object* x_1679; 
x_1642 = lean_ctor_get(x_1588, 1);
lean_inc(x_1642);
lean_dec(x_1588);
x_1643 = l_Array_empty___closed__1;
x_1644 = lean_array_push(x_1643, x_1571);
x_1645 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1646 = lean_array_push(x_1644, x_1645);
x_1647 = l_Lean_mkTermIdFromIdent___closed__2;
x_1648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1648, 0, x_1647);
lean_ctor_set(x_1648, 1, x_1646);
x_1649 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1650 = lean_array_push(x_1649, x_1648);
x_1651 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1652, 0, x_1651);
lean_ctor_set(x_1652, 1, x_1650);
x_1653 = lean_array_push(x_1643, x_1652);
x_1654 = l_Lean_nullKind___closed__2;
x_1655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1655, 0, x_1654);
lean_ctor_set(x_1655, 1, x_1653);
x_1656 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1657 = lean_array_push(x_1656, x_1655);
x_1658 = lean_array_push(x_1657, x_1645);
x_1659 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1660 = lean_array_push(x_1658, x_1659);
x_1661 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1662 = lean_array_push(x_1660, x_1661);
lean_inc(x_14);
x_1663 = lean_array_push(x_1643, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1664 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1664 = lean_box(0);
}
if (lean_is_scalar(x_1664)) {
 x_1665 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1665 = x_1664;
}
lean_ctor_set(x_1665, 0, x_1654);
lean_ctor_set(x_1665, 1, x_1663);
x_1666 = lean_array_push(x_1643, x_1665);
x_1667 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1668 = lean_array_push(x_1666, x_1667);
x_1669 = lean_array_push(x_1668, x_1584);
x_1670 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1671, 0, x_1670);
lean_ctor_set(x_1671, 1, x_1669);
x_1672 = lean_array_push(x_1643, x_1671);
x_1673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1673, 0, x_1654);
lean_ctor_set(x_1673, 1, x_1672);
x_1674 = lean_array_push(x_1662, x_1673);
x_1675 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1676, 0, x_1675);
lean_ctor_set(x_1676, 1, x_1674);
x_1677 = 1;
x_1678 = lean_box(x_1677);
lean_ctor_set(x_1579, 1, x_1678);
lean_ctor_set(x_1579, 0, x_1676);
x_1679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1679, 0, x_1578);
lean_ctor_set(x_1679, 1, x_1642);
return x_1679;
}
}
else
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; uint8_t x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; 
x_1680 = lean_ctor_get(x_1579, 0);
lean_inc(x_1680);
lean_dec(x_1579);
x_1681 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1580);
lean_dec(x_5);
x_1682 = lean_ctor_get(x_1681, 1);
lean_inc(x_1682);
lean_dec(x_1681);
x_1683 = l_Lean_Elab_Term_getMainModule___rarg(x_1682);
x_1684 = lean_ctor_get(x_1683, 1);
lean_inc(x_1684);
if (lean_is_exclusive(x_1683)) {
 lean_ctor_release(x_1683, 0);
 lean_ctor_release(x_1683, 1);
 x_1685 = x_1683;
} else {
 lean_dec_ref(x_1683);
 x_1685 = lean_box(0);
}
x_1686 = l_Array_empty___closed__1;
x_1687 = lean_array_push(x_1686, x_1571);
x_1688 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1689 = lean_array_push(x_1687, x_1688);
x_1690 = l_Lean_mkTermIdFromIdent___closed__2;
x_1691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1691, 0, x_1690);
lean_ctor_set(x_1691, 1, x_1689);
x_1692 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1693 = lean_array_push(x_1692, x_1691);
x_1694 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1695, 0, x_1694);
lean_ctor_set(x_1695, 1, x_1693);
x_1696 = lean_array_push(x_1686, x_1695);
x_1697 = l_Lean_nullKind___closed__2;
x_1698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1698, 0, x_1697);
lean_ctor_set(x_1698, 1, x_1696);
x_1699 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1700 = lean_array_push(x_1699, x_1698);
x_1701 = lean_array_push(x_1700, x_1688);
x_1702 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1703 = lean_array_push(x_1701, x_1702);
x_1704 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1705 = lean_array_push(x_1703, x_1704);
lean_inc(x_14);
x_1706 = lean_array_push(x_1686, x_14);
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
lean_ctor_set(x_1708, 0, x_1697);
lean_ctor_set(x_1708, 1, x_1706);
x_1709 = lean_array_push(x_1686, x_1708);
x_1710 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1711 = lean_array_push(x_1709, x_1710);
x_1712 = lean_array_push(x_1711, x_1680);
x_1713 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1714, 0, x_1713);
lean_ctor_set(x_1714, 1, x_1712);
x_1715 = lean_array_push(x_1686, x_1714);
x_1716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1716, 0, x_1697);
lean_ctor_set(x_1716, 1, x_1715);
x_1717 = lean_array_push(x_1705, x_1716);
x_1718 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1719, 0, x_1718);
lean_ctor_set(x_1719, 1, x_1717);
x_1720 = 1;
x_1721 = lean_box(x_1720);
x_1722 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1722, 0, x_1719);
lean_ctor_set(x_1722, 1, x_1721);
lean_ctor_set(x_1578, 1, x_1722);
if (lean_is_scalar(x_1685)) {
 x_1723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1723 = x_1685;
}
lean_ctor_set(x_1723, 0, x_1578);
lean_ctor_set(x_1723, 1, x_1684);
return x_1723;
}
}
else
{
lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; uint8_t x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; 
x_1724 = lean_ctor_get(x_1578, 0);
lean_inc(x_1724);
lean_dec(x_1578);
x_1725 = lean_ctor_get(x_1579, 0);
lean_inc(x_1725);
if (lean_is_exclusive(x_1579)) {
 lean_ctor_release(x_1579, 0);
 lean_ctor_release(x_1579, 1);
 x_1726 = x_1579;
} else {
 lean_dec_ref(x_1579);
 x_1726 = lean_box(0);
}
x_1727 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1580);
lean_dec(x_5);
x_1728 = lean_ctor_get(x_1727, 1);
lean_inc(x_1728);
lean_dec(x_1727);
x_1729 = l_Lean_Elab_Term_getMainModule___rarg(x_1728);
x_1730 = lean_ctor_get(x_1729, 1);
lean_inc(x_1730);
if (lean_is_exclusive(x_1729)) {
 lean_ctor_release(x_1729, 0);
 lean_ctor_release(x_1729, 1);
 x_1731 = x_1729;
} else {
 lean_dec_ref(x_1729);
 x_1731 = lean_box(0);
}
x_1732 = l_Array_empty___closed__1;
x_1733 = lean_array_push(x_1732, x_1571);
x_1734 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1735 = lean_array_push(x_1733, x_1734);
x_1736 = l_Lean_mkTermIdFromIdent___closed__2;
x_1737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1737, 0, x_1736);
lean_ctor_set(x_1737, 1, x_1735);
x_1738 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1739 = lean_array_push(x_1738, x_1737);
x_1740 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1741, 0, x_1740);
lean_ctor_set(x_1741, 1, x_1739);
x_1742 = lean_array_push(x_1732, x_1741);
x_1743 = l_Lean_nullKind___closed__2;
x_1744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1744, 0, x_1743);
lean_ctor_set(x_1744, 1, x_1742);
x_1745 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1746 = lean_array_push(x_1745, x_1744);
x_1747 = lean_array_push(x_1746, x_1734);
x_1748 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1749 = lean_array_push(x_1747, x_1748);
x_1750 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1751 = lean_array_push(x_1749, x_1750);
lean_inc(x_14);
x_1752 = lean_array_push(x_1732, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1753 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1753 = lean_box(0);
}
if (lean_is_scalar(x_1753)) {
 x_1754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1754 = x_1753;
}
lean_ctor_set(x_1754, 0, x_1743);
lean_ctor_set(x_1754, 1, x_1752);
x_1755 = lean_array_push(x_1732, x_1754);
x_1756 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1757 = lean_array_push(x_1755, x_1756);
x_1758 = lean_array_push(x_1757, x_1725);
x_1759 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1760, 0, x_1759);
lean_ctor_set(x_1760, 1, x_1758);
x_1761 = lean_array_push(x_1732, x_1760);
x_1762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1762, 0, x_1743);
lean_ctor_set(x_1762, 1, x_1761);
x_1763 = lean_array_push(x_1751, x_1762);
x_1764 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1765, 0, x_1764);
lean_ctor_set(x_1765, 1, x_1763);
x_1766 = 1;
x_1767 = lean_box(x_1766);
if (lean_is_scalar(x_1726)) {
 x_1768 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1768 = x_1726;
}
lean_ctor_set(x_1768, 0, x_1765);
lean_ctor_set(x_1768, 1, x_1767);
x_1769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1769, 0, x_1724);
lean_ctor_set(x_1769, 1, x_1768);
if (lean_is_scalar(x_1731)) {
 x_1770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1770 = x_1731;
}
lean_ctor_set(x_1770, 0, x_1769);
lean_ctor_set(x_1770, 1, x_1730);
return x_1770;
}
}
else
{
uint8_t x_1771; 
lean_dec(x_1571);
lean_dec(x_14);
lean_dec(x_5);
x_1771 = !lean_is_exclusive(x_1577);
if (x_1771 == 0)
{
return x_1577;
}
else
{
lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
x_1772 = lean_ctor_get(x_1577, 0);
x_1773 = lean_ctor_get(x_1577, 1);
lean_inc(x_1773);
lean_inc(x_1772);
lean_dec(x_1577);
x_1774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1774, 0, x_1772);
lean_ctor_set(x_1774, 1, x_1773);
return x_1774;
}
}
}
}
}
else
{
lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_1775 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_1776 = lean_ctor_get(x_1775, 0);
lean_inc(x_1776);
x_1777 = lean_ctor_get(x_1775, 1);
lean_inc(x_1777);
lean_dec(x_1775);
x_1778 = lean_unsigned_to_nat(1u);
x_1779 = lean_nat_add(x_3, x_1778);
lean_dec(x_3);
x_1780 = l_Lean_Elab_Term_mkExplicitBinder(x_1776, x_14);
x_1781 = lean_array_push(x_4, x_1780);
x_3 = x_1779;
x_4 = x_1781;
x_6 = x_1777;
goto _start;
}
}
else
{
lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_1783 = lean_unsigned_to_nat(1u);
x_1784 = lean_nat_add(x_3, x_1783);
lean_dec(x_3);
x_1785 = lean_array_push(x_4, x_14);
x_3 = x_1784;
x_4 = x_1785;
goto _start;
}
}
else
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_1787 = lean_unsigned_to_nat(1u);
x_1788 = lean_nat_add(x_3, x_1787);
lean_dec(x_3);
x_1789 = lean_array_push(x_4, x_14);
x_3 = x_1788;
x_4 = x_1789;
goto _start;
}
}
else
{
lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_1791 = lean_unsigned_to_nat(1u);
x_1792 = lean_nat_add(x_3, x_1791);
lean_dec(x_3);
x_1793 = lean_array_push(x_4, x_14);
x_3 = x_1792;
x_4 = x_1793;
goto _start;
}
}
}
}
}
else
{
lean_object* x_1795; size_t x_1796; lean_object* x_1797; uint8_t x_1798; 
x_1795 = lean_ctor_get(x_18, 1);
x_1796 = lean_ctor_get_usize(x_18, 2);
lean_inc(x_1795);
lean_dec(x_18);
x_1797 = l_Lean_mkAppStx___closed__1;
x_1798 = lean_string_dec_eq(x_1795, x_1797);
lean_dec(x_1795);
if (x_1798 == 0)
{
uint8_t x_1799; lean_object* x_1800; 
lean_free_object(x_17);
lean_dec(x_28);
lean_free_object(x_16);
lean_dec(x_25);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_1799 = 1;
lean_inc(x_14);
x_1800 = l_Lean_Syntax_isTermId_x3f(x_14, x_1799);
if (lean_obj_tag(x_1800) == 0)
{
lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; 
x_1801 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_1802 = lean_ctor_get(x_1801, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1801, 1);
lean_inc(x_1803);
lean_dec(x_1801);
x_1804 = lean_unsigned_to_nat(1u);
x_1805 = lean_nat_add(x_3, x_1804);
lean_dec(x_3);
x_1806 = l_Lean_mkHole(x_14);
lean_inc(x_1802);
x_1807 = l_Lean_Elab_Term_mkExplicitBinder(x_1802, x_1806);
x_1808 = lean_array_push(x_4, x_1807);
lean_inc(x_5);
x_1809 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_1805, x_1808, x_5, x_1803);
if (lean_obj_tag(x_1809) == 0)
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; 
x_1810 = lean_ctor_get(x_1809, 0);
lean_inc(x_1810);
x_1811 = lean_ctor_get(x_1810, 1);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1809, 1);
lean_inc(x_1812);
lean_dec(x_1809);
x_1813 = lean_ctor_get(x_1810, 0);
lean_inc(x_1813);
if (lean_is_exclusive(x_1810)) {
 lean_ctor_release(x_1810, 0);
 lean_ctor_release(x_1810, 1);
 x_1814 = x_1810;
} else {
 lean_dec_ref(x_1810);
 x_1814 = lean_box(0);
}
x_1815 = lean_ctor_get(x_1811, 0);
lean_inc(x_1815);
if (lean_is_exclusive(x_1811)) {
 lean_ctor_release(x_1811, 0);
 lean_ctor_release(x_1811, 1);
 x_1816 = x_1811;
} else {
 lean_dec_ref(x_1811);
 x_1816 = lean_box(0);
}
x_1817 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1812);
lean_dec(x_5);
x_1818 = lean_ctor_get(x_1817, 1);
lean_inc(x_1818);
lean_dec(x_1817);
x_1819 = l_Lean_Elab_Term_getMainModule___rarg(x_1818);
x_1820 = lean_ctor_get(x_1819, 1);
lean_inc(x_1820);
if (lean_is_exclusive(x_1819)) {
 lean_ctor_release(x_1819, 0);
 lean_ctor_release(x_1819, 1);
 x_1821 = x_1819;
} else {
 lean_dec_ref(x_1819);
 x_1821 = lean_box(0);
}
x_1822 = l_Array_empty___closed__1;
x_1823 = lean_array_push(x_1822, x_1802);
x_1824 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1825 = lean_array_push(x_1823, x_1824);
x_1826 = l_Lean_mkTermIdFromIdent___closed__2;
x_1827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1827, 0, x_1826);
lean_ctor_set(x_1827, 1, x_1825);
x_1828 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1829 = lean_array_push(x_1828, x_1827);
x_1830 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1831 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1831, 0, x_1830);
lean_ctor_set(x_1831, 1, x_1829);
x_1832 = lean_array_push(x_1822, x_1831);
x_1833 = l_Lean_nullKind___closed__2;
x_1834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1834, 0, x_1833);
lean_ctor_set(x_1834, 1, x_1832);
x_1835 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1836 = lean_array_push(x_1835, x_1834);
x_1837 = lean_array_push(x_1836, x_1824);
x_1838 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1839 = lean_array_push(x_1837, x_1838);
x_1840 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1841 = lean_array_push(x_1839, x_1840);
lean_inc(x_14);
x_1842 = lean_array_push(x_1822, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1843 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1843 = lean_box(0);
}
if (lean_is_scalar(x_1843)) {
 x_1844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1844 = x_1843;
}
lean_ctor_set(x_1844, 0, x_1833);
lean_ctor_set(x_1844, 1, x_1842);
x_1845 = lean_array_push(x_1822, x_1844);
x_1846 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1847 = lean_array_push(x_1845, x_1846);
x_1848 = lean_array_push(x_1847, x_1815);
x_1849 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1850, 0, x_1849);
lean_ctor_set(x_1850, 1, x_1848);
x_1851 = lean_array_push(x_1822, x_1850);
x_1852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1852, 0, x_1833);
lean_ctor_set(x_1852, 1, x_1851);
x_1853 = lean_array_push(x_1841, x_1852);
x_1854 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1855, 0, x_1854);
lean_ctor_set(x_1855, 1, x_1853);
x_1856 = lean_box(x_1799);
if (lean_is_scalar(x_1816)) {
 x_1857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1857 = x_1816;
}
lean_ctor_set(x_1857, 0, x_1855);
lean_ctor_set(x_1857, 1, x_1856);
if (lean_is_scalar(x_1814)) {
 x_1858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1858 = x_1814;
}
lean_ctor_set(x_1858, 0, x_1813);
lean_ctor_set(x_1858, 1, x_1857);
if (lean_is_scalar(x_1821)) {
 x_1859 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1859 = x_1821;
}
lean_ctor_set(x_1859, 0, x_1858);
lean_ctor_set(x_1859, 1, x_1820);
return x_1859;
}
else
{
lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; 
lean_dec(x_1802);
lean_dec(x_14);
lean_dec(x_5);
x_1860 = lean_ctor_get(x_1809, 0);
lean_inc(x_1860);
x_1861 = lean_ctor_get(x_1809, 1);
lean_inc(x_1861);
if (lean_is_exclusive(x_1809)) {
 lean_ctor_release(x_1809, 0);
 lean_ctor_release(x_1809, 1);
 x_1862 = x_1809;
} else {
 lean_dec_ref(x_1809);
 x_1862 = lean_box(0);
}
if (lean_is_scalar(x_1862)) {
 x_1863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1863 = x_1862;
}
lean_ctor_set(x_1863, 0, x_1860);
lean_ctor_set(x_1863, 1, x_1861);
return x_1863;
}
}
else
{
lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; uint8_t x_1867; 
x_1864 = lean_ctor_get(x_1800, 0);
lean_inc(x_1864);
lean_dec(x_1800);
x_1865 = lean_ctor_get(x_1864, 0);
lean_inc(x_1865);
x_1866 = lean_ctor_get(x_1864, 1);
lean_inc(x_1866);
lean_dec(x_1864);
x_1867 = l_Lean_Syntax_isNone(x_1866);
lean_dec(x_1866);
if (x_1867 == 0)
{
lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; 
lean_dec(x_1865);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1868 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_1869 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_1868, x_5, x_6);
lean_dec(x_14);
x_1870 = lean_ctor_get(x_1869, 0);
lean_inc(x_1870);
x_1871 = lean_ctor_get(x_1869, 1);
lean_inc(x_1871);
if (lean_is_exclusive(x_1869)) {
 lean_ctor_release(x_1869, 0);
 lean_ctor_release(x_1869, 1);
 x_1872 = x_1869;
} else {
 lean_dec_ref(x_1869);
 x_1872 = lean_box(0);
}
if (lean_is_scalar(x_1872)) {
 x_1873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1873 = x_1872;
}
lean_ctor_set(x_1873, 0, x_1870);
lean_ctor_set(x_1873, 1, x_1871);
return x_1873;
}
else
{
lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; 
x_1874 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_1875 = lean_unsigned_to_nat(1u);
x_1876 = lean_nat_add(x_3, x_1875);
lean_dec(x_3);
x_1877 = l_Lean_Elab_Term_mkExplicitBinder(x_1865, x_1874);
x_1878 = lean_array_push(x_4, x_1877);
x_3 = x_1876;
x_4 = x_1878;
goto _start;
}
}
}
else
{
lean_object* x_1880; uint8_t x_1881; 
x_1880 = l_Lean_mkAppStx___closed__3;
x_1881 = lean_string_dec_eq(x_28, x_1880);
if (x_1881 == 0)
{
lean_object* x_1882; lean_object* x_1883; uint8_t x_1884; lean_object* x_1885; 
x_1882 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1882, 0, x_19);
lean_ctor_set(x_1882, 1, x_1797);
lean_ctor_set_usize(x_1882, 2, x_1796);
lean_ctor_set(x_17, 0, x_1882);
x_1883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1883, 0, x_15);
lean_ctor_set(x_1883, 1, x_20);
x_1884 = 1;
lean_inc(x_1883);
x_1885 = l_Lean_Syntax_isTermId_x3f(x_1883, x_1884);
if (lean_obj_tag(x_1885) == 0)
{
lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
lean_dec(x_1883);
x_1886 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_1887 = lean_ctor_get(x_1886, 0);
lean_inc(x_1887);
x_1888 = lean_ctor_get(x_1886, 1);
lean_inc(x_1888);
lean_dec(x_1886);
x_1889 = lean_unsigned_to_nat(1u);
x_1890 = lean_nat_add(x_3, x_1889);
lean_dec(x_3);
x_1891 = l_Lean_mkHole(x_14);
lean_inc(x_1887);
x_1892 = l_Lean_Elab_Term_mkExplicitBinder(x_1887, x_1891);
x_1893 = lean_array_push(x_4, x_1892);
lean_inc(x_5);
x_1894 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_1890, x_1893, x_5, x_1888);
if (lean_obj_tag(x_1894) == 0)
{
lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; 
x_1895 = lean_ctor_get(x_1894, 0);
lean_inc(x_1895);
x_1896 = lean_ctor_get(x_1895, 1);
lean_inc(x_1896);
x_1897 = lean_ctor_get(x_1894, 1);
lean_inc(x_1897);
lean_dec(x_1894);
x_1898 = lean_ctor_get(x_1895, 0);
lean_inc(x_1898);
if (lean_is_exclusive(x_1895)) {
 lean_ctor_release(x_1895, 0);
 lean_ctor_release(x_1895, 1);
 x_1899 = x_1895;
} else {
 lean_dec_ref(x_1895);
 x_1899 = lean_box(0);
}
x_1900 = lean_ctor_get(x_1896, 0);
lean_inc(x_1900);
if (lean_is_exclusive(x_1896)) {
 lean_ctor_release(x_1896, 0);
 lean_ctor_release(x_1896, 1);
 x_1901 = x_1896;
} else {
 lean_dec_ref(x_1896);
 x_1901 = lean_box(0);
}
x_1902 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1897);
lean_dec(x_5);
x_1903 = lean_ctor_get(x_1902, 1);
lean_inc(x_1903);
lean_dec(x_1902);
x_1904 = l_Lean_Elab_Term_getMainModule___rarg(x_1903);
x_1905 = lean_ctor_get(x_1904, 1);
lean_inc(x_1905);
if (lean_is_exclusive(x_1904)) {
 lean_ctor_release(x_1904, 0);
 lean_ctor_release(x_1904, 1);
 x_1906 = x_1904;
} else {
 lean_dec_ref(x_1904);
 x_1906 = lean_box(0);
}
x_1907 = l_Array_empty___closed__1;
x_1908 = lean_array_push(x_1907, x_1887);
x_1909 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1910 = lean_array_push(x_1908, x_1909);
x_1911 = l_Lean_mkTermIdFromIdent___closed__2;
x_1912 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1912, 0, x_1911);
lean_ctor_set(x_1912, 1, x_1910);
x_1913 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1914 = lean_array_push(x_1913, x_1912);
x_1915 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_1916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1916, 0, x_1915);
lean_ctor_set(x_1916, 1, x_1914);
x_1917 = lean_array_push(x_1907, x_1916);
x_1918 = l_Lean_nullKind___closed__2;
x_1919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1919, 0, x_1918);
lean_ctor_set(x_1919, 1, x_1917);
x_1920 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_1921 = lean_array_push(x_1920, x_1919);
x_1922 = lean_array_push(x_1921, x_1909);
x_1923 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_1924 = lean_array_push(x_1922, x_1923);
x_1925 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_1926 = lean_array_push(x_1924, x_1925);
lean_inc(x_14);
x_1927 = lean_array_push(x_1907, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1928 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1928 = lean_box(0);
}
if (lean_is_scalar(x_1928)) {
 x_1929 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1929 = x_1928;
}
lean_ctor_set(x_1929, 0, x_1918);
lean_ctor_set(x_1929, 1, x_1927);
x_1930 = lean_array_push(x_1907, x_1929);
x_1931 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_1932 = lean_array_push(x_1930, x_1931);
x_1933 = lean_array_push(x_1932, x_1900);
x_1934 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1935, 0, x_1934);
lean_ctor_set(x_1935, 1, x_1933);
x_1936 = lean_array_push(x_1907, x_1935);
x_1937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1937, 0, x_1918);
lean_ctor_set(x_1937, 1, x_1936);
x_1938 = lean_array_push(x_1926, x_1937);
x_1939 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1940, 0, x_1939);
lean_ctor_set(x_1940, 1, x_1938);
x_1941 = lean_box(x_1884);
if (lean_is_scalar(x_1901)) {
 x_1942 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1942 = x_1901;
}
lean_ctor_set(x_1942, 0, x_1940);
lean_ctor_set(x_1942, 1, x_1941);
if (lean_is_scalar(x_1899)) {
 x_1943 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1943 = x_1899;
}
lean_ctor_set(x_1943, 0, x_1898);
lean_ctor_set(x_1943, 1, x_1942);
if (lean_is_scalar(x_1906)) {
 x_1944 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1944 = x_1906;
}
lean_ctor_set(x_1944, 0, x_1943);
lean_ctor_set(x_1944, 1, x_1905);
return x_1944;
}
else
{
lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
lean_dec(x_1887);
lean_dec(x_14);
lean_dec(x_5);
x_1945 = lean_ctor_get(x_1894, 0);
lean_inc(x_1945);
x_1946 = lean_ctor_get(x_1894, 1);
lean_inc(x_1946);
if (lean_is_exclusive(x_1894)) {
 lean_ctor_release(x_1894, 0);
 lean_ctor_release(x_1894, 1);
 x_1947 = x_1894;
} else {
 lean_dec_ref(x_1894);
 x_1947 = lean_box(0);
}
if (lean_is_scalar(x_1947)) {
 x_1948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1948 = x_1947;
}
lean_ctor_set(x_1948, 0, x_1945);
lean_ctor_set(x_1948, 1, x_1946);
return x_1948;
}
}
else
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; uint8_t x_1952; 
lean_dec(x_14);
x_1949 = lean_ctor_get(x_1885, 0);
lean_inc(x_1949);
lean_dec(x_1885);
x_1950 = lean_ctor_get(x_1949, 0);
lean_inc(x_1950);
x_1951 = lean_ctor_get(x_1949, 1);
lean_inc(x_1951);
lean_dec(x_1949);
x_1952 = l_Lean_Syntax_isNone(x_1951);
lean_dec(x_1951);
if (x_1952 == 0)
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; 
lean_dec(x_1950);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1953 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_1954 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1883, x_1953, x_5, x_6);
lean_dec(x_1883);
x_1955 = lean_ctor_get(x_1954, 0);
lean_inc(x_1955);
x_1956 = lean_ctor_get(x_1954, 1);
lean_inc(x_1956);
if (lean_is_exclusive(x_1954)) {
 lean_ctor_release(x_1954, 0);
 lean_ctor_release(x_1954, 1);
 x_1957 = x_1954;
} else {
 lean_dec_ref(x_1954);
 x_1957 = lean_box(0);
}
if (lean_is_scalar(x_1957)) {
 x_1958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1958 = x_1957;
}
lean_ctor_set(x_1958, 0, x_1955);
lean_ctor_set(x_1958, 1, x_1956);
return x_1958;
}
else
{
lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; 
x_1959 = l_Lean_mkHole(x_1883);
lean_dec(x_1883);
x_1960 = lean_unsigned_to_nat(1u);
x_1961 = lean_nat_add(x_3, x_1960);
lean_dec(x_3);
x_1962 = l_Lean_Elab_Term_mkExplicitBinder(x_1950, x_1959);
x_1963 = lean_array_push(x_4, x_1962);
x_3 = x_1961;
x_4 = x_1963;
goto _start;
}
}
}
else
{
lean_object* x_1965; uint8_t x_1966; 
lean_dec(x_28);
x_1965 = l_Lean_mkAppStx___closed__5;
x_1966 = lean_string_dec_eq(x_25, x_1965);
if (x_1966 == 0)
{
lean_object* x_1967; lean_object* x_1968; uint8_t x_1969; lean_object* x_1970; 
x_1967 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_1967, 0, x_19);
lean_ctor_set(x_1967, 1, x_1797);
lean_ctor_set_usize(x_1967, 2, x_1796);
lean_ctor_set(x_17, 1, x_1880);
lean_ctor_set(x_17, 0, x_1967);
x_1968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1968, 0, x_15);
lean_ctor_set(x_1968, 1, x_20);
x_1969 = 1;
lean_inc(x_1968);
x_1970 = l_Lean_Syntax_isTermId_x3f(x_1968, x_1969);
if (lean_obj_tag(x_1970) == 0)
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; 
lean_dec(x_1968);
x_1971 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_1972 = lean_ctor_get(x_1971, 0);
lean_inc(x_1972);
x_1973 = lean_ctor_get(x_1971, 1);
lean_inc(x_1973);
lean_dec(x_1971);
x_1974 = lean_unsigned_to_nat(1u);
x_1975 = lean_nat_add(x_3, x_1974);
lean_dec(x_3);
x_1976 = l_Lean_mkHole(x_14);
lean_inc(x_1972);
x_1977 = l_Lean_Elab_Term_mkExplicitBinder(x_1972, x_1976);
x_1978 = lean_array_push(x_4, x_1977);
lean_inc(x_5);
x_1979 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_1975, x_1978, x_5, x_1973);
if (lean_obj_tag(x_1979) == 0)
{
lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; 
x_1980 = lean_ctor_get(x_1979, 0);
lean_inc(x_1980);
x_1981 = lean_ctor_get(x_1980, 1);
lean_inc(x_1981);
x_1982 = lean_ctor_get(x_1979, 1);
lean_inc(x_1982);
lean_dec(x_1979);
x_1983 = lean_ctor_get(x_1980, 0);
lean_inc(x_1983);
if (lean_is_exclusive(x_1980)) {
 lean_ctor_release(x_1980, 0);
 lean_ctor_release(x_1980, 1);
 x_1984 = x_1980;
} else {
 lean_dec_ref(x_1980);
 x_1984 = lean_box(0);
}
x_1985 = lean_ctor_get(x_1981, 0);
lean_inc(x_1985);
if (lean_is_exclusive(x_1981)) {
 lean_ctor_release(x_1981, 0);
 lean_ctor_release(x_1981, 1);
 x_1986 = x_1981;
} else {
 lean_dec_ref(x_1981);
 x_1986 = lean_box(0);
}
x_1987 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_1982);
lean_dec(x_5);
x_1988 = lean_ctor_get(x_1987, 1);
lean_inc(x_1988);
lean_dec(x_1987);
x_1989 = l_Lean_Elab_Term_getMainModule___rarg(x_1988);
x_1990 = lean_ctor_get(x_1989, 1);
lean_inc(x_1990);
if (lean_is_exclusive(x_1989)) {
 lean_ctor_release(x_1989, 0);
 lean_ctor_release(x_1989, 1);
 x_1991 = x_1989;
} else {
 lean_dec_ref(x_1989);
 x_1991 = lean_box(0);
}
x_1992 = l_Array_empty___closed__1;
x_1993 = lean_array_push(x_1992, x_1972);
x_1994 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_1995 = lean_array_push(x_1993, x_1994);
x_1996 = l_Lean_mkTermIdFromIdent___closed__2;
x_1997 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1997, 0, x_1996);
lean_ctor_set(x_1997, 1, x_1995);
x_1998 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_1999 = lean_array_push(x_1998, x_1997);
x_2000 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2001 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2001, 0, x_2000);
lean_ctor_set(x_2001, 1, x_1999);
x_2002 = lean_array_push(x_1992, x_2001);
x_2003 = l_Lean_nullKind___closed__2;
x_2004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2004, 0, x_2003);
lean_ctor_set(x_2004, 1, x_2002);
x_2005 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2006 = lean_array_push(x_2005, x_2004);
x_2007 = lean_array_push(x_2006, x_1994);
x_2008 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2009 = lean_array_push(x_2007, x_2008);
x_2010 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2011 = lean_array_push(x_2009, x_2010);
lean_inc(x_14);
x_2012 = lean_array_push(x_1992, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2013 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2013 = lean_box(0);
}
if (lean_is_scalar(x_2013)) {
 x_2014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2014 = x_2013;
}
lean_ctor_set(x_2014, 0, x_2003);
lean_ctor_set(x_2014, 1, x_2012);
x_2015 = lean_array_push(x_1992, x_2014);
x_2016 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2017 = lean_array_push(x_2015, x_2016);
x_2018 = lean_array_push(x_2017, x_1985);
x_2019 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2020, 0, x_2019);
lean_ctor_set(x_2020, 1, x_2018);
x_2021 = lean_array_push(x_1992, x_2020);
x_2022 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2022, 0, x_2003);
lean_ctor_set(x_2022, 1, x_2021);
x_2023 = lean_array_push(x_2011, x_2022);
x_2024 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2025, 0, x_2024);
lean_ctor_set(x_2025, 1, x_2023);
x_2026 = lean_box(x_1969);
if (lean_is_scalar(x_1986)) {
 x_2027 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2027 = x_1986;
}
lean_ctor_set(x_2027, 0, x_2025);
lean_ctor_set(x_2027, 1, x_2026);
if (lean_is_scalar(x_1984)) {
 x_2028 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2028 = x_1984;
}
lean_ctor_set(x_2028, 0, x_1983);
lean_ctor_set(x_2028, 1, x_2027);
if (lean_is_scalar(x_1991)) {
 x_2029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2029 = x_1991;
}
lean_ctor_set(x_2029, 0, x_2028);
lean_ctor_set(x_2029, 1, x_1990);
return x_2029;
}
else
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; 
lean_dec(x_1972);
lean_dec(x_14);
lean_dec(x_5);
x_2030 = lean_ctor_get(x_1979, 0);
lean_inc(x_2030);
x_2031 = lean_ctor_get(x_1979, 1);
lean_inc(x_2031);
if (lean_is_exclusive(x_1979)) {
 lean_ctor_release(x_1979, 0);
 lean_ctor_release(x_1979, 1);
 x_2032 = x_1979;
} else {
 lean_dec_ref(x_1979);
 x_2032 = lean_box(0);
}
if (lean_is_scalar(x_2032)) {
 x_2033 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2033 = x_2032;
}
lean_ctor_set(x_2033, 0, x_2030);
lean_ctor_set(x_2033, 1, x_2031);
return x_2033;
}
}
else
{
lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; uint8_t x_2037; 
lean_dec(x_14);
x_2034 = lean_ctor_get(x_1970, 0);
lean_inc(x_2034);
lean_dec(x_1970);
x_2035 = lean_ctor_get(x_2034, 0);
lean_inc(x_2035);
x_2036 = lean_ctor_get(x_2034, 1);
lean_inc(x_2036);
lean_dec(x_2034);
x_2037 = l_Lean_Syntax_isNone(x_2036);
lean_dec(x_2036);
if (x_2037 == 0)
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; 
lean_dec(x_2035);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2038 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_2039 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1968, x_2038, x_5, x_6);
lean_dec(x_1968);
x_2040 = lean_ctor_get(x_2039, 0);
lean_inc(x_2040);
x_2041 = lean_ctor_get(x_2039, 1);
lean_inc(x_2041);
if (lean_is_exclusive(x_2039)) {
 lean_ctor_release(x_2039, 0);
 lean_ctor_release(x_2039, 1);
 x_2042 = x_2039;
} else {
 lean_dec_ref(x_2039);
 x_2042 = lean_box(0);
}
if (lean_is_scalar(x_2042)) {
 x_2043 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2043 = x_2042;
}
lean_ctor_set(x_2043, 0, x_2040);
lean_ctor_set(x_2043, 1, x_2041);
return x_2043;
}
else
{
lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; 
x_2044 = l_Lean_mkHole(x_1968);
lean_dec(x_1968);
x_2045 = lean_unsigned_to_nat(1u);
x_2046 = lean_nat_add(x_3, x_2045);
lean_dec(x_3);
x_2047 = l_Lean_Elab_Term_mkExplicitBinder(x_2035, x_2044);
x_2048 = lean_array_push(x_4, x_2047);
x_3 = x_2046;
x_4 = x_2048;
goto _start;
}
}
}
else
{
lean_object* x_2050; uint8_t x_2051; 
lean_dec(x_25);
x_2050 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_2051 = lean_string_dec_eq(x_22, x_2050);
if (x_2051 == 0)
{
lean_object* x_2052; uint8_t x_2053; 
x_2052 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_2053 = lean_string_dec_eq(x_22, x_2052);
if (x_2053 == 0)
{
lean_object* x_2054; uint8_t x_2055; 
x_2054 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_2055 = lean_string_dec_eq(x_22, x_2054);
if (x_2055 == 0)
{
lean_object* x_2056; uint8_t x_2057; 
x_2056 = l_Lean_mkHole___closed__1;
x_2057 = lean_string_dec_eq(x_22, x_2056);
if (x_2057 == 0)
{
lean_object* x_2058; uint8_t x_2059; 
x_2058 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_2059 = lean_string_dec_eq(x_22, x_2058);
if (x_2059 == 0)
{
lean_object* x_2060; lean_object* x_2061; uint8_t x_2062; lean_object* x_2063; 
x_2060 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2060, 0, x_19);
lean_ctor_set(x_2060, 1, x_1797);
lean_ctor_set_usize(x_2060, 2, x_1796);
lean_ctor_set(x_17, 1, x_1880);
lean_ctor_set(x_17, 0, x_2060);
lean_ctor_set(x_16, 1, x_1965);
x_2061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2061, 0, x_15);
lean_ctor_set(x_2061, 1, x_20);
x_2062 = 1;
lean_inc(x_2061);
x_2063 = l_Lean_Syntax_isTermId_x3f(x_2061, x_2062);
if (lean_obj_tag(x_2063) == 0)
{
lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; 
lean_dec(x_2061);
x_2064 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2065 = lean_ctor_get(x_2064, 0);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_2064, 1);
lean_inc(x_2066);
lean_dec(x_2064);
x_2067 = lean_unsigned_to_nat(1u);
x_2068 = lean_nat_add(x_3, x_2067);
lean_dec(x_3);
x_2069 = l_Lean_mkHole(x_14);
lean_inc(x_2065);
x_2070 = l_Lean_Elab_Term_mkExplicitBinder(x_2065, x_2069);
x_2071 = lean_array_push(x_4, x_2070);
lean_inc(x_5);
x_2072 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2068, x_2071, x_5, x_2066);
if (lean_obj_tag(x_2072) == 0)
{
lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; 
x_2073 = lean_ctor_get(x_2072, 0);
lean_inc(x_2073);
x_2074 = lean_ctor_get(x_2073, 1);
lean_inc(x_2074);
x_2075 = lean_ctor_get(x_2072, 1);
lean_inc(x_2075);
lean_dec(x_2072);
x_2076 = lean_ctor_get(x_2073, 0);
lean_inc(x_2076);
if (lean_is_exclusive(x_2073)) {
 lean_ctor_release(x_2073, 0);
 lean_ctor_release(x_2073, 1);
 x_2077 = x_2073;
} else {
 lean_dec_ref(x_2073);
 x_2077 = lean_box(0);
}
x_2078 = lean_ctor_get(x_2074, 0);
lean_inc(x_2078);
if (lean_is_exclusive(x_2074)) {
 lean_ctor_release(x_2074, 0);
 lean_ctor_release(x_2074, 1);
 x_2079 = x_2074;
} else {
 lean_dec_ref(x_2074);
 x_2079 = lean_box(0);
}
x_2080 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2075);
lean_dec(x_5);
x_2081 = lean_ctor_get(x_2080, 1);
lean_inc(x_2081);
lean_dec(x_2080);
x_2082 = l_Lean_Elab_Term_getMainModule___rarg(x_2081);
x_2083 = lean_ctor_get(x_2082, 1);
lean_inc(x_2083);
if (lean_is_exclusive(x_2082)) {
 lean_ctor_release(x_2082, 0);
 lean_ctor_release(x_2082, 1);
 x_2084 = x_2082;
} else {
 lean_dec_ref(x_2082);
 x_2084 = lean_box(0);
}
x_2085 = l_Array_empty___closed__1;
x_2086 = lean_array_push(x_2085, x_2065);
x_2087 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2088 = lean_array_push(x_2086, x_2087);
x_2089 = l_Lean_mkTermIdFromIdent___closed__2;
x_2090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2090, 0, x_2089);
lean_ctor_set(x_2090, 1, x_2088);
x_2091 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2092 = lean_array_push(x_2091, x_2090);
x_2093 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2094 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2094, 0, x_2093);
lean_ctor_set(x_2094, 1, x_2092);
x_2095 = lean_array_push(x_2085, x_2094);
x_2096 = l_Lean_nullKind___closed__2;
x_2097 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2097, 0, x_2096);
lean_ctor_set(x_2097, 1, x_2095);
x_2098 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2099 = lean_array_push(x_2098, x_2097);
x_2100 = lean_array_push(x_2099, x_2087);
x_2101 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2102 = lean_array_push(x_2100, x_2101);
x_2103 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2104 = lean_array_push(x_2102, x_2103);
lean_inc(x_14);
x_2105 = lean_array_push(x_2085, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2106 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2106 = lean_box(0);
}
if (lean_is_scalar(x_2106)) {
 x_2107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2107 = x_2106;
}
lean_ctor_set(x_2107, 0, x_2096);
lean_ctor_set(x_2107, 1, x_2105);
x_2108 = lean_array_push(x_2085, x_2107);
x_2109 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2110 = lean_array_push(x_2108, x_2109);
x_2111 = lean_array_push(x_2110, x_2078);
x_2112 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2113, 0, x_2112);
lean_ctor_set(x_2113, 1, x_2111);
x_2114 = lean_array_push(x_2085, x_2113);
x_2115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2115, 0, x_2096);
lean_ctor_set(x_2115, 1, x_2114);
x_2116 = lean_array_push(x_2104, x_2115);
x_2117 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2118, 0, x_2117);
lean_ctor_set(x_2118, 1, x_2116);
x_2119 = lean_box(x_2062);
if (lean_is_scalar(x_2079)) {
 x_2120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2120 = x_2079;
}
lean_ctor_set(x_2120, 0, x_2118);
lean_ctor_set(x_2120, 1, x_2119);
if (lean_is_scalar(x_2077)) {
 x_2121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2121 = x_2077;
}
lean_ctor_set(x_2121, 0, x_2076);
lean_ctor_set(x_2121, 1, x_2120);
if (lean_is_scalar(x_2084)) {
 x_2122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2122 = x_2084;
}
lean_ctor_set(x_2122, 0, x_2121);
lean_ctor_set(x_2122, 1, x_2083);
return x_2122;
}
else
{
lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; 
lean_dec(x_2065);
lean_dec(x_14);
lean_dec(x_5);
x_2123 = lean_ctor_get(x_2072, 0);
lean_inc(x_2123);
x_2124 = lean_ctor_get(x_2072, 1);
lean_inc(x_2124);
if (lean_is_exclusive(x_2072)) {
 lean_ctor_release(x_2072, 0);
 lean_ctor_release(x_2072, 1);
 x_2125 = x_2072;
} else {
 lean_dec_ref(x_2072);
 x_2125 = lean_box(0);
}
if (lean_is_scalar(x_2125)) {
 x_2126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2126 = x_2125;
}
lean_ctor_set(x_2126, 0, x_2123);
lean_ctor_set(x_2126, 1, x_2124);
return x_2126;
}
}
else
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; uint8_t x_2130; 
lean_dec(x_14);
x_2127 = lean_ctor_get(x_2063, 0);
lean_inc(x_2127);
lean_dec(x_2063);
x_2128 = lean_ctor_get(x_2127, 0);
lean_inc(x_2128);
x_2129 = lean_ctor_get(x_2127, 1);
lean_inc(x_2129);
lean_dec(x_2127);
x_2130 = l_Lean_Syntax_isNone(x_2129);
lean_dec(x_2129);
if (x_2130 == 0)
{
lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; 
lean_dec(x_2128);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2131 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_2132 = l_Lean_Elab_Term_throwErrorAt___rarg(x_2061, x_2131, x_5, x_6);
lean_dec(x_2061);
x_2133 = lean_ctor_get(x_2132, 0);
lean_inc(x_2133);
x_2134 = lean_ctor_get(x_2132, 1);
lean_inc(x_2134);
if (lean_is_exclusive(x_2132)) {
 lean_ctor_release(x_2132, 0);
 lean_ctor_release(x_2132, 1);
 x_2135 = x_2132;
} else {
 lean_dec_ref(x_2132);
 x_2135 = lean_box(0);
}
if (lean_is_scalar(x_2135)) {
 x_2136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2136 = x_2135;
}
lean_ctor_set(x_2136, 0, x_2133);
lean_ctor_set(x_2136, 1, x_2134);
return x_2136;
}
else
{
lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; 
x_2137 = l_Lean_mkHole(x_2061);
lean_dec(x_2061);
x_2138 = lean_unsigned_to_nat(1u);
x_2139 = lean_nat_add(x_3, x_2138);
lean_dec(x_3);
x_2140 = l_Lean_Elab_Term_mkExplicitBinder(x_2128, x_2137);
x_2141 = lean_array_push(x_4, x_2140);
x_3 = x_2139;
x_4 = x_2141;
goto _start;
}
}
}
else
{
lean_object* x_2143; lean_object* x_2144; uint8_t x_2145; 
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2143 = lean_unsigned_to_nat(1u);
x_2144 = l_Lean_Syntax_getArg(x_14, x_2143);
x_2145 = l_Lean_Syntax_isNone(x_2144);
if (x_2145 == 0)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; uint8_t x_2149; 
x_2146 = lean_unsigned_to_nat(0u);
x_2147 = l_Lean_Syntax_getArg(x_2144, x_2146);
x_2148 = l_Lean_Syntax_getArg(x_2144, x_2143);
lean_dec(x_2144);
x_2149 = l_Lean_Syntax_isNone(x_2148);
if (x_2149 == 0)
{
lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; uint8_t x_2157; 
x_2150 = l_Lean_Syntax_getArg(x_2148, x_2146);
lean_dec(x_2148);
lean_inc(x_2150);
x_2151 = l_Lean_Syntax_getKind(x_2150);
x_2152 = lean_name_mk_string(x_19, x_1797);
x_2153 = lean_name_mk_string(x_2152, x_1880);
x_2154 = lean_name_mk_string(x_2153, x_1965);
x_2155 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_2156 = lean_name_mk_string(x_2154, x_2155);
x_2157 = lean_name_eq(x_2151, x_2156);
lean_dec(x_2156);
lean_dec(x_2151);
if (x_2157 == 0)
{
lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; 
lean_dec(x_2150);
lean_dec(x_2147);
x_2158 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2159 = lean_ctor_get(x_2158, 0);
lean_inc(x_2159);
x_2160 = lean_ctor_get(x_2158, 1);
lean_inc(x_2160);
lean_dec(x_2158);
x_2161 = lean_nat_add(x_3, x_2143);
lean_dec(x_3);
x_2162 = l_Lean_mkHole(x_14);
lean_inc(x_2159);
x_2163 = l_Lean_Elab_Term_mkExplicitBinder(x_2159, x_2162);
x_2164 = lean_array_push(x_4, x_2163);
lean_inc(x_5);
x_2165 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2161, x_2164, x_5, x_2160);
if (lean_obj_tag(x_2165) == 0)
{
lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; uint8_t x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; 
x_2166 = lean_ctor_get(x_2165, 0);
lean_inc(x_2166);
x_2167 = lean_ctor_get(x_2166, 1);
lean_inc(x_2167);
x_2168 = lean_ctor_get(x_2165, 1);
lean_inc(x_2168);
lean_dec(x_2165);
x_2169 = lean_ctor_get(x_2166, 0);
lean_inc(x_2169);
if (lean_is_exclusive(x_2166)) {
 lean_ctor_release(x_2166, 0);
 lean_ctor_release(x_2166, 1);
 x_2170 = x_2166;
} else {
 lean_dec_ref(x_2166);
 x_2170 = lean_box(0);
}
x_2171 = lean_ctor_get(x_2167, 0);
lean_inc(x_2171);
if (lean_is_exclusive(x_2167)) {
 lean_ctor_release(x_2167, 0);
 lean_ctor_release(x_2167, 1);
 x_2172 = x_2167;
} else {
 lean_dec_ref(x_2167);
 x_2172 = lean_box(0);
}
x_2173 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2168);
lean_dec(x_5);
x_2174 = lean_ctor_get(x_2173, 1);
lean_inc(x_2174);
lean_dec(x_2173);
x_2175 = l_Lean_Elab_Term_getMainModule___rarg(x_2174);
x_2176 = lean_ctor_get(x_2175, 1);
lean_inc(x_2176);
if (lean_is_exclusive(x_2175)) {
 lean_ctor_release(x_2175, 0);
 lean_ctor_release(x_2175, 1);
 x_2177 = x_2175;
} else {
 lean_dec_ref(x_2175);
 x_2177 = lean_box(0);
}
x_2178 = l_Array_empty___closed__1;
x_2179 = lean_array_push(x_2178, x_2159);
x_2180 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2181 = lean_array_push(x_2179, x_2180);
x_2182 = l_Lean_mkTermIdFromIdent___closed__2;
x_2183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2183, 0, x_2182);
lean_ctor_set(x_2183, 1, x_2181);
x_2184 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2185 = lean_array_push(x_2184, x_2183);
x_2186 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2187, 0, x_2186);
lean_ctor_set(x_2187, 1, x_2185);
x_2188 = lean_array_push(x_2178, x_2187);
x_2189 = l_Lean_nullKind___closed__2;
x_2190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2190, 0, x_2189);
lean_ctor_set(x_2190, 1, x_2188);
x_2191 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2192 = lean_array_push(x_2191, x_2190);
x_2193 = lean_array_push(x_2192, x_2180);
x_2194 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2195 = lean_array_push(x_2193, x_2194);
x_2196 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2197 = lean_array_push(x_2195, x_2196);
lean_inc(x_14);
x_2198 = lean_array_push(x_2178, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2199 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2199 = lean_box(0);
}
if (lean_is_scalar(x_2199)) {
 x_2200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2200 = x_2199;
}
lean_ctor_set(x_2200, 0, x_2189);
lean_ctor_set(x_2200, 1, x_2198);
x_2201 = lean_array_push(x_2178, x_2200);
x_2202 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2203 = lean_array_push(x_2201, x_2202);
x_2204 = lean_array_push(x_2203, x_2171);
x_2205 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2206, 0, x_2205);
lean_ctor_set(x_2206, 1, x_2204);
x_2207 = lean_array_push(x_2178, x_2206);
x_2208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2208, 0, x_2189);
lean_ctor_set(x_2208, 1, x_2207);
x_2209 = lean_array_push(x_2197, x_2208);
x_2210 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2211, 0, x_2210);
lean_ctor_set(x_2211, 1, x_2209);
x_2212 = 1;
x_2213 = lean_box(x_2212);
if (lean_is_scalar(x_2172)) {
 x_2214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2214 = x_2172;
}
lean_ctor_set(x_2214, 0, x_2211);
lean_ctor_set(x_2214, 1, x_2213);
if (lean_is_scalar(x_2170)) {
 x_2215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2215 = x_2170;
}
lean_ctor_set(x_2215, 0, x_2169);
lean_ctor_set(x_2215, 1, x_2214);
if (lean_is_scalar(x_2177)) {
 x_2216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2216 = x_2177;
}
lean_ctor_set(x_2216, 0, x_2215);
lean_ctor_set(x_2216, 1, x_2176);
return x_2216;
}
else
{
lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; 
lean_dec(x_2159);
lean_dec(x_14);
lean_dec(x_5);
x_2217 = lean_ctor_get(x_2165, 0);
lean_inc(x_2217);
x_2218 = lean_ctor_get(x_2165, 1);
lean_inc(x_2218);
if (lean_is_exclusive(x_2165)) {
 lean_ctor_release(x_2165, 0);
 lean_ctor_release(x_2165, 1);
 x_2219 = x_2165;
} else {
 lean_dec_ref(x_2165);
 x_2219 = lean_box(0);
}
if (lean_is_scalar(x_2219)) {
 x_2220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2220 = x_2219;
}
lean_ctor_set(x_2220, 0, x_2217);
lean_ctor_set(x_2220, 1, x_2218);
return x_2220;
}
}
else
{
lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; 
x_2221 = l_Lean_Syntax_getArg(x_2150, x_2143);
lean_dec(x_2150);
x_2222 = l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(x_2147, x_5, x_6);
x_2223 = lean_ctor_get(x_2222, 0);
lean_inc(x_2223);
if (lean_obj_tag(x_2223) == 0)
{
lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; 
lean_dec(x_2221);
x_2224 = lean_ctor_get(x_2222, 1);
lean_inc(x_2224);
lean_dec(x_2222);
x_2225 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_2224);
x_2226 = lean_ctor_get(x_2225, 0);
lean_inc(x_2226);
x_2227 = lean_ctor_get(x_2225, 1);
lean_inc(x_2227);
lean_dec(x_2225);
x_2228 = lean_nat_add(x_3, x_2143);
lean_dec(x_3);
x_2229 = l_Lean_mkHole(x_14);
lean_inc(x_2226);
x_2230 = l_Lean_Elab_Term_mkExplicitBinder(x_2226, x_2229);
x_2231 = lean_array_push(x_4, x_2230);
lean_inc(x_5);
x_2232 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2228, x_2231, x_5, x_2227);
if (lean_obj_tag(x_2232) == 0)
{
lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; uint8_t x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; 
x_2233 = lean_ctor_get(x_2232, 0);
lean_inc(x_2233);
x_2234 = lean_ctor_get(x_2233, 1);
lean_inc(x_2234);
x_2235 = lean_ctor_get(x_2232, 1);
lean_inc(x_2235);
lean_dec(x_2232);
x_2236 = lean_ctor_get(x_2233, 0);
lean_inc(x_2236);
if (lean_is_exclusive(x_2233)) {
 lean_ctor_release(x_2233, 0);
 lean_ctor_release(x_2233, 1);
 x_2237 = x_2233;
} else {
 lean_dec_ref(x_2233);
 x_2237 = lean_box(0);
}
x_2238 = lean_ctor_get(x_2234, 0);
lean_inc(x_2238);
if (lean_is_exclusive(x_2234)) {
 lean_ctor_release(x_2234, 0);
 lean_ctor_release(x_2234, 1);
 x_2239 = x_2234;
} else {
 lean_dec_ref(x_2234);
 x_2239 = lean_box(0);
}
x_2240 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2235);
lean_dec(x_5);
x_2241 = lean_ctor_get(x_2240, 1);
lean_inc(x_2241);
lean_dec(x_2240);
x_2242 = l_Lean_Elab_Term_getMainModule___rarg(x_2241);
x_2243 = lean_ctor_get(x_2242, 1);
lean_inc(x_2243);
if (lean_is_exclusive(x_2242)) {
 lean_ctor_release(x_2242, 0);
 lean_ctor_release(x_2242, 1);
 x_2244 = x_2242;
} else {
 lean_dec_ref(x_2242);
 x_2244 = lean_box(0);
}
x_2245 = l_Array_empty___closed__1;
x_2246 = lean_array_push(x_2245, x_2226);
x_2247 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2248 = lean_array_push(x_2246, x_2247);
x_2249 = l_Lean_mkTermIdFromIdent___closed__2;
x_2250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2250, 0, x_2249);
lean_ctor_set(x_2250, 1, x_2248);
x_2251 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2252 = lean_array_push(x_2251, x_2250);
x_2253 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2254, 0, x_2253);
lean_ctor_set(x_2254, 1, x_2252);
x_2255 = lean_array_push(x_2245, x_2254);
x_2256 = l_Lean_nullKind___closed__2;
x_2257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2257, 0, x_2256);
lean_ctor_set(x_2257, 1, x_2255);
x_2258 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2259 = lean_array_push(x_2258, x_2257);
x_2260 = lean_array_push(x_2259, x_2247);
x_2261 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2262 = lean_array_push(x_2260, x_2261);
x_2263 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2264 = lean_array_push(x_2262, x_2263);
lean_inc(x_14);
x_2265 = lean_array_push(x_2245, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2266 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2266 = lean_box(0);
}
if (lean_is_scalar(x_2266)) {
 x_2267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2267 = x_2266;
}
lean_ctor_set(x_2267, 0, x_2256);
lean_ctor_set(x_2267, 1, x_2265);
x_2268 = lean_array_push(x_2245, x_2267);
x_2269 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2270 = lean_array_push(x_2268, x_2269);
x_2271 = lean_array_push(x_2270, x_2238);
x_2272 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2273, 0, x_2272);
lean_ctor_set(x_2273, 1, x_2271);
x_2274 = lean_array_push(x_2245, x_2273);
x_2275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2275, 0, x_2256);
lean_ctor_set(x_2275, 1, x_2274);
x_2276 = lean_array_push(x_2264, x_2275);
x_2277 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2278, 0, x_2277);
lean_ctor_set(x_2278, 1, x_2276);
x_2279 = 1;
x_2280 = lean_box(x_2279);
if (lean_is_scalar(x_2239)) {
 x_2281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2281 = x_2239;
}
lean_ctor_set(x_2281, 0, x_2278);
lean_ctor_set(x_2281, 1, x_2280);
if (lean_is_scalar(x_2237)) {
 x_2282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2282 = x_2237;
}
lean_ctor_set(x_2282, 0, x_2236);
lean_ctor_set(x_2282, 1, x_2281);
if (lean_is_scalar(x_2244)) {
 x_2283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2283 = x_2244;
}
lean_ctor_set(x_2283, 0, x_2282);
lean_ctor_set(x_2283, 1, x_2243);
return x_2283;
}
else
{
lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; 
lean_dec(x_2226);
lean_dec(x_14);
lean_dec(x_5);
x_2284 = lean_ctor_get(x_2232, 0);
lean_inc(x_2284);
x_2285 = lean_ctor_get(x_2232, 1);
lean_inc(x_2285);
if (lean_is_exclusive(x_2232)) {
 lean_ctor_release(x_2232, 0);
 lean_ctor_release(x_2232, 1);
 x_2286 = x_2232;
} else {
 lean_dec_ref(x_2232);
 x_2286 = lean_box(0);
}
if (lean_is_scalar(x_2286)) {
 x_2287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2287 = x_2286;
}
lean_ctor_set(x_2287, 0, x_2284);
lean_ctor_set(x_2287, 1, x_2285);
return x_2287;
}
}
else
{
lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; 
lean_dec(x_14);
x_2288 = lean_ctor_get(x_2222, 1);
lean_inc(x_2288);
lean_dec(x_2222);
x_2289 = lean_ctor_get(x_2223, 0);
lean_inc(x_2289);
lean_dec(x_2223);
x_2290 = lean_nat_add(x_3, x_2143);
lean_dec(x_3);
x_2291 = x_2289;
x_2292 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(x_2221, x_2146, x_2291);
x_2293 = x_2292;
x_2294 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2293, x_2293, x_2146, x_4);
lean_dec(x_2293);
x_3 = x_2290;
x_4 = x_2294;
x_6 = x_2288;
goto _start;
}
}
}
else
{
lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; 
lean_dec(x_2148);
lean_dec(x_2147);
x_2296 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2297 = lean_ctor_get(x_2296, 0);
lean_inc(x_2297);
x_2298 = lean_ctor_get(x_2296, 1);
lean_inc(x_2298);
lean_dec(x_2296);
x_2299 = lean_nat_add(x_3, x_2143);
lean_dec(x_3);
x_2300 = l_Lean_mkHole(x_14);
lean_inc(x_2297);
x_2301 = l_Lean_Elab_Term_mkExplicitBinder(x_2297, x_2300);
x_2302 = lean_array_push(x_4, x_2301);
lean_inc(x_5);
x_2303 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2299, x_2302, x_5, x_2298);
if (lean_obj_tag(x_2303) == 0)
{
lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; uint8_t x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; 
x_2304 = lean_ctor_get(x_2303, 0);
lean_inc(x_2304);
x_2305 = lean_ctor_get(x_2304, 1);
lean_inc(x_2305);
x_2306 = lean_ctor_get(x_2303, 1);
lean_inc(x_2306);
lean_dec(x_2303);
x_2307 = lean_ctor_get(x_2304, 0);
lean_inc(x_2307);
if (lean_is_exclusive(x_2304)) {
 lean_ctor_release(x_2304, 0);
 lean_ctor_release(x_2304, 1);
 x_2308 = x_2304;
} else {
 lean_dec_ref(x_2304);
 x_2308 = lean_box(0);
}
x_2309 = lean_ctor_get(x_2305, 0);
lean_inc(x_2309);
if (lean_is_exclusive(x_2305)) {
 lean_ctor_release(x_2305, 0);
 lean_ctor_release(x_2305, 1);
 x_2310 = x_2305;
} else {
 lean_dec_ref(x_2305);
 x_2310 = lean_box(0);
}
x_2311 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2306);
lean_dec(x_5);
x_2312 = lean_ctor_get(x_2311, 1);
lean_inc(x_2312);
lean_dec(x_2311);
x_2313 = l_Lean_Elab_Term_getMainModule___rarg(x_2312);
x_2314 = lean_ctor_get(x_2313, 1);
lean_inc(x_2314);
if (lean_is_exclusive(x_2313)) {
 lean_ctor_release(x_2313, 0);
 lean_ctor_release(x_2313, 1);
 x_2315 = x_2313;
} else {
 lean_dec_ref(x_2313);
 x_2315 = lean_box(0);
}
x_2316 = l_Array_empty___closed__1;
x_2317 = lean_array_push(x_2316, x_2297);
x_2318 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2319 = lean_array_push(x_2317, x_2318);
x_2320 = l_Lean_mkTermIdFromIdent___closed__2;
x_2321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2321, 0, x_2320);
lean_ctor_set(x_2321, 1, x_2319);
x_2322 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2323 = lean_array_push(x_2322, x_2321);
x_2324 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2325, 0, x_2324);
lean_ctor_set(x_2325, 1, x_2323);
x_2326 = lean_array_push(x_2316, x_2325);
x_2327 = l_Lean_nullKind___closed__2;
x_2328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2328, 0, x_2327);
lean_ctor_set(x_2328, 1, x_2326);
x_2329 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2330 = lean_array_push(x_2329, x_2328);
x_2331 = lean_array_push(x_2330, x_2318);
x_2332 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2333 = lean_array_push(x_2331, x_2332);
x_2334 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2335 = lean_array_push(x_2333, x_2334);
lean_inc(x_14);
x_2336 = lean_array_push(x_2316, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2337 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2337 = lean_box(0);
}
if (lean_is_scalar(x_2337)) {
 x_2338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2338 = x_2337;
}
lean_ctor_set(x_2338, 0, x_2327);
lean_ctor_set(x_2338, 1, x_2336);
x_2339 = lean_array_push(x_2316, x_2338);
x_2340 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2341 = lean_array_push(x_2339, x_2340);
x_2342 = lean_array_push(x_2341, x_2309);
x_2343 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2344, 0, x_2343);
lean_ctor_set(x_2344, 1, x_2342);
x_2345 = lean_array_push(x_2316, x_2344);
x_2346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2346, 0, x_2327);
lean_ctor_set(x_2346, 1, x_2345);
x_2347 = lean_array_push(x_2335, x_2346);
x_2348 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2349, 0, x_2348);
lean_ctor_set(x_2349, 1, x_2347);
x_2350 = 1;
x_2351 = lean_box(x_2350);
if (lean_is_scalar(x_2310)) {
 x_2352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2352 = x_2310;
}
lean_ctor_set(x_2352, 0, x_2349);
lean_ctor_set(x_2352, 1, x_2351);
if (lean_is_scalar(x_2308)) {
 x_2353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2353 = x_2308;
}
lean_ctor_set(x_2353, 0, x_2307);
lean_ctor_set(x_2353, 1, x_2352);
if (lean_is_scalar(x_2315)) {
 x_2354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2354 = x_2315;
}
lean_ctor_set(x_2354, 0, x_2353);
lean_ctor_set(x_2354, 1, x_2314);
return x_2354;
}
else
{
lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; 
lean_dec(x_2297);
lean_dec(x_14);
lean_dec(x_5);
x_2355 = lean_ctor_get(x_2303, 0);
lean_inc(x_2355);
x_2356 = lean_ctor_get(x_2303, 1);
lean_inc(x_2356);
if (lean_is_exclusive(x_2303)) {
 lean_ctor_release(x_2303, 0);
 lean_ctor_release(x_2303, 1);
 x_2357 = x_2303;
} else {
 lean_dec_ref(x_2303);
 x_2357 = lean_box(0);
}
if (lean_is_scalar(x_2357)) {
 x_2358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2358 = x_2357;
}
lean_ctor_set(x_2358, 0, x_2355);
lean_ctor_set(x_2358, 1, x_2356);
return x_2358;
}
}
}
else
{
lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; 
lean_dec(x_2144);
x_2359 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2360 = lean_ctor_get(x_2359, 0);
lean_inc(x_2360);
x_2361 = lean_ctor_get(x_2359, 1);
lean_inc(x_2361);
lean_dec(x_2359);
x_2362 = lean_nat_add(x_3, x_2143);
lean_dec(x_3);
x_2363 = l_Lean_mkHole(x_14);
lean_inc(x_2360);
x_2364 = l_Lean_Elab_Term_mkExplicitBinder(x_2360, x_2363);
x_2365 = lean_array_push(x_4, x_2364);
lean_inc(x_5);
x_2366 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2362, x_2365, x_5, x_2361);
if (lean_obj_tag(x_2366) == 0)
{
lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; uint8_t x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; 
x_2367 = lean_ctor_get(x_2366, 0);
lean_inc(x_2367);
x_2368 = lean_ctor_get(x_2367, 1);
lean_inc(x_2368);
x_2369 = lean_ctor_get(x_2366, 1);
lean_inc(x_2369);
lean_dec(x_2366);
x_2370 = lean_ctor_get(x_2367, 0);
lean_inc(x_2370);
if (lean_is_exclusive(x_2367)) {
 lean_ctor_release(x_2367, 0);
 lean_ctor_release(x_2367, 1);
 x_2371 = x_2367;
} else {
 lean_dec_ref(x_2367);
 x_2371 = lean_box(0);
}
x_2372 = lean_ctor_get(x_2368, 0);
lean_inc(x_2372);
if (lean_is_exclusive(x_2368)) {
 lean_ctor_release(x_2368, 0);
 lean_ctor_release(x_2368, 1);
 x_2373 = x_2368;
} else {
 lean_dec_ref(x_2368);
 x_2373 = lean_box(0);
}
x_2374 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2369);
lean_dec(x_5);
x_2375 = lean_ctor_get(x_2374, 1);
lean_inc(x_2375);
lean_dec(x_2374);
x_2376 = l_Lean_Elab_Term_getMainModule___rarg(x_2375);
x_2377 = lean_ctor_get(x_2376, 1);
lean_inc(x_2377);
if (lean_is_exclusive(x_2376)) {
 lean_ctor_release(x_2376, 0);
 lean_ctor_release(x_2376, 1);
 x_2378 = x_2376;
} else {
 lean_dec_ref(x_2376);
 x_2378 = lean_box(0);
}
x_2379 = l_Array_empty___closed__1;
x_2380 = lean_array_push(x_2379, x_2360);
x_2381 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2382 = lean_array_push(x_2380, x_2381);
x_2383 = l_Lean_mkTermIdFromIdent___closed__2;
x_2384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2384, 0, x_2383);
lean_ctor_set(x_2384, 1, x_2382);
x_2385 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2386 = lean_array_push(x_2385, x_2384);
x_2387 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2388, 0, x_2387);
lean_ctor_set(x_2388, 1, x_2386);
x_2389 = lean_array_push(x_2379, x_2388);
x_2390 = l_Lean_nullKind___closed__2;
x_2391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2391, 0, x_2390);
lean_ctor_set(x_2391, 1, x_2389);
x_2392 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2393 = lean_array_push(x_2392, x_2391);
x_2394 = lean_array_push(x_2393, x_2381);
x_2395 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2396 = lean_array_push(x_2394, x_2395);
x_2397 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2398 = lean_array_push(x_2396, x_2397);
lean_inc(x_14);
x_2399 = lean_array_push(x_2379, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2400 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2400 = lean_box(0);
}
if (lean_is_scalar(x_2400)) {
 x_2401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2401 = x_2400;
}
lean_ctor_set(x_2401, 0, x_2390);
lean_ctor_set(x_2401, 1, x_2399);
x_2402 = lean_array_push(x_2379, x_2401);
x_2403 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2404 = lean_array_push(x_2402, x_2403);
x_2405 = lean_array_push(x_2404, x_2372);
x_2406 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2407, 0, x_2406);
lean_ctor_set(x_2407, 1, x_2405);
x_2408 = lean_array_push(x_2379, x_2407);
x_2409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2409, 0, x_2390);
lean_ctor_set(x_2409, 1, x_2408);
x_2410 = lean_array_push(x_2398, x_2409);
x_2411 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2412, 0, x_2411);
lean_ctor_set(x_2412, 1, x_2410);
x_2413 = 1;
x_2414 = lean_box(x_2413);
if (lean_is_scalar(x_2373)) {
 x_2415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2415 = x_2373;
}
lean_ctor_set(x_2415, 0, x_2412);
lean_ctor_set(x_2415, 1, x_2414);
if (lean_is_scalar(x_2371)) {
 x_2416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2416 = x_2371;
}
lean_ctor_set(x_2416, 0, x_2370);
lean_ctor_set(x_2416, 1, x_2415);
if (lean_is_scalar(x_2378)) {
 x_2417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2417 = x_2378;
}
lean_ctor_set(x_2417, 0, x_2416);
lean_ctor_set(x_2417, 1, x_2377);
return x_2417;
}
else
{
lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; 
lean_dec(x_2360);
lean_dec(x_14);
lean_dec(x_5);
x_2418 = lean_ctor_get(x_2366, 0);
lean_inc(x_2418);
x_2419 = lean_ctor_get(x_2366, 1);
lean_inc(x_2419);
if (lean_is_exclusive(x_2366)) {
 lean_ctor_release(x_2366, 0);
 lean_ctor_release(x_2366, 1);
 x_2420 = x_2366;
} else {
 lean_dec_ref(x_2366);
 x_2420 = lean_box(0);
}
if (lean_is_scalar(x_2420)) {
 x_2421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2421 = x_2420;
}
lean_ctor_set(x_2421, 0, x_2418);
lean_ctor_set(x_2421, 1, x_2419);
return x_2421;
}
}
}
}
else
{
lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; 
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2422 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2423 = lean_ctor_get(x_2422, 0);
lean_inc(x_2423);
x_2424 = lean_ctor_get(x_2422, 1);
lean_inc(x_2424);
lean_dec(x_2422);
x_2425 = lean_unsigned_to_nat(1u);
x_2426 = lean_nat_add(x_3, x_2425);
lean_dec(x_3);
x_2427 = l_Lean_Elab_Term_mkExplicitBinder(x_2423, x_14);
x_2428 = lean_array_push(x_4, x_2427);
x_3 = x_2426;
x_4 = x_2428;
x_6 = x_2424;
goto _start;
}
}
else
{
lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; 
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2430 = lean_unsigned_to_nat(1u);
x_2431 = lean_nat_add(x_3, x_2430);
lean_dec(x_3);
x_2432 = lean_array_push(x_4, x_14);
x_3 = x_2431;
x_4 = x_2432;
goto _start;
}
}
else
{
lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; 
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2434 = lean_unsigned_to_nat(1u);
x_2435 = lean_nat_add(x_3, x_2434);
lean_dec(x_3);
x_2436 = lean_array_push(x_4, x_14);
x_3 = x_2435;
x_4 = x_2436;
goto _start;
}
}
else
{
lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; 
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2438 = lean_unsigned_to_nat(1u);
x_2439 = lean_nat_add(x_3, x_2438);
lean_dec(x_3);
x_2440 = lean_array_push(x_4, x_14);
x_3 = x_2439;
x_4 = x_2440;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_2442; size_t x_2443; lean_object* x_2444; size_t x_2445; lean_object* x_2446; lean_object* x_2447; uint8_t x_2448; 
x_2442 = lean_ctor_get(x_17, 1);
x_2443 = lean_ctor_get_usize(x_17, 2);
lean_inc(x_2442);
lean_dec(x_17);
x_2444 = lean_ctor_get(x_18, 1);
lean_inc(x_2444);
x_2445 = lean_ctor_get_usize(x_18, 2);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_2446 = x_18;
} else {
 lean_dec_ref(x_18);
 x_2446 = lean_box(0);
}
x_2447 = l_Lean_mkAppStx___closed__1;
x_2448 = lean_string_dec_eq(x_2444, x_2447);
lean_dec(x_2444);
if (x_2448 == 0)
{
uint8_t x_2449; lean_object* x_2450; 
lean_dec(x_2446);
lean_dec(x_2442);
lean_free_object(x_16);
lean_dec(x_25);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2449 = 1;
lean_inc(x_14);
x_2450 = l_Lean_Syntax_isTermId_x3f(x_14, x_2449);
if (lean_obj_tag(x_2450) == 0)
{
lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; 
x_2451 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2452 = lean_ctor_get(x_2451, 0);
lean_inc(x_2452);
x_2453 = lean_ctor_get(x_2451, 1);
lean_inc(x_2453);
lean_dec(x_2451);
x_2454 = lean_unsigned_to_nat(1u);
x_2455 = lean_nat_add(x_3, x_2454);
lean_dec(x_3);
x_2456 = l_Lean_mkHole(x_14);
lean_inc(x_2452);
x_2457 = l_Lean_Elab_Term_mkExplicitBinder(x_2452, x_2456);
x_2458 = lean_array_push(x_4, x_2457);
lean_inc(x_5);
x_2459 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2455, x_2458, x_5, x_2453);
if (lean_obj_tag(x_2459) == 0)
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; 
x_2460 = lean_ctor_get(x_2459, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2460, 1);
lean_inc(x_2461);
x_2462 = lean_ctor_get(x_2459, 1);
lean_inc(x_2462);
lean_dec(x_2459);
x_2463 = lean_ctor_get(x_2460, 0);
lean_inc(x_2463);
if (lean_is_exclusive(x_2460)) {
 lean_ctor_release(x_2460, 0);
 lean_ctor_release(x_2460, 1);
 x_2464 = x_2460;
} else {
 lean_dec_ref(x_2460);
 x_2464 = lean_box(0);
}
x_2465 = lean_ctor_get(x_2461, 0);
lean_inc(x_2465);
if (lean_is_exclusive(x_2461)) {
 lean_ctor_release(x_2461, 0);
 lean_ctor_release(x_2461, 1);
 x_2466 = x_2461;
} else {
 lean_dec_ref(x_2461);
 x_2466 = lean_box(0);
}
x_2467 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2462);
lean_dec(x_5);
x_2468 = lean_ctor_get(x_2467, 1);
lean_inc(x_2468);
lean_dec(x_2467);
x_2469 = l_Lean_Elab_Term_getMainModule___rarg(x_2468);
x_2470 = lean_ctor_get(x_2469, 1);
lean_inc(x_2470);
if (lean_is_exclusive(x_2469)) {
 lean_ctor_release(x_2469, 0);
 lean_ctor_release(x_2469, 1);
 x_2471 = x_2469;
} else {
 lean_dec_ref(x_2469);
 x_2471 = lean_box(0);
}
x_2472 = l_Array_empty___closed__1;
x_2473 = lean_array_push(x_2472, x_2452);
x_2474 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2475 = lean_array_push(x_2473, x_2474);
x_2476 = l_Lean_mkTermIdFromIdent___closed__2;
x_2477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2477, 0, x_2476);
lean_ctor_set(x_2477, 1, x_2475);
x_2478 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2479 = lean_array_push(x_2478, x_2477);
x_2480 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2481, 0, x_2480);
lean_ctor_set(x_2481, 1, x_2479);
x_2482 = lean_array_push(x_2472, x_2481);
x_2483 = l_Lean_nullKind___closed__2;
x_2484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2484, 0, x_2483);
lean_ctor_set(x_2484, 1, x_2482);
x_2485 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2486 = lean_array_push(x_2485, x_2484);
x_2487 = lean_array_push(x_2486, x_2474);
x_2488 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2489 = lean_array_push(x_2487, x_2488);
x_2490 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2491 = lean_array_push(x_2489, x_2490);
lean_inc(x_14);
x_2492 = lean_array_push(x_2472, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2493 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2493 = lean_box(0);
}
if (lean_is_scalar(x_2493)) {
 x_2494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2494 = x_2493;
}
lean_ctor_set(x_2494, 0, x_2483);
lean_ctor_set(x_2494, 1, x_2492);
x_2495 = lean_array_push(x_2472, x_2494);
x_2496 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2497 = lean_array_push(x_2495, x_2496);
x_2498 = lean_array_push(x_2497, x_2465);
x_2499 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2500, 0, x_2499);
lean_ctor_set(x_2500, 1, x_2498);
x_2501 = lean_array_push(x_2472, x_2500);
x_2502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2502, 0, x_2483);
lean_ctor_set(x_2502, 1, x_2501);
x_2503 = lean_array_push(x_2491, x_2502);
x_2504 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2505, 0, x_2504);
lean_ctor_set(x_2505, 1, x_2503);
x_2506 = lean_box(x_2449);
if (lean_is_scalar(x_2466)) {
 x_2507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2507 = x_2466;
}
lean_ctor_set(x_2507, 0, x_2505);
lean_ctor_set(x_2507, 1, x_2506);
if (lean_is_scalar(x_2464)) {
 x_2508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2508 = x_2464;
}
lean_ctor_set(x_2508, 0, x_2463);
lean_ctor_set(x_2508, 1, x_2507);
if (lean_is_scalar(x_2471)) {
 x_2509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2509 = x_2471;
}
lean_ctor_set(x_2509, 0, x_2508);
lean_ctor_set(x_2509, 1, x_2470);
return x_2509;
}
else
{
lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; 
lean_dec(x_2452);
lean_dec(x_14);
lean_dec(x_5);
x_2510 = lean_ctor_get(x_2459, 0);
lean_inc(x_2510);
x_2511 = lean_ctor_get(x_2459, 1);
lean_inc(x_2511);
if (lean_is_exclusive(x_2459)) {
 lean_ctor_release(x_2459, 0);
 lean_ctor_release(x_2459, 1);
 x_2512 = x_2459;
} else {
 lean_dec_ref(x_2459);
 x_2512 = lean_box(0);
}
if (lean_is_scalar(x_2512)) {
 x_2513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2513 = x_2512;
}
lean_ctor_set(x_2513, 0, x_2510);
lean_ctor_set(x_2513, 1, x_2511);
return x_2513;
}
}
else
{
lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; uint8_t x_2517; 
x_2514 = lean_ctor_get(x_2450, 0);
lean_inc(x_2514);
lean_dec(x_2450);
x_2515 = lean_ctor_get(x_2514, 0);
lean_inc(x_2515);
x_2516 = lean_ctor_get(x_2514, 1);
lean_inc(x_2516);
lean_dec(x_2514);
x_2517 = l_Lean_Syntax_isNone(x_2516);
lean_dec(x_2516);
if (x_2517 == 0)
{
lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; 
lean_dec(x_2515);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2518 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_2519 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_2518, x_5, x_6);
lean_dec(x_14);
x_2520 = lean_ctor_get(x_2519, 0);
lean_inc(x_2520);
x_2521 = lean_ctor_get(x_2519, 1);
lean_inc(x_2521);
if (lean_is_exclusive(x_2519)) {
 lean_ctor_release(x_2519, 0);
 lean_ctor_release(x_2519, 1);
 x_2522 = x_2519;
} else {
 lean_dec_ref(x_2519);
 x_2522 = lean_box(0);
}
if (lean_is_scalar(x_2522)) {
 x_2523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2523 = x_2522;
}
lean_ctor_set(x_2523, 0, x_2520);
lean_ctor_set(x_2523, 1, x_2521);
return x_2523;
}
else
{
lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; 
x_2524 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_2525 = lean_unsigned_to_nat(1u);
x_2526 = lean_nat_add(x_3, x_2525);
lean_dec(x_3);
x_2527 = l_Lean_Elab_Term_mkExplicitBinder(x_2515, x_2524);
x_2528 = lean_array_push(x_4, x_2527);
x_3 = x_2526;
x_4 = x_2528;
goto _start;
}
}
}
else
{
lean_object* x_2530; uint8_t x_2531; 
x_2530 = l_Lean_mkAppStx___closed__3;
x_2531 = lean_string_dec_eq(x_2442, x_2530);
if (x_2531 == 0)
{
lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; uint8_t x_2535; lean_object* x_2536; 
if (lean_is_scalar(x_2446)) {
 x_2532 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2532 = x_2446;
}
lean_ctor_set(x_2532, 0, x_19);
lean_ctor_set(x_2532, 1, x_2447);
lean_ctor_set_usize(x_2532, 2, x_2445);
x_2533 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2533, 0, x_2532);
lean_ctor_set(x_2533, 1, x_2442);
lean_ctor_set_usize(x_2533, 2, x_2443);
lean_ctor_set(x_16, 0, x_2533);
x_2534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2534, 0, x_15);
lean_ctor_set(x_2534, 1, x_20);
x_2535 = 1;
lean_inc(x_2534);
x_2536 = l_Lean_Syntax_isTermId_x3f(x_2534, x_2535);
if (lean_obj_tag(x_2536) == 0)
{
lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; 
lean_dec(x_2534);
x_2537 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2538 = lean_ctor_get(x_2537, 0);
lean_inc(x_2538);
x_2539 = lean_ctor_get(x_2537, 1);
lean_inc(x_2539);
lean_dec(x_2537);
x_2540 = lean_unsigned_to_nat(1u);
x_2541 = lean_nat_add(x_3, x_2540);
lean_dec(x_3);
x_2542 = l_Lean_mkHole(x_14);
lean_inc(x_2538);
x_2543 = l_Lean_Elab_Term_mkExplicitBinder(x_2538, x_2542);
x_2544 = lean_array_push(x_4, x_2543);
lean_inc(x_5);
x_2545 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2541, x_2544, x_5, x_2539);
if (lean_obj_tag(x_2545) == 0)
{
lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; 
x_2546 = lean_ctor_get(x_2545, 0);
lean_inc(x_2546);
x_2547 = lean_ctor_get(x_2546, 1);
lean_inc(x_2547);
x_2548 = lean_ctor_get(x_2545, 1);
lean_inc(x_2548);
lean_dec(x_2545);
x_2549 = lean_ctor_get(x_2546, 0);
lean_inc(x_2549);
if (lean_is_exclusive(x_2546)) {
 lean_ctor_release(x_2546, 0);
 lean_ctor_release(x_2546, 1);
 x_2550 = x_2546;
} else {
 lean_dec_ref(x_2546);
 x_2550 = lean_box(0);
}
x_2551 = lean_ctor_get(x_2547, 0);
lean_inc(x_2551);
if (lean_is_exclusive(x_2547)) {
 lean_ctor_release(x_2547, 0);
 lean_ctor_release(x_2547, 1);
 x_2552 = x_2547;
} else {
 lean_dec_ref(x_2547);
 x_2552 = lean_box(0);
}
x_2553 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2548);
lean_dec(x_5);
x_2554 = lean_ctor_get(x_2553, 1);
lean_inc(x_2554);
lean_dec(x_2553);
x_2555 = l_Lean_Elab_Term_getMainModule___rarg(x_2554);
x_2556 = lean_ctor_get(x_2555, 1);
lean_inc(x_2556);
if (lean_is_exclusive(x_2555)) {
 lean_ctor_release(x_2555, 0);
 lean_ctor_release(x_2555, 1);
 x_2557 = x_2555;
} else {
 lean_dec_ref(x_2555);
 x_2557 = lean_box(0);
}
x_2558 = l_Array_empty___closed__1;
x_2559 = lean_array_push(x_2558, x_2538);
x_2560 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2561 = lean_array_push(x_2559, x_2560);
x_2562 = l_Lean_mkTermIdFromIdent___closed__2;
x_2563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2563, 0, x_2562);
lean_ctor_set(x_2563, 1, x_2561);
x_2564 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2565 = lean_array_push(x_2564, x_2563);
x_2566 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2567, 0, x_2566);
lean_ctor_set(x_2567, 1, x_2565);
x_2568 = lean_array_push(x_2558, x_2567);
x_2569 = l_Lean_nullKind___closed__2;
x_2570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2570, 0, x_2569);
lean_ctor_set(x_2570, 1, x_2568);
x_2571 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2572 = lean_array_push(x_2571, x_2570);
x_2573 = lean_array_push(x_2572, x_2560);
x_2574 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2575 = lean_array_push(x_2573, x_2574);
x_2576 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2577 = lean_array_push(x_2575, x_2576);
lean_inc(x_14);
x_2578 = lean_array_push(x_2558, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2579 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2579 = lean_box(0);
}
if (lean_is_scalar(x_2579)) {
 x_2580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2580 = x_2579;
}
lean_ctor_set(x_2580, 0, x_2569);
lean_ctor_set(x_2580, 1, x_2578);
x_2581 = lean_array_push(x_2558, x_2580);
x_2582 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2583 = lean_array_push(x_2581, x_2582);
x_2584 = lean_array_push(x_2583, x_2551);
x_2585 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2586, 0, x_2585);
lean_ctor_set(x_2586, 1, x_2584);
x_2587 = lean_array_push(x_2558, x_2586);
x_2588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2588, 0, x_2569);
lean_ctor_set(x_2588, 1, x_2587);
x_2589 = lean_array_push(x_2577, x_2588);
x_2590 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2591, 0, x_2590);
lean_ctor_set(x_2591, 1, x_2589);
x_2592 = lean_box(x_2535);
if (lean_is_scalar(x_2552)) {
 x_2593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2593 = x_2552;
}
lean_ctor_set(x_2593, 0, x_2591);
lean_ctor_set(x_2593, 1, x_2592);
if (lean_is_scalar(x_2550)) {
 x_2594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2594 = x_2550;
}
lean_ctor_set(x_2594, 0, x_2549);
lean_ctor_set(x_2594, 1, x_2593);
if (lean_is_scalar(x_2557)) {
 x_2595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2595 = x_2557;
}
lean_ctor_set(x_2595, 0, x_2594);
lean_ctor_set(x_2595, 1, x_2556);
return x_2595;
}
else
{
lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; 
lean_dec(x_2538);
lean_dec(x_14);
lean_dec(x_5);
x_2596 = lean_ctor_get(x_2545, 0);
lean_inc(x_2596);
x_2597 = lean_ctor_get(x_2545, 1);
lean_inc(x_2597);
if (lean_is_exclusive(x_2545)) {
 lean_ctor_release(x_2545, 0);
 lean_ctor_release(x_2545, 1);
 x_2598 = x_2545;
} else {
 lean_dec_ref(x_2545);
 x_2598 = lean_box(0);
}
if (lean_is_scalar(x_2598)) {
 x_2599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2599 = x_2598;
}
lean_ctor_set(x_2599, 0, x_2596);
lean_ctor_set(x_2599, 1, x_2597);
return x_2599;
}
}
else
{
lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; uint8_t x_2603; 
lean_dec(x_14);
x_2600 = lean_ctor_get(x_2536, 0);
lean_inc(x_2600);
lean_dec(x_2536);
x_2601 = lean_ctor_get(x_2600, 0);
lean_inc(x_2601);
x_2602 = lean_ctor_get(x_2600, 1);
lean_inc(x_2602);
lean_dec(x_2600);
x_2603 = l_Lean_Syntax_isNone(x_2602);
lean_dec(x_2602);
if (x_2603 == 0)
{
lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; 
lean_dec(x_2601);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2604 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_2605 = l_Lean_Elab_Term_throwErrorAt___rarg(x_2534, x_2604, x_5, x_6);
lean_dec(x_2534);
x_2606 = lean_ctor_get(x_2605, 0);
lean_inc(x_2606);
x_2607 = lean_ctor_get(x_2605, 1);
lean_inc(x_2607);
if (lean_is_exclusive(x_2605)) {
 lean_ctor_release(x_2605, 0);
 lean_ctor_release(x_2605, 1);
 x_2608 = x_2605;
} else {
 lean_dec_ref(x_2605);
 x_2608 = lean_box(0);
}
if (lean_is_scalar(x_2608)) {
 x_2609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2609 = x_2608;
}
lean_ctor_set(x_2609, 0, x_2606);
lean_ctor_set(x_2609, 1, x_2607);
return x_2609;
}
else
{
lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; 
x_2610 = l_Lean_mkHole(x_2534);
lean_dec(x_2534);
x_2611 = lean_unsigned_to_nat(1u);
x_2612 = lean_nat_add(x_3, x_2611);
lean_dec(x_3);
x_2613 = l_Lean_Elab_Term_mkExplicitBinder(x_2601, x_2610);
x_2614 = lean_array_push(x_4, x_2613);
x_3 = x_2612;
x_4 = x_2614;
goto _start;
}
}
}
else
{
lean_object* x_2616; uint8_t x_2617; 
lean_dec(x_2442);
x_2616 = l_Lean_mkAppStx___closed__5;
x_2617 = lean_string_dec_eq(x_25, x_2616);
if (x_2617 == 0)
{
lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; uint8_t x_2621; lean_object* x_2622; 
if (lean_is_scalar(x_2446)) {
 x_2618 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2618 = x_2446;
}
lean_ctor_set(x_2618, 0, x_19);
lean_ctor_set(x_2618, 1, x_2447);
lean_ctor_set_usize(x_2618, 2, x_2445);
x_2619 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2619, 0, x_2618);
lean_ctor_set(x_2619, 1, x_2530);
lean_ctor_set_usize(x_2619, 2, x_2443);
lean_ctor_set(x_16, 0, x_2619);
x_2620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2620, 0, x_15);
lean_ctor_set(x_2620, 1, x_20);
x_2621 = 1;
lean_inc(x_2620);
x_2622 = l_Lean_Syntax_isTermId_x3f(x_2620, x_2621);
if (lean_obj_tag(x_2622) == 0)
{
lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; 
lean_dec(x_2620);
x_2623 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2624 = lean_ctor_get(x_2623, 0);
lean_inc(x_2624);
x_2625 = lean_ctor_get(x_2623, 1);
lean_inc(x_2625);
lean_dec(x_2623);
x_2626 = lean_unsigned_to_nat(1u);
x_2627 = lean_nat_add(x_3, x_2626);
lean_dec(x_3);
x_2628 = l_Lean_mkHole(x_14);
lean_inc(x_2624);
x_2629 = l_Lean_Elab_Term_mkExplicitBinder(x_2624, x_2628);
x_2630 = lean_array_push(x_4, x_2629);
lean_inc(x_5);
x_2631 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2627, x_2630, x_5, x_2625);
if (lean_obj_tag(x_2631) == 0)
{
lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; 
x_2632 = lean_ctor_get(x_2631, 0);
lean_inc(x_2632);
x_2633 = lean_ctor_get(x_2632, 1);
lean_inc(x_2633);
x_2634 = lean_ctor_get(x_2631, 1);
lean_inc(x_2634);
lean_dec(x_2631);
x_2635 = lean_ctor_get(x_2632, 0);
lean_inc(x_2635);
if (lean_is_exclusive(x_2632)) {
 lean_ctor_release(x_2632, 0);
 lean_ctor_release(x_2632, 1);
 x_2636 = x_2632;
} else {
 lean_dec_ref(x_2632);
 x_2636 = lean_box(0);
}
x_2637 = lean_ctor_get(x_2633, 0);
lean_inc(x_2637);
if (lean_is_exclusive(x_2633)) {
 lean_ctor_release(x_2633, 0);
 lean_ctor_release(x_2633, 1);
 x_2638 = x_2633;
} else {
 lean_dec_ref(x_2633);
 x_2638 = lean_box(0);
}
x_2639 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2634);
lean_dec(x_5);
x_2640 = lean_ctor_get(x_2639, 1);
lean_inc(x_2640);
lean_dec(x_2639);
x_2641 = l_Lean_Elab_Term_getMainModule___rarg(x_2640);
x_2642 = lean_ctor_get(x_2641, 1);
lean_inc(x_2642);
if (lean_is_exclusive(x_2641)) {
 lean_ctor_release(x_2641, 0);
 lean_ctor_release(x_2641, 1);
 x_2643 = x_2641;
} else {
 lean_dec_ref(x_2641);
 x_2643 = lean_box(0);
}
x_2644 = l_Array_empty___closed__1;
x_2645 = lean_array_push(x_2644, x_2624);
x_2646 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2647 = lean_array_push(x_2645, x_2646);
x_2648 = l_Lean_mkTermIdFromIdent___closed__2;
x_2649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2649, 0, x_2648);
lean_ctor_set(x_2649, 1, x_2647);
x_2650 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2651 = lean_array_push(x_2650, x_2649);
x_2652 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2653, 0, x_2652);
lean_ctor_set(x_2653, 1, x_2651);
x_2654 = lean_array_push(x_2644, x_2653);
x_2655 = l_Lean_nullKind___closed__2;
x_2656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2656, 0, x_2655);
lean_ctor_set(x_2656, 1, x_2654);
x_2657 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2658 = lean_array_push(x_2657, x_2656);
x_2659 = lean_array_push(x_2658, x_2646);
x_2660 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2661 = lean_array_push(x_2659, x_2660);
x_2662 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2663 = lean_array_push(x_2661, x_2662);
lean_inc(x_14);
x_2664 = lean_array_push(x_2644, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2665 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2665 = lean_box(0);
}
if (lean_is_scalar(x_2665)) {
 x_2666 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2666 = x_2665;
}
lean_ctor_set(x_2666, 0, x_2655);
lean_ctor_set(x_2666, 1, x_2664);
x_2667 = lean_array_push(x_2644, x_2666);
x_2668 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2669 = lean_array_push(x_2667, x_2668);
x_2670 = lean_array_push(x_2669, x_2637);
x_2671 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2672, 0, x_2671);
lean_ctor_set(x_2672, 1, x_2670);
x_2673 = lean_array_push(x_2644, x_2672);
x_2674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2674, 0, x_2655);
lean_ctor_set(x_2674, 1, x_2673);
x_2675 = lean_array_push(x_2663, x_2674);
x_2676 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2677, 0, x_2676);
lean_ctor_set(x_2677, 1, x_2675);
x_2678 = lean_box(x_2621);
if (lean_is_scalar(x_2638)) {
 x_2679 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2679 = x_2638;
}
lean_ctor_set(x_2679, 0, x_2677);
lean_ctor_set(x_2679, 1, x_2678);
if (lean_is_scalar(x_2636)) {
 x_2680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2680 = x_2636;
}
lean_ctor_set(x_2680, 0, x_2635);
lean_ctor_set(x_2680, 1, x_2679);
if (lean_is_scalar(x_2643)) {
 x_2681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2681 = x_2643;
}
lean_ctor_set(x_2681, 0, x_2680);
lean_ctor_set(x_2681, 1, x_2642);
return x_2681;
}
else
{
lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; 
lean_dec(x_2624);
lean_dec(x_14);
lean_dec(x_5);
x_2682 = lean_ctor_get(x_2631, 0);
lean_inc(x_2682);
x_2683 = lean_ctor_get(x_2631, 1);
lean_inc(x_2683);
if (lean_is_exclusive(x_2631)) {
 lean_ctor_release(x_2631, 0);
 lean_ctor_release(x_2631, 1);
 x_2684 = x_2631;
} else {
 lean_dec_ref(x_2631);
 x_2684 = lean_box(0);
}
if (lean_is_scalar(x_2684)) {
 x_2685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2685 = x_2684;
}
lean_ctor_set(x_2685, 0, x_2682);
lean_ctor_set(x_2685, 1, x_2683);
return x_2685;
}
}
else
{
lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; uint8_t x_2689; 
lean_dec(x_14);
x_2686 = lean_ctor_get(x_2622, 0);
lean_inc(x_2686);
lean_dec(x_2622);
x_2687 = lean_ctor_get(x_2686, 0);
lean_inc(x_2687);
x_2688 = lean_ctor_get(x_2686, 1);
lean_inc(x_2688);
lean_dec(x_2686);
x_2689 = l_Lean_Syntax_isNone(x_2688);
lean_dec(x_2688);
if (x_2689 == 0)
{
lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; 
lean_dec(x_2687);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2690 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_2691 = l_Lean_Elab_Term_throwErrorAt___rarg(x_2620, x_2690, x_5, x_6);
lean_dec(x_2620);
x_2692 = lean_ctor_get(x_2691, 0);
lean_inc(x_2692);
x_2693 = lean_ctor_get(x_2691, 1);
lean_inc(x_2693);
if (lean_is_exclusive(x_2691)) {
 lean_ctor_release(x_2691, 0);
 lean_ctor_release(x_2691, 1);
 x_2694 = x_2691;
} else {
 lean_dec_ref(x_2691);
 x_2694 = lean_box(0);
}
if (lean_is_scalar(x_2694)) {
 x_2695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2695 = x_2694;
}
lean_ctor_set(x_2695, 0, x_2692);
lean_ctor_set(x_2695, 1, x_2693);
return x_2695;
}
else
{
lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; 
x_2696 = l_Lean_mkHole(x_2620);
lean_dec(x_2620);
x_2697 = lean_unsigned_to_nat(1u);
x_2698 = lean_nat_add(x_3, x_2697);
lean_dec(x_3);
x_2699 = l_Lean_Elab_Term_mkExplicitBinder(x_2687, x_2696);
x_2700 = lean_array_push(x_4, x_2699);
x_3 = x_2698;
x_4 = x_2700;
goto _start;
}
}
}
else
{
lean_object* x_2702; uint8_t x_2703; 
lean_dec(x_25);
x_2702 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_2703 = lean_string_dec_eq(x_22, x_2702);
if (x_2703 == 0)
{
lean_object* x_2704; uint8_t x_2705; 
x_2704 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_2705 = lean_string_dec_eq(x_22, x_2704);
if (x_2705 == 0)
{
lean_object* x_2706; uint8_t x_2707; 
x_2706 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_2707 = lean_string_dec_eq(x_22, x_2706);
if (x_2707 == 0)
{
lean_object* x_2708; uint8_t x_2709; 
x_2708 = l_Lean_mkHole___closed__1;
x_2709 = lean_string_dec_eq(x_22, x_2708);
if (x_2709 == 0)
{
lean_object* x_2710; uint8_t x_2711; 
x_2710 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_2711 = lean_string_dec_eq(x_22, x_2710);
if (x_2711 == 0)
{
lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; uint8_t x_2715; lean_object* x_2716; 
if (lean_is_scalar(x_2446)) {
 x_2712 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_2712 = x_2446;
}
lean_ctor_set(x_2712, 0, x_19);
lean_ctor_set(x_2712, 1, x_2447);
lean_ctor_set_usize(x_2712, 2, x_2445);
x_2713 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_2713, 0, x_2712);
lean_ctor_set(x_2713, 1, x_2530);
lean_ctor_set_usize(x_2713, 2, x_2443);
lean_ctor_set(x_16, 1, x_2616);
lean_ctor_set(x_16, 0, x_2713);
x_2714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2714, 0, x_15);
lean_ctor_set(x_2714, 1, x_20);
x_2715 = 1;
lean_inc(x_2714);
x_2716 = l_Lean_Syntax_isTermId_x3f(x_2714, x_2715);
if (lean_obj_tag(x_2716) == 0)
{
lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; 
lean_dec(x_2714);
x_2717 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2718 = lean_ctor_get(x_2717, 0);
lean_inc(x_2718);
x_2719 = lean_ctor_get(x_2717, 1);
lean_inc(x_2719);
lean_dec(x_2717);
x_2720 = lean_unsigned_to_nat(1u);
x_2721 = lean_nat_add(x_3, x_2720);
lean_dec(x_3);
x_2722 = l_Lean_mkHole(x_14);
lean_inc(x_2718);
x_2723 = l_Lean_Elab_Term_mkExplicitBinder(x_2718, x_2722);
x_2724 = lean_array_push(x_4, x_2723);
lean_inc(x_5);
x_2725 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2721, x_2724, x_5, x_2719);
if (lean_obj_tag(x_2725) == 0)
{
lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_2775; 
x_2726 = lean_ctor_get(x_2725, 0);
lean_inc(x_2726);
x_2727 = lean_ctor_get(x_2726, 1);
lean_inc(x_2727);
x_2728 = lean_ctor_get(x_2725, 1);
lean_inc(x_2728);
lean_dec(x_2725);
x_2729 = lean_ctor_get(x_2726, 0);
lean_inc(x_2729);
if (lean_is_exclusive(x_2726)) {
 lean_ctor_release(x_2726, 0);
 lean_ctor_release(x_2726, 1);
 x_2730 = x_2726;
} else {
 lean_dec_ref(x_2726);
 x_2730 = lean_box(0);
}
x_2731 = lean_ctor_get(x_2727, 0);
lean_inc(x_2731);
if (lean_is_exclusive(x_2727)) {
 lean_ctor_release(x_2727, 0);
 lean_ctor_release(x_2727, 1);
 x_2732 = x_2727;
} else {
 lean_dec_ref(x_2727);
 x_2732 = lean_box(0);
}
x_2733 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2728);
lean_dec(x_5);
x_2734 = lean_ctor_get(x_2733, 1);
lean_inc(x_2734);
lean_dec(x_2733);
x_2735 = l_Lean_Elab_Term_getMainModule___rarg(x_2734);
x_2736 = lean_ctor_get(x_2735, 1);
lean_inc(x_2736);
if (lean_is_exclusive(x_2735)) {
 lean_ctor_release(x_2735, 0);
 lean_ctor_release(x_2735, 1);
 x_2737 = x_2735;
} else {
 lean_dec_ref(x_2735);
 x_2737 = lean_box(0);
}
x_2738 = l_Array_empty___closed__1;
x_2739 = lean_array_push(x_2738, x_2718);
x_2740 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2741 = lean_array_push(x_2739, x_2740);
x_2742 = l_Lean_mkTermIdFromIdent___closed__2;
x_2743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2743, 0, x_2742);
lean_ctor_set(x_2743, 1, x_2741);
x_2744 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2745 = lean_array_push(x_2744, x_2743);
x_2746 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2747, 0, x_2746);
lean_ctor_set(x_2747, 1, x_2745);
x_2748 = lean_array_push(x_2738, x_2747);
x_2749 = l_Lean_nullKind___closed__2;
x_2750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2750, 0, x_2749);
lean_ctor_set(x_2750, 1, x_2748);
x_2751 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2752 = lean_array_push(x_2751, x_2750);
x_2753 = lean_array_push(x_2752, x_2740);
x_2754 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2755 = lean_array_push(x_2753, x_2754);
x_2756 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2757 = lean_array_push(x_2755, x_2756);
lean_inc(x_14);
x_2758 = lean_array_push(x_2738, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2759 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2759 = lean_box(0);
}
if (lean_is_scalar(x_2759)) {
 x_2760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2760 = x_2759;
}
lean_ctor_set(x_2760, 0, x_2749);
lean_ctor_set(x_2760, 1, x_2758);
x_2761 = lean_array_push(x_2738, x_2760);
x_2762 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2763 = lean_array_push(x_2761, x_2762);
x_2764 = lean_array_push(x_2763, x_2731);
x_2765 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2766, 0, x_2765);
lean_ctor_set(x_2766, 1, x_2764);
x_2767 = lean_array_push(x_2738, x_2766);
x_2768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2768, 0, x_2749);
lean_ctor_set(x_2768, 1, x_2767);
x_2769 = lean_array_push(x_2757, x_2768);
x_2770 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2771, 0, x_2770);
lean_ctor_set(x_2771, 1, x_2769);
x_2772 = lean_box(x_2715);
if (lean_is_scalar(x_2732)) {
 x_2773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2773 = x_2732;
}
lean_ctor_set(x_2773, 0, x_2771);
lean_ctor_set(x_2773, 1, x_2772);
if (lean_is_scalar(x_2730)) {
 x_2774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2774 = x_2730;
}
lean_ctor_set(x_2774, 0, x_2729);
lean_ctor_set(x_2774, 1, x_2773);
if (lean_is_scalar(x_2737)) {
 x_2775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2775 = x_2737;
}
lean_ctor_set(x_2775, 0, x_2774);
lean_ctor_set(x_2775, 1, x_2736);
return x_2775;
}
else
{
lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; 
lean_dec(x_2718);
lean_dec(x_14);
lean_dec(x_5);
x_2776 = lean_ctor_get(x_2725, 0);
lean_inc(x_2776);
x_2777 = lean_ctor_get(x_2725, 1);
lean_inc(x_2777);
if (lean_is_exclusive(x_2725)) {
 lean_ctor_release(x_2725, 0);
 lean_ctor_release(x_2725, 1);
 x_2778 = x_2725;
} else {
 lean_dec_ref(x_2725);
 x_2778 = lean_box(0);
}
if (lean_is_scalar(x_2778)) {
 x_2779 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2779 = x_2778;
}
lean_ctor_set(x_2779, 0, x_2776);
lean_ctor_set(x_2779, 1, x_2777);
return x_2779;
}
}
else
{
lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; uint8_t x_2783; 
lean_dec(x_14);
x_2780 = lean_ctor_get(x_2716, 0);
lean_inc(x_2780);
lean_dec(x_2716);
x_2781 = lean_ctor_get(x_2780, 0);
lean_inc(x_2781);
x_2782 = lean_ctor_get(x_2780, 1);
lean_inc(x_2782);
lean_dec(x_2780);
x_2783 = l_Lean_Syntax_isNone(x_2782);
lean_dec(x_2782);
if (x_2783 == 0)
{
lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; 
lean_dec(x_2781);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2784 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_2785 = l_Lean_Elab_Term_throwErrorAt___rarg(x_2714, x_2784, x_5, x_6);
lean_dec(x_2714);
x_2786 = lean_ctor_get(x_2785, 0);
lean_inc(x_2786);
x_2787 = lean_ctor_get(x_2785, 1);
lean_inc(x_2787);
if (lean_is_exclusive(x_2785)) {
 lean_ctor_release(x_2785, 0);
 lean_ctor_release(x_2785, 1);
 x_2788 = x_2785;
} else {
 lean_dec_ref(x_2785);
 x_2788 = lean_box(0);
}
if (lean_is_scalar(x_2788)) {
 x_2789 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2789 = x_2788;
}
lean_ctor_set(x_2789, 0, x_2786);
lean_ctor_set(x_2789, 1, x_2787);
return x_2789;
}
else
{
lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; 
x_2790 = l_Lean_mkHole(x_2714);
lean_dec(x_2714);
x_2791 = lean_unsigned_to_nat(1u);
x_2792 = lean_nat_add(x_3, x_2791);
lean_dec(x_3);
x_2793 = l_Lean_Elab_Term_mkExplicitBinder(x_2781, x_2790);
x_2794 = lean_array_push(x_4, x_2793);
x_3 = x_2792;
x_4 = x_2794;
goto _start;
}
}
}
else
{
lean_object* x_2796; lean_object* x_2797; uint8_t x_2798; 
lean_dec(x_2446);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_2796 = lean_unsigned_to_nat(1u);
x_2797 = l_Lean_Syntax_getArg(x_14, x_2796);
x_2798 = l_Lean_Syntax_isNone(x_2797);
if (x_2798 == 0)
{
lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; uint8_t x_2802; 
x_2799 = lean_unsigned_to_nat(0u);
x_2800 = l_Lean_Syntax_getArg(x_2797, x_2799);
x_2801 = l_Lean_Syntax_getArg(x_2797, x_2796);
lean_dec(x_2797);
x_2802 = l_Lean_Syntax_isNone(x_2801);
if (x_2802 == 0)
{
lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; uint8_t x_2810; 
x_2803 = l_Lean_Syntax_getArg(x_2801, x_2799);
lean_dec(x_2801);
lean_inc(x_2803);
x_2804 = l_Lean_Syntax_getKind(x_2803);
x_2805 = lean_name_mk_string(x_19, x_2447);
x_2806 = lean_name_mk_string(x_2805, x_2530);
x_2807 = lean_name_mk_string(x_2806, x_2616);
x_2808 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_2809 = lean_name_mk_string(x_2807, x_2808);
x_2810 = lean_name_eq(x_2804, x_2809);
lean_dec(x_2809);
lean_dec(x_2804);
if (x_2810 == 0)
{
lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; 
lean_dec(x_2803);
lean_dec(x_2800);
x_2811 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2812 = lean_ctor_get(x_2811, 0);
lean_inc(x_2812);
x_2813 = lean_ctor_get(x_2811, 1);
lean_inc(x_2813);
lean_dec(x_2811);
x_2814 = lean_nat_add(x_3, x_2796);
lean_dec(x_3);
x_2815 = l_Lean_mkHole(x_14);
lean_inc(x_2812);
x_2816 = l_Lean_Elab_Term_mkExplicitBinder(x_2812, x_2815);
x_2817 = lean_array_push(x_4, x_2816);
lean_inc(x_5);
x_2818 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2814, x_2817, x_5, x_2813);
if (lean_obj_tag(x_2818) == 0)
{
lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; uint8_t x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; 
x_2819 = lean_ctor_get(x_2818, 0);
lean_inc(x_2819);
x_2820 = lean_ctor_get(x_2819, 1);
lean_inc(x_2820);
x_2821 = lean_ctor_get(x_2818, 1);
lean_inc(x_2821);
lean_dec(x_2818);
x_2822 = lean_ctor_get(x_2819, 0);
lean_inc(x_2822);
if (lean_is_exclusive(x_2819)) {
 lean_ctor_release(x_2819, 0);
 lean_ctor_release(x_2819, 1);
 x_2823 = x_2819;
} else {
 lean_dec_ref(x_2819);
 x_2823 = lean_box(0);
}
x_2824 = lean_ctor_get(x_2820, 0);
lean_inc(x_2824);
if (lean_is_exclusive(x_2820)) {
 lean_ctor_release(x_2820, 0);
 lean_ctor_release(x_2820, 1);
 x_2825 = x_2820;
} else {
 lean_dec_ref(x_2820);
 x_2825 = lean_box(0);
}
x_2826 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2821);
lean_dec(x_5);
x_2827 = lean_ctor_get(x_2826, 1);
lean_inc(x_2827);
lean_dec(x_2826);
x_2828 = l_Lean_Elab_Term_getMainModule___rarg(x_2827);
x_2829 = lean_ctor_get(x_2828, 1);
lean_inc(x_2829);
if (lean_is_exclusive(x_2828)) {
 lean_ctor_release(x_2828, 0);
 lean_ctor_release(x_2828, 1);
 x_2830 = x_2828;
} else {
 lean_dec_ref(x_2828);
 x_2830 = lean_box(0);
}
x_2831 = l_Array_empty___closed__1;
x_2832 = lean_array_push(x_2831, x_2812);
x_2833 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2834 = lean_array_push(x_2832, x_2833);
x_2835 = l_Lean_mkTermIdFromIdent___closed__2;
x_2836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2836, 0, x_2835);
lean_ctor_set(x_2836, 1, x_2834);
x_2837 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2838 = lean_array_push(x_2837, x_2836);
x_2839 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2840, 0, x_2839);
lean_ctor_set(x_2840, 1, x_2838);
x_2841 = lean_array_push(x_2831, x_2840);
x_2842 = l_Lean_nullKind___closed__2;
x_2843 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2843, 0, x_2842);
lean_ctor_set(x_2843, 1, x_2841);
x_2844 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2845 = lean_array_push(x_2844, x_2843);
x_2846 = lean_array_push(x_2845, x_2833);
x_2847 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2848 = lean_array_push(x_2846, x_2847);
x_2849 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2850 = lean_array_push(x_2848, x_2849);
lean_inc(x_14);
x_2851 = lean_array_push(x_2831, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2852 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2852 = lean_box(0);
}
if (lean_is_scalar(x_2852)) {
 x_2853 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2853 = x_2852;
}
lean_ctor_set(x_2853, 0, x_2842);
lean_ctor_set(x_2853, 1, x_2851);
x_2854 = lean_array_push(x_2831, x_2853);
x_2855 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2856 = lean_array_push(x_2854, x_2855);
x_2857 = lean_array_push(x_2856, x_2824);
x_2858 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2859, 0, x_2858);
lean_ctor_set(x_2859, 1, x_2857);
x_2860 = lean_array_push(x_2831, x_2859);
x_2861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2861, 0, x_2842);
lean_ctor_set(x_2861, 1, x_2860);
x_2862 = lean_array_push(x_2850, x_2861);
x_2863 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2864, 0, x_2863);
lean_ctor_set(x_2864, 1, x_2862);
x_2865 = 1;
x_2866 = lean_box(x_2865);
if (lean_is_scalar(x_2825)) {
 x_2867 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2867 = x_2825;
}
lean_ctor_set(x_2867, 0, x_2864);
lean_ctor_set(x_2867, 1, x_2866);
if (lean_is_scalar(x_2823)) {
 x_2868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2868 = x_2823;
}
lean_ctor_set(x_2868, 0, x_2822);
lean_ctor_set(x_2868, 1, x_2867);
if (lean_is_scalar(x_2830)) {
 x_2869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2869 = x_2830;
}
lean_ctor_set(x_2869, 0, x_2868);
lean_ctor_set(x_2869, 1, x_2829);
return x_2869;
}
else
{
lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; 
lean_dec(x_2812);
lean_dec(x_14);
lean_dec(x_5);
x_2870 = lean_ctor_get(x_2818, 0);
lean_inc(x_2870);
x_2871 = lean_ctor_get(x_2818, 1);
lean_inc(x_2871);
if (lean_is_exclusive(x_2818)) {
 lean_ctor_release(x_2818, 0);
 lean_ctor_release(x_2818, 1);
 x_2872 = x_2818;
} else {
 lean_dec_ref(x_2818);
 x_2872 = lean_box(0);
}
if (lean_is_scalar(x_2872)) {
 x_2873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2873 = x_2872;
}
lean_ctor_set(x_2873, 0, x_2870);
lean_ctor_set(x_2873, 1, x_2871);
return x_2873;
}
}
else
{
lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; 
x_2874 = l_Lean_Syntax_getArg(x_2803, x_2796);
lean_dec(x_2803);
x_2875 = l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(x_2800, x_5, x_6);
x_2876 = lean_ctor_get(x_2875, 0);
lean_inc(x_2876);
if (lean_obj_tag(x_2876) == 0)
{
lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; 
lean_dec(x_2874);
x_2877 = lean_ctor_get(x_2875, 1);
lean_inc(x_2877);
lean_dec(x_2875);
x_2878 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_2877);
x_2879 = lean_ctor_get(x_2878, 0);
lean_inc(x_2879);
x_2880 = lean_ctor_get(x_2878, 1);
lean_inc(x_2880);
lean_dec(x_2878);
x_2881 = lean_nat_add(x_3, x_2796);
lean_dec(x_3);
x_2882 = l_Lean_mkHole(x_14);
lean_inc(x_2879);
x_2883 = l_Lean_Elab_Term_mkExplicitBinder(x_2879, x_2882);
x_2884 = lean_array_push(x_4, x_2883);
lean_inc(x_5);
x_2885 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2881, x_2884, x_5, x_2880);
if (lean_obj_tag(x_2885) == 0)
{
lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; uint8_t x_2932; lean_object* x_2933; lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; 
x_2886 = lean_ctor_get(x_2885, 0);
lean_inc(x_2886);
x_2887 = lean_ctor_get(x_2886, 1);
lean_inc(x_2887);
x_2888 = lean_ctor_get(x_2885, 1);
lean_inc(x_2888);
lean_dec(x_2885);
x_2889 = lean_ctor_get(x_2886, 0);
lean_inc(x_2889);
if (lean_is_exclusive(x_2886)) {
 lean_ctor_release(x_2886, 0);
 lean_ctor_release(x_2886, 1);
 x_2890 = x_2886;
} else {
 lean_dec_ref(x_2886);
 x_2890 = lean_box(0);
}
x_2891 = lean_ctor_get(x_2887, 0);
lean_inc(x_2891);
if (lean_is_exclusive(x_2887)) {
 lean_ctor_release(x_2887, 0);
 lean_ctor_release(x_2887, 1);
 x_2892 = x_2887;
} else {
 lean_dec_ref(x_2887);
 x_2892 = lean_box(0);
}
x_2893 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2888);
lean_dec(x_5);
x_2894 = lean_ctor_get(x_2893, 1);
lean_inc(x_2894);
lean_dec(x_2893);
x_2895 = l_Lean_Elab_Term_getMainModule___rarg(x_2894);
x_2896 = lean_ctor_get(x_2895, 1);
lean_inc(x_2896);
if (lean_is_exclusive(x_2895)) {
 lean_ctor_release(x_2895, 0);
 lean_ctor_release(x_2895, 1);
 x_2897 = x_2895;
} else {
 lean_dec_ref(x_2895);
 x_2897 = lean_box(0);
}
x_2898 = l_Array_empty___closed__1;
x_2899 = lean_array_push(x_2898, x_2879);
x_2900 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2901 = lean_array_push(x_2899, x_2900);
x_2902 = l_Lean_mkTermIdFromIdent___closed__2;
x_2903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2903, 0, x_2902);
lean_ctor_set(x_2903, 1, x_2901);
x_2904 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2905 = lean_array_push(x_2904, x_2903);
x_2906 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2907 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2907, 0, x_2906);
lean_ctor_set(x_2907, 1, x_2905);
x_2908 = lean_array_push(x_2898, x_2907);
x_2909 = l_Lean_nullKind___closed__2;
x_2910 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2910, 0, x_2909);
lean_ctor_set(x_2910, 1, x_2908);
x_2911 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2912 = lean_array_push(x_2911, x_2910);
x_2913 = lean_array_push(x_2912, x_2900);
x_2914 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2915 = lean_array_push(x_2913, x_2914);
x_2916 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2917 = lean_array_push(x_2915, x_2916);
lean_inc(x_14);
x_2918 = lean_array_push(x_2898, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2919 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2919 = lean_box(0);
}
if (lean_is_scalar(x_2919)) {
 x_2920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2920 = x_2919;
}
lean_ctor_set(x_2920, 0, x_2909);
lean_ctor_set(x_2920, 1, x_2918);
x_2921 = lean_array_push(x_2898, x_2920);
x_2922 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2923 = lean_array_push(x_2921, x_2922);
x_2924 = lean_array_push(x_2923, x_2891);
x_2925 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2926 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2926, 0, x_2925);
lean_ctor_set(x_2926, 1, x_2924);
x_2927 = lean_array_push(x_2898, x_2926);
x_2928 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2928, 0, x_2909);
lean_ctor_set(x_2928, 1, x_2927);
x_2929 = lean_array_push(x_2917, x_2928);
x_2930 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_2931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2931, 0, x_2930);
lean_ctor_set(x_2931, 1, x_2929);
x_2932 = 1;
x_2933 = lean_box(x_2932);
if (lean_is_scalar(x_2892)) {
 x_2934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2934 = x_2892;
}
lean_ctor_set(x_2934, 0, x_2931);
lean_ctor_set(x_2934, 1, x_2933);
if (lean_is_scalar(x_2890)) {
 x_2935 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2935 = x_2890;
}
lean_ctor_set(x_2935, 0, x_2889);
lean_ctor_set(x_2935, 1, x_2934);
if (lean_is_scalar(x_2897)) {
 x_2936 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2936 = x_2897;
}
lean_ctor_set(x_2936, 0, x_2935);
lean_ctor_set(x_2936, 1, x_2896);
return x_2936;
}
else
{
lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; 
lean_dec(x_2879);
lean_dec(x_14);
lean_dec(x_5);
x_2937 = lean_ctor_get(x_2885, 0);
lean_inc(x_2937);
x_2938 = lean_ctor_get(x_2885, 1);
lean_inc(x_2938);
if (lean_is_exclusive(x_2885)) {
 lean_ctor_release(x_2885, 0);
 lean_ctor_release(x_2885, 1);
 x_2939 = x_2885;
} else {
 lean_dec_ref(x_2885);
 x_2939 = lean_box(0);
}
if (lean_is_scalar(x_2939)) {
 x_2940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2940 = x_2939;
}
lean_ctor_set(x_2940, 0, x_2937);
lean_ctor_set(x_2940, 1, x_2938);
return x_2940;
}
}
else
{
lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; 
lean_dec(x_14);
x_2941 = lean_ctor_get(x_2875, 1);
lean_inc(x_2941);
lean_dec(x_2875);
x_2942 = lean_ctor_get(x_2876, 0);
lean_inc(x_2942);
lean_dec(x_2876);
x_2943 = lean_nat_add(x_3, x_2796);
lean_dec(x_3);
x_2944 = x_2942;
x_2945 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(x_2874, x_2799, x_2944);
x_2946 = x_2945;
x_2947 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2946, x_2946, x_2799, x_4);
lean_dec(x_2946);
x_3 = x_2943;
x_4 = x_2947;
x_6 = x_2941;
goto _start;
}
}
}
else
{
lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; 
lean_dec(x_2801);
lean_dec(x_2800);
x_2949 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_2950 = lean_ctor_get(x_2949, 0);
lean_inc(x_2950);
x_2951 = lean_ctor_get(x_2949, 1);
lean_inc(x_2951);
lean_dec(x_2949);
x_2952 = lean_nat_add(x_3, x_2796);
lean_dec(x_3);
x_2953 = l_Lean_mkHole(x_14);
lean_inc(x_2950);
x_2954 = l_Lean_Elab_Term_mkExplicitBinder(x_2950, x_2953);
x_2955 = lean_array_push(x_4, x_2954);
lean_inc(x_5);
x_2956 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_2952, x_2955, x_5, x_2951);
if (lean_obj_tag(x_2956) == 0)
{
lean_object* x_2957; lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; uint8_t x_3003; lean_object* x_3004; lean_object* x_3005; lean_object* x_3006; lean_object* x_3007; 
x_2957 = lean_ctor_get(x_2956, 0);
lean_inc(x_2957);
x_2958 = lean_ctor_get(x_2957, 1);
lean_inc(x_2958);
x_2959 = lean_ctor_get(x_2956, 1);
lean_inc(x_2959);
lean_dec(x_2956);
x_2960 = lean_ctor_get(x_2957, 0);
lean_inc(x_2960);
if (lean_is_exclusive(x_2957)) {
 lean_ctor_release(x_2957, 0);
 lean_ctor_release(x_2957, 1);
 x_2961 = x_2957;
} else {
 lean_dec_ref(x_2957);
 x_2961 = lean_box(0);
}
x_2962 = lean_ctor_get(x_2958, 0);
lean_inc(x_2962);
if (lean_is_exclusive(x_2958)) {
 lean_ctor_release(x_2958, 0);
 lean_ctor_release(x_2958, 1);
 x_2963 = x_2958;
} else {
 lean_dec_ref(x_2958);
 x_2963 = lean_box(0);
}
x_2964 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_2959);
lean_dec(x_5);
x_2965 = lean_ctor_get(x_2964, 1);
lean_inc(x_2965);
lean_dec(x_2964);
x_2966 = l_Lean_Elab_Term_getMainModule___rarg(x_2965);
x_2967 = lean_ctor_get(x_2966, 1);
lean_inc(x_2967);
if (lean_is_exclusive(x_2966)) {
 lean_ctor_release(x_2966, 0);
 lean_ctor_release(x_2966, 1);
 x_2968 = x_2966;
} else {
 lean_dec_ref(x_2966);
 x_2968 = lean_box(0);
}
x_2969 = l_Array_empty___closed__1;
x_2970 = lean_array_push(x_2969, x_2950);
x_2971 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_2972 = lean_array_push(x_2970, x_2971);
x_2973 = l_Lean_mkTermIdFromIdent___closed__2;
x_2974 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2974, 0, x_2973);
lean_ctor_set(x_2974, 1, x_2972);
x_2975 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_2976 = lean_array_push(x_2975, x_2974);
x_2977 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_2978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2978, 0, x_2977);
lean_ctor_set(x_2978, 1, x_2976);
x_2979 = lean_array_push(x_2969, x_2978);
x_2980 = l_Lean_nullKind___closed__2;
x_2981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2981, 0, x_2980);
lean_ctor_set(x_2981, 1, x_2979);
x_2982 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_2983 = lean_array_push(x_2982, x_2981);
x_2984 = lean_array_push(x_2983, x_2971);
x_2985 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_2986 = lean_array_push(x_2984, x_2985);
x_2987 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_2988 = lean_array_push(x_2986, x_2987);
lean_inc(x_14);
x_2989 = lean_array_push(x_2969, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2990 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2990 = lean_box(0);
}
if (lean_is_scalar(x_2990)) {
 x_2991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2991 = x_2990;
}
lean_ctor_set(x_2991, 0, x_2980);
lean_ctor_set(x_2991, 1, x_2989);
x_2992 = lean_array_push(x_2969, x_2991);
x_2993 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_2994 = lean_array_push(x_2992, x_2993);
x_2995 = lean_array_push(x_2994, x_2962);
x_2996 = l_Lean_Parser_Term_matchAlt___closed__2;
x_2997 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2997, 0, x_2996);
lean_ctor_set(x_2997, 1, x_2995);
x_2998 = lean_array_push(x_2969, x_2997);
x_2999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2999, 0, x_2980);
lean_ctor_set(x_2999, 1, x_2998);
x_3000 = lean_array_push(x_2988, x_2999);
x_3001 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3002, 0, x_3001);
lean_ctor_set(x_3002, 1, x_3000);
x_3003 = 1;
x_3004 = lean_box(x_3003);
if (lean_is_scalar(x_2963)) {
 x_3005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3005 = x_2963;
}
lean_ctor_set(x_3005, 0, x_3002);
lean_ctor_set(x_3005, 1, x_3004);
if (lean_is_scalar(x_2961)) {
 x_3006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3006 = x_2961;
}
lean_ctor_set(x_3006, 0, x_2960);
lean_ctor_set(x_3006, 1, x_3005);
if (lean_is_scalar(x_2968)) {
 x_3007 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3007 = x_2968;
}
lean_ctor_set(x_3007, 0, x_3006);
lean_ctor_set(x_3007, 1, x_2967);
return x_3007;
}
else
{
lean_object* x_3008; lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; 
lean_dec(x_2950);
lean_dec(x_14);
lean_dec(x_5);
x_3008 = lean_ctor_get(x_2956, 0);
lean_inc(x_3008);
x_3009 = lean_ctor_get(x_2956, 1);
lean_inc(x_3009);
if (lean_is_exclusive(x_2956)) {
 lean_ctor_release(x_2956, 0);
 lean_ctor_release(x_2956, 1);
 x_3010 = x_2956;
} else {
 lean_dec_ref(x_2956);
 x_3010 = lean_box(0);
}
if (lean_is_scalar(x_3010)) {
 x_3011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3011 = x_3010;
}
lean_ctor_set(x_3011, 0, x_3008);
lean_ctor_set(x_3011, 1, x_3009);
return x_3011;
}
}
}
else
{
lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; 
lean_dec(x_2797);
x_3012 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3013 = lean_ctor_get(x_3012, 0);
lean_inc(x_3013);
x_3014 = lean_ctor_get(x_3012, 1);
lean_inc(x_3014);
lean_dec(x_3012);
x_3015 = lean_nat_add(x_3, x_2796);
lean_dec(x_3);
x_3016 = l_Lean_mkHole(x_14);
lean_inc(x_3013);
x_3017 = l_Lean_Elab_Term_mkExplicitBinder(x_3013, x_3016);
x_3018 = lean_array_push(x_4, x_3017);
lean_inc(x_5);
x_3019 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3015, x_3018, x_5, x_3014);
if (lean_obj_tag(x_3019) == 0)
{
lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; uint8_t x_3066; lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; lean_object* x_3070; 
x_3020 = lean_ctor_get(x_3019, 0);
lean_inc(x_3020);
x_3021 = lean_ctor_get(x_3020, 1);
lean_inc(x_3021);
x_3022 = lean_ctor_get(x_3019, 1);
lean_inc(x_3022);
lean_dec(x_3019);
x_3023 = lean_ctor_get(x_3020, 0);
lean_inc(x_3023);
if (lean_is_exclusive(x_3020)) {
 lean_ctor_release(x_3020, 0);
 lean_ctor_release(x_3020, 1);
 x_3024 = x_3020;
} else {
 lean_dec_ref(x_3020);
 x_3024 = lean_box(0);
}
x_3025 = lean_ctor_get(x_3021, 0);
lean_inc(x_3025);
if (lean_is_exclusive(x_3021)) {
 lean_ctor_release(x_3021, 0);
 lean_ctor_release(x_3021, 1);
 x_3026 = x_3021;
} else {
 lean_dec_ref(x_3021);
 x_3026 = lean_box(0);
}
x_3027 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3022);
lean_dec(x_5);
x_3028 = lean_ctor_get(x_3027, 1);
lean_inc(x_3028);
lean_dec(x_3027);
x_3029 = l_Lean_Elab_Term_getMainModule___rarg(x_3028);
x_3030 = lean_ctor_get(x_3029, 1);
lean_inc(x_3030);
if (lean_is_exclusive(x_3029)) {
 lean_ctor_release(x_3029, 0);
 lean_ctor_release(x_3029, 1);
 x_3031 = x_3029;
} else {
 lean_dec_ref(x_3029);
 x_3031 = lean_box(0);
}
x_3032 = l_Array_empty___closed__1;
x_3033 = lean_array_push(x_3032, x_3013);
x_3034 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3035 = lean_array_push(x_3033, x_3034);
x_3036 = l_Lean_mkTermIdFromIdent___closed__2;
x_3037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3037, 0, x_3036);
lean_ctor_set(x_3037, 1, x_3035);
x_3038 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3039 = lean_array_push(x_3038, x_3037);
x_3040 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3041 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3041, 0, x_3040);
lean_ctor_set(x_3041, 1, x_3039);
x_3042 = lean_array_push(x_3032, x_3041);
x_3043 = l_Lean_nullKind___closed__2;
x_3044 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3044, 0, x_3043);
lean_ctor_set(x_3044, 1, x_3042);
x_3045 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3046 = lean_array_push(x_3045, x_3044);
x_3047 = lean_array_push(x_3046, x_3034);
x_3048 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3049 = lean_array_push(x_3047, x_3048);
x_3050 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3051 = lean_array_push(x_3049, x_3050);
lean_inc(x_14);
x_3052 = lean_array_push(x_3032, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3053 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3053 = lean_box(0);
}
if (lean_is_scalar(x_3053)) {
 x_3054 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3054 = x_3053;
}
lean_ctor_set(x_3054, 0, x_3043);
lean_ctor_set(x_3054, 1, x_3052);
x_3055 = lean_array_push(x_3032, x_3054);
x_3056 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3057 = lean_array_push(x_3055, x_3056);
x_3058 = lean_array_push(x_3057, x_3025);
x_3059 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3060, 0, x_3059);
lean_ctor_set(x_3060, 1, x_3058);
x_3061 = lean_array_push(x_3032, x_3060);
x_3062 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3062, 0, x_3043);
lean_ctor_set(x_3062, 1, x_3061);
x_3063 = lean_array_push(x_3051, x_3062);
x_3064 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3065, 0, x_3064);
lean_ctor_set(x_3065, 1, x_3063);
x_3066 = 1;
x_3067 = lean_box(x_3066);
if (lean_is_scalar(x_3026)) {
 x_3068 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3068 = x_3026;
}
lean_ctor_set(x_3068, 0, x_3065);
lean_ctor_set(x_3068, 1, x_3067);
if (lean_is_scalar(x_3024)) {
 x_3069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3069 = x_3024;
}
lean_ctor_set(x_3069, 0, x_3023);
lean_ctor_set(x_3069, 1, x_3068);
if (lean_is_scalar(x_3031)) {
 x_3070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3070 = x_3031;
}
lean_ctor_set(x_3070, 0, x_3069);
lean_ctor_set(x_3070, 1, x_3030);
return x_3070;
}
else
{
lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; lean_object* x_3074; 
lean_dec(x_3013);
lean_dec(x_14);
lean_dec(x_5);
x_3071 = lean_ctor_get(x_3019, 0);
lean_inc(x_3071);
x_3072 = lean_ctor_get(x_3019, 1);
lean_inc(x_3072);
if (lean_is_exclusive(x_3019)) {
 lean_ctor_release(x_3019, 0);
 lean_ctor_release(x_3019, 1);
 x_3073 = x_3019;
} else {
 lean_dec_ref(x_3019);
 x_3073 = lean_box(0);
}
if (lean_is_scalar(x_3073)) {
 x_3074 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3074 = x_3073;
}
lean_ctor_set(x_3074, 0, x_3071);
lean_ctor_set(x_3074, 1, x_3072);
return x_3074;
}
}
}
}
else
{
lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; 
lean_dec(x_2446);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3075 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3076 = lean_ctor_get(x_3075, 0);
lean_inc(x_3076);
x_3077 = lean_ctor_get(x_3075, 1);
lean_inc(x_3077);
lean_dec(x_3075);
x_3078 = lean_unsigned_to_nat(1u);
x_3079 = lean_nat_add(x_3, x_3078);
lean_dec(x_3);
x_3080 = l_Lean_Elab_Term_mkExplicitBinder(x_3076, x_14);
x_3081 = lean_array_push(x_4, x_3080);
x_3 = x_3079;
x_4 = x_3081;
x_6 = x_3077;
goto _start;
}
}
else
{
lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; 
lean_dec(x_2446);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3083 = lean_unsigned_to_nat(1u);
x_3084 = lean_nat_add(x_3, x_3083);
lean_dec(x_3);
x_3085 = lean_array_push(x_4, x_14);
x_3 = x_3084;
x_4 = x_3085;
goto _start;
}
}
else
{
lean_object* x_3087; lean_object* x_3088; lean_object* x_3089; 
lean_dec(x_2446);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3087 = lean_unsigned_to_nat(1u);
x_3088 = lean_nat_add(x_3, x_3087);
lean_dec(x_3);
x_3089 = lean_array_push(x_4, x_14);
x_3 = x_3088;
x_4 = x_3089;
goto _start;
}
}
else
{
lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; 
lean_dec(x_2446);
lean_free_object(x_16);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3091 = lean_unsigned_to_nat(1u);
x_3092 = lean_nat_add(x_3, x_3091);
lean_dec(x_3);
x_3093 = lean_array_push(x_4, x_14);
x_3 = x_3092;
x_4 = x_3093;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_3095; size_t x_3096; lean_object* x_3097; size_t x_3098; lean_object* x_3099; lean_object* x_3100; size_t x_3101; lean_object* x_3102; lean_object* x_3103; uint8_t x_3104; 
x_3095 = lean_ctor_get(x_16, 1);
x_3096 = lean_ctor_get_usize(x_16, 2);
lean_inc(x_3095);
lean_dec(x_16);
x_3097 = lean_ctor_get(x_17, 1);
lean_inc(x_3097);
x_3098 = lean_ctor_get_usize(x_17, 2);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_3099 = x_17;
} else {
 lean_dec_ref(x_17);
 x_3099 = lean_box(0);
}
x_3100 = lean_ctor_get(x_18, 1);
lean_inc(x_3100);
x_3101 = lean_ctor_get_usize(x_18, 2);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_3102 = x_18;
} else {
 lean_dec_ref(x_18);
 x_3102 = lean_box(0);
}
x_3103 = l_Lean_mkAppStx___closed__1;
x_3104 = lean_string_dec_eq(x_3100, x_3103);
lean_dec(x_3100);
if (x_3104 == 0)
{
uint8_t x_3105; lean_object* x_3106; 
lean_dec(x_3102);
lean_dec(x_3099);
lean_dec(x_3097);
lean_dec(x_3095);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3105 = 1;
lean_inc(x_14);
x_3106 = l_Lean_Syntax_isTermId_x3f(x_14, x_3105);
if (lean_obj_tag(x_3106) == 0)
{
lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; 
x_3107 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3108 = lean_ctor_get(x_3107, 0);
lean_inc(x_3108);
x_3109 = lean_ctor_get(x_3107, 1);
lean_inc(x_3109);
lean_dec(x_3107);
x_3110 = lean_unsigned_to_nat(1u);
x_3111 = lean_nat_add(x_3, x_3110);
lean_dec(x_3);
x_3112 = l_Lean_mkHole(x_14);
lean_inc(x_3108);
x_3113 = l_Lean_Elab_Term_mkExplicitBinder(x_3108, x_3112);
x_3114 = lean_array_push(x_4, x_3113);
lean_inc(x_5);
x_3115 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3111, x_3114, x_5, x_3109);
if (lean_obj_tag(x_3115) == 0)
{
lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; 
x_3116 = lean_ctor_get(x_3115, 0);
lean_inc(x_3116);
x_3117 = lean_ctor_get(x_3116, 1);
lean_inc(x_3117);
x_3118 = lean_ctor_get(x_3115, 1);
lean_inc(x_3118);
lean_dec(x_3115);
x_3119 = lean_ctor_get(x_3116, 0);
lean_inc(x_3119);
if (lean_is_exclusive(x_3116)) {
 lean_ctor_release(x_3116, 0);
 lean_ctor_release(x_3116, 1);
 x_3120 = x_3116;
} else {
 lean_dec_ref(x_3116);
 x_3120 = lean_box(0);
}
x_3121 = lean_ctor_get(x_3117, 0);
lean_inc(x_3121);
if (lean_is_exclusive(x_3117)) {
 lean_ctor_release(x_3117, 0);
 lean_ctor_release(x_3117, 1);
 x_3122 = x_3117;
} else {
 lean_dec_ref(x_3117);
 x_3122 = lean_box(0);
}
x_3123 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3118);
lean_dec(x_5);
x_3124 = lean_ctor_get(x_3123, 1);
lean_inc(x_3124);
lean_dec(x_3123);
x_3125 = l_Lean_Elab_Term_getMainModule___rarg(x_3124);
x_3126 = lean_ctor_get(x_3125, 1);
lean_inc(x_3126);
if (lean_is_exclusive(x_3125)) {
 lean_ctor_release(x_3125, 0);
 lean_ctor_release(x_3125, 1);
 x_3127 = x_3125;
} else {
 lean_dec_ref(x_3125);
 x_3127 = lean_box(0);
}
x_3128 = l_Array_empty___closed__1;
x_3129 = lean_array_push(x_3128, x_3108);
x_3130 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3131 = lean_array_push(x_3129, x_3130);
x_3132 = l_Lean_mkTermIdFromIdent___closed__2;
x_3133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3133, 0, x_3132);
lean_ctor_set(x_3133, 1, x_3131);
x_3134 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3135 = lean_array_push(x_3134, x_3133);
x_3136 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3137, 0, x_3136);
lean_ctor_set(x_3137, 1, x_3135);
x_3138 = lean_array_push(x_3128, x_3137);
x_3139 = l_Lean_nullKind___closed__2;
x_3140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3140, 0, x_3139);
lean_ctor_set(x_3140, 1, x_3138);
x_3141 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3142 = lean_array_push(x_3141, x_3140);
x_3143 = lean_array_push(x_3142, x_3130);
x_3144 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3145 = lean_array_push(x_3143, x_3144);
x_3146 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3147 = lean_array_push(x_3145, x_3146);
lean_inc(x_14);
x_3148 = lean_array_push(x_3128, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3149 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3149 = lean_box(0);
}
if (lean_is_scalar(x_3149)) {
 x_3150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3150 = x_3149;
}
lean_ctor_set(x_3150, 0, x_3139);
lean_ctor_set(x_3150, 1, x_3148);
x_3151 = lean_array_push(x_3128, x_3150);
x_3152 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3153 = lean_array_push(x_3151, x_3152);
x_3154 = lean_array_push(x_3153, x_3121);
x_3155 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3156, 0, x_3155);
lean_ctor_set(x_3156, 1, x_3154);
x_3157 = lean_array_push(x_3128, x_3156);
x_3158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3158, 0, x_3139);
lean_ctor_set(x_3158, 1, x_3157);
x_3159 = lean_array_push(x_3147, x_3158);
x_3160 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3161, 0, x_3160);
lean_ctor_set(x_3161, 1, x_3159);
x_3162 = lean_box(x_3105);
if (lean_is_scalar(x_3122)) {
 x_3163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3163 = x_3122;
}
lean_ctor_set(x_3163, 0, x_3161);
lean_ctor_set(x_3163, 1, x_3162);
if (lean_is_scalar(x_3120)) {
 x_3164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3164 = x_3120;
}
lean_ctor_set(x_3164, 0, x_3119);
lean_ctor_set(x_3164, 1, x_3163);
if (lean_is_scalar(x_3127)) {
 x_3165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3165 = x_3127;
}
lean_ctor_set(x_3165, 0, x_3164);
lean_ctor_set(x_3165, 1, x_3126);
return x_3165;
}
else
{
lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; 
lean_dec(x_3108);
lean_dec(x_14);
lean_dec(x_5);
x_3166 = lean_ctor_get(x_3115, 0);
lean_inc(x_3166);
x_3167 = lean_ctor_get(x_3115, 1);
lean_inc(x_3167);
if (lean_is_exclusive(x_3115)) {
 lean_ctor_release(x_3115, 0);
 lean_ctor_release(x_3115, 1);
 x_3168 = x_3115;
} else {
 lean_dec_ref(x_3115);
 x_3168 = lean_box(0);
}
if (lean_is_scalar(x_3168)) {
 x_3169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3169 = x_3168;
}
lean_ctor_set(x_3169, 0, x_3166);
lean_ctor_set(x_3169, 1, x_3167);
return x_3169;
}
}
else
{
lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; uint8_t x_3173; 
x_3170 = lean_ctor_get(x_3106, 0);
lean_inc(x_3170);
lean_dec(x_3106);
x_3171 = lean_ctor_get(x_3170, 0);
lean_inc(x_3171);
x_3172 = lean_ctor_get(x_3170, 1);
lean_inc(x_3172);
lean_dec(x_3170);
x_3173 = l_Lean_Syntax_isNone(x_3172);
lean_dec(x_3172);
if (x_3173 == 0)
{
lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; 
lean_dec(x_3171);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3174 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_3175 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_3174, x_5, x_6);
lean_dec(x_14);
x_3176 = lean_ctor_get(x_3175, 0);
lean_inc(x_3176);
x_3177 = lean_ctor_get(x_3175, 1);
lean_inc(x_3177);
if (lean_is_exclusive(x_3175)) {
 lean_ctor_release(x_3175, 0);
 lean_ctor_release(x_3175, 1);
 x_3178 = x_3175;
} else {
 lean_dec_ref(x_3175);
 x_3178 = lean_box(0);
}
if (lean_is_scalar(x_3178)) {
 x_3179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3179 = x_3178;
}
lean_ctor_set(x_3179, 0, x_3176);
lean_ctor_set(x_3179, 1, x_3177);
return x_3179;
}
else
{
lean_object* x_3180; lean_object* x_3181; lean_object* x_3182; lean_object* x_3183; lean_object* x_3184; 
x_3180 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_3181 = lean_unsigned_to_nat(1u);
x_3182 = lean_nat_add(x_3, x_3181);
lean_dec(x_3);
x_3183 = l_Lean_Elab_Term_mkExplicitBinder(x_3171, x_3180);
x_3184 = lean_array_push(x_4, x_3183);
x_3 = x_3182;
x_4 = x_3184;
goto _start;
}
}
}
else
{
lean_object* x_3186; uint8_t x_3187; 
x_3186 = l_Lean_mkAppStx___closed__3;
x_3187 = lean_string_dec_eq(x_3097, x_3186);
if (x_3187 == 0)
{
lean_object* x_3188; lean_object* x_3189; lean_object* x_3190; lean_object* x_3191; uint8_t x_3192; lean_object* x_3193; 
if (lean_is_scalar(x_3102)) {
 x_3188 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3188 = x_3102;
}
lean_ctor_set(x_3188, 0, x_19);
lean_ctor_set(x_3188, 1, x_3103);
lean_ctor_set_usize(x_3188, 2, x_3101);
if (lean_is_scalar(x_3099)) {
 x_3189 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3189 = x_3099;
}
lean_ctor_set(x_3189, 0, x_3188);
lean_ctor_set(x_3189, 1, x_3097);
lean_ctor_set_usize(x_3189, 2, x_3098);
x_3190 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3190, 0, x_3189);
lean_ctor_set(x_3190, 1, x_3095);
lean_ctor_set_usize(x_3190, 2, x_3096);
lean_ctor_set(x_15, 0, x_3190);
x_3191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3191, 0, x_15);
lean_ctor_set(x_3191, 1, x_20);
x_3192 = 1;
lean_inc(x_3191);
x_3193 = l_Lean_Syntax_isTermId_x3f(x_3191, x_3192);
if (lean_obj_tag(x_3193) == 0)
{
lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; 
lean_dec(x_3191);
x_3194 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3195 = lean_ctor_get(x_3194, 0);
lean_inc(x_3195);
x_3196 = lean_ctor_get(x_3194, 1);
lean_inc(x_3196);
lean_dec(x_3194);
x_3197 = lean_unsigned_to_nat(1u);
x_3198 = lean_nat_add(x_3, x_3197);
lean_dec(x_3);
x_3199 = l_Lean_mkHole(x_14);
lean_inc(x_3195);
x_3200 = l_Lean_Elab_Term_mkExplicitBinder(x_3195, x_3199);
x_3201 = lean_array_push(x_4, x_3200);
lean_inc(x_5);
x_3202 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3198, x_3201, x_5, x_3196);
if (lean_obj_tag(x_3202) == 0)
{
lean_object* x_3203; lean_object* x_3204; lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; lean_object* x_3229; lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; lean_object* x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; lean_object* x_3250; lean_object* x_3251; lean_object* x_3252; 
x_3203 = lean_ctor_get(x_3202, 0);
lean_inc(x_3203);
x_3204 = lean_ctor_get(x_3203, 1);
lean_inc(x_3204);
x_3205 = lean_ctor_get(x_3202, 1);
lean_inc(x_3205);
lean_dec(x_3202);
x_3206 = lean_ctor_get(x_3203, 0);
lean_inc(x_3206);
if (lean_is_exclusive(x_3203)) {
 lean_ctor_release(x_3203, 0);
 lean_ctor_release(x_3203, 1);
 x_3207 = x_3203;
} else {
 lean_dec_ref(x_3203);
 x_3207 = lean_box(0);
}
x_3208 = lean_ctor_get(x_3204, 0);
lean_inc(x_3208);
if (lean_is_exclusive(x_3204)) {
 lean_ctor_release(x_3204, 0);
 lean_ctor_release(x_3204, 1);
 x_3209 = x_3204;
} else {
 lean_dec_ref(x_3204);
 x_3209 = lean_box(0);
}
x_3210 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3205);
lean_dec(x_5);
x_3211 = lean_ctor_get(x_3210, 1);
lean_inc(x_3211);
lean_dec(x_3210);
x_3212 = l_Lean_Elab_Term_getMainModule___rarg(x_3211);
x_3213 = lean_ctor_get(x_3212, 1);
lean_inc(x_3213);
if (lean_is_exclusive(x_3212)) {
 lean_ctor_release(x_3212, 0);
 lean_ctor_release(x_3212, 1);
 x_3214 = x_3212;
} else {
 lean_dec_ref(x_3212);
 x_3214 = lean_box(0);
}
x_3215 = l_Array_empty___closed__1;
x_3216 = lean_array_push(x_3215, x_3195);
x_3217 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3218 = lean_array_push(x_3216, x_3217);
x_3219 = l_Lean_mkTermIdFromIdent___closed__2;
x_3220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3220, 0, x_3219);
lean_ctor_set(x_3220, 1, x_3218);
x_3221 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3222 = lean_array_push(x_3221, x_3220);
x_3223 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3224, 0, x_3223);
lean_ctor_set(x_3224, 1, x_3222);
x_3225 = lean_array_push(x_3215, x_3224);
x_3226 = l_Lean_nullKind___closed__2;
x_3227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3227, 0, x_3226);
lean_ctor_set(x_3227, 1, x_3225);
x_3228 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3229 = lean_array_push(x_3228, x_3227);
x_3230 = lean_array_push(x_3229, x_3217);
x_3231 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3232 = lean_array_push(x_3230, x_3231);
x_3233 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3234 = lean_array_push(x_3232, x_3233);
lean_inc(x_14);
x_3235 = lean_array_push(x_3215, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3236 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3236 = lean_box(0);
}
if (lean_is_scalar(x_3236)) {
 x_3237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3237 = x_3236;
}
lean_ctor_set(x_3237, 0, x_3226);
lean_ctor_set(x_3237, 1, x_3235);
x_3238 = lean_array_push(x_3215, x_3237);
x_3239 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3240 = lean_array_push(x_3238, x_3239);
x_3241 = lean_array_push(x_3240, x_3208);
x_3242 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3243, 0, x_3242);
lean_ctor_set(x_3243, 1, x_3241);
x_3244 = lean_array_push(x_3215, x_3243);
x_3245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3245, 0, x_3226);
lean_ctor_set(x_3245, 1, x_3244);
x_3246 = lean_array_push(x_3234, x_3245);
x_3247 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3248, 0, x_3247);
lean_ctor_set(x_3248, 1, x_3246);
x_3249 = lean_box(x_3192);
if (lean_is_scalar(x_3209)) {
 x_3250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3250 = x_3209;
}
lean_ctor_set(x_3250, 0, x_3248);
lean_ctor_set(x_3250, 1, x_3249);
if (lean_is_scalar(x_3207)) {
 x_3251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3251 = x_3207;
}
lean_ctor_set(x_3251, 0, x_3206);
lean_ctor_set(x_3251, 1, x_3250);
if (lean_is_scalar(x_3214)) {
 x_3252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3252 = x_3214;
}
lean_ctor_set(x_3252, 0, x_3251);
lean_ctor_set(x_3252, 1, x_3213);
return x_3252;
}
else
{
lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; lean_object* x_3256; 
lean_dec(x_3195);
lean_dec(x_14);
lean_dec(x_5);
x_3253 = lean_ctor_get(x_3202, 0);
lean_inc(x_3253);
x_3254 = lean_ctor_get(x_3202, 1);
lean_inc(x_3254);
if (lean_is_exclusive(x_3202)) {
 lean_ctor_release(x_3202, 0);
 lean_ctor_release(x_3202, 1);
 x_3255 = x_3202;
} else {
 lean_dec_ref(x_3202);
 x_3255 = lean_box(0);
}
if (lean_is_scalar(x_3255)) {
 x_3256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3256 = x_3255;
}
lean_ctor_set(x_3256, 0, x_3253);
lean_ctor_set(x_3256, 1, x_3254);
return x_3256;
}
}
else
{
lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; uint8_t x_3260; 
lean_dec(x_14);
x_3257 = lean_ctor_get(x_3193, 0);
lean_inc(x_3257);
lean_dec(x_3193);
x_3258 = lean_ctor_get(x_3257, 0);
lean_inc(x_3258);
x_3259 = lean_ctor_get(x_3257, 1);
lean_inc(x_3259);
lean_dec(x_3257);
x_3260 = l_Lean_Syntax_isNone(x_3259);
lean_dec(x_3259);
if (x_3260 == 0)
{
lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; 
lean_dec(x_3258);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3261 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_3262 = l_Lean_Elab_Term_throwErrorAt___rarg(x_3191, x_3261, x_5, x_6);
lean_dec(x_3191);
x_3263 = lean_ctor_get(x_3262, 0);
lean_inc(x_3263);
x_3264 = lean_ctor_get(x_3262, 1);
lean_inc(x_3264);
if (lean_is_exclusive(x_3262)) {
 lean_ctor_release(x_3262, 0);
 lean_ctor_release(x_3262, 1);
 x_3265 = x_3262;
} else {
 lean_dec_ref(x_3262);
 x_3265 = lean_box(0);
}
if (lean_is_scalar(x_3265)) {
 x_3266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3266 = x_3265;
}
lean_ctor_set(x_3266, 0, x_3263);
lean_ctor_set(x_3266, 1, x_3264);
return x_3266;
}
else
{
lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; 
x_3267 = l_Lean_mkHole(x_3191);
lean_dec(x_3191);
x_3268 = lean_unsigned_to_nat(1u);
x_3269 = lean_nat_add(x_3, x_3268);
lean_dec(x_3);
x_3270 = l_Lean_Elab_Term_mkExplicitBinder(x_3258, x_3267);
x_3271 = lean_array_push(x_4, x_3270);
x_3 = x_3269;
x_4 = x_3271;
goto _start;
}
}
}
else
{
lean_object* x_3273; uint8_t x_3274; 
lean_dec(x_3097);
x_3273 = l_Lean_mkAppStx___closed__5;
x_3274 = lean_string_dec_eq(x_3095, x_3273);
if (x_3274 == 0)
{
lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; uint8_t x_3279; lean_object* x_3280; 
if (lean_is_scalar(x_3102)) {
 x_3275 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3275 = x_3102;
}
lean_ctor_set(x_3275, 0, x_19);
lean_ctor_set(x_3275, 1, x_3103);
lean_ctor_set_usize(x_3275, 2, x_3101);
if (lean_is_scalar(x_3099)) {
 x_3276 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3276 = x_3099;
}
lean_ctor_set(x_3276, 0, x_3275);
lean_ctor_set(x_3276, 1, x_3186);
lean_ctor_set_usize(x_3276, 2, x_3098);
x_3277 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3277, 0, x_3276);
lean_ctor_set(x_3277, 1, x_3095);
lean_ctor_set_usize(x_3277, 2, x_3096);
lean_ctor_set(x_15, 0, x_3277);
x_3278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3278, 0, x_15);
lean_ctor_set(x_3278, 1, x_20);
x_3279 = 1;
lean_inc(x_3278);
x_3280 = l_Lean_Syntax_isTermId_x3f(x_3278, x_3279);
if (lean_obj_tag(x_3280) == 0)
{
lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; 
lean_dec(x_3278);
x_3281 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3282 = lean_ctor_get(x_3281, 0);
lean_inc(x_3282);
x_3283 = lean_ctor_get(x_3281, 1);
lean_inc(x_3283);
lean_dec(x_3281);
x_3284 = lean_unsigned_to_nat(1u);
x_3285 = lean_nat_add(x_3, x_3284);
lean_dec(x_3);
x_3286 = l_Lean_mkHole(x_14);
lean_inc(x_3282);
x_3287 = l_Lean_Elab_Term_mkExplicitBinder(x_3282, x_3286);
x_3288 = lean_array_push(x_4, x_3287);
lean_inc(x_5);
x_3289 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3285, x_3288, x_5, x_3283);
if (lean_obj_tag(x_3289) == 0)
{
lean_object* x_3290; lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; lean_object* x_3306; lean_object* x_3307; lean_object* x_3308; lean_object* x_3309; lean_object* x_3310; lean_object* x_3311; lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; lean_object* x_3315; lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; 
x_3290 = lean_ctor_get(x_3289, 0);
lean_inc(x_3290);
x_3291 = lean_ctor_get(x_3290, 1);
lean_inc(x_3291);
x_3292 = lean_ctor_get(x_3289, 1);
lean_inc(x_3292);
lean_dec(x_3289);
x_3293 = lean_ctor_get(x_3290, 0);
lean_inc(x_3293);
if (lean_is_exclusive(x_3290)) {
 lean_ctor_release(x_3290, 0);
 lean_ctor_release(x_3290, 1);
 x_3294 = x_3290;
} else {
 lean_dec_ref(x_3290);
 x_3294 = lean_box(0);
}
x_3295 = lean_ctor_get(x_3291, 0);
lean_inc(x_3295);
if (lean_is_exclusive(x_3291)) {
 lean_ctor_release(x_3291, 0);
 lean_ctor_release(x_3291, 1);
 x_3296 = x_3291;
} else {
 lean_dec_ref(x_3291);
 x_3296 = lean_box(0);
}
x_3297 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3292);
lean_dec(x_5);
x_3298 = lean_ctor_get(x_3297, 1);
lean_inc(x_3298);
lean_dec(x_3297);
x_3299 = l_Lean_Elab_Term_getMainModule___rarg(x_3298);
x_3300 = lean_ctor_get(x_3299, 1);
lean_inc(x_3300);
if (lean_is_exclusive(x_3299)) {
 lean_ctor_release(x_3299, 0);
 lean_ctor_release(x_3299, 1);
 x_3301 = x_3299;
} else {
 lean_dec_ref(x_3299);
 x_3301 = lean_box(0);
}
x_3302 = l_Array_empty___closed__1;
x_3303 = lean_array_push(x_3302, x_3282);
x_3304 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3305 = lean_array_push(x_3303, x_3304);
x_3306 = l_Lean_mkTermIdFromIdent___closed__2;
x_3307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3307, 0, x_3306);
lean_ctor_set(x_3307, 1, x_3305);
x_3308 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3309 = lean_array_push(x_3308, x_3307);
x_3310 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3311, 0, x_3310);
lean_ctor_set(x_3311, 1, x_3309);
x_3312 = lean_array_push(x_3302, x_3311);
x_3313 = l_Lean_nullKind___closed__2;
x_3314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3314, 0, x_3313);
lean_ctor_set(x_3314, 1, x_3312);
x_3315 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3316 = lean_array_push(x_3315, x_3314);
x_3317 = lean_array_push(x_3316, x_3304);
x_3318 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3319 = lean_array_push(x_3317, x_3318);
x_3320 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3321 = lean_array_push(x_3319, x_3320);
lean_inc(x_14);
x_3322 = lean_array_push(x_3302, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3323 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3323 = lean_box(0);
}
if (lean_is_scalar(x_3323)) {
 x_3324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3324 = x_3323;
}
lean_ctor_set(x_3324, 0, x_3313);
lean_ctor_set(x_3324, 1, x_3322);
x_3325 = lean_array_push(x_3302, x_3324);
x_3326 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3327 = lean_array_push(x_3325, x_3326);
x_3328 = lean_array_push(x_3327, x_3295);
x_3329 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3330, 0, x_3329);
lean_ctor_set(x_3330, 1, x_3328);
x_3331 = lean_array_push(x_3302, x_3330);
x_3332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3332, 0, x_3313);
lean_ctor_set(x_3332, 1, x_3331);
x_3333 = lean_array_push(x_3321, x_3332);
x_3334 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3335, 0, x_3334);
lean_ctor_set(x_3335, 1, x_3333);
x_3336 = lean_box(x_3279);
if (lean_is_scalar(x_3296)) {
 x_3337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3337 = x_3296;
}
lean_ctor_set(x_3337, 0, x_3335);
lean_ctor_set(x_3337, 1, x_3336);
if (lean_is_scalar(x_3294)) {
 x_3338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3338 = x_3294;
}
lean_ctor_set(x_3338, 0, x_3293);
lean_ctor_set(x_3338, 1, x_3337);
if (lean_is_scalar(x_3301)) {
 x_3339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3339 = x_3301;
}
lean_ctor_set(x_3339, 0, x_3338);
lean_ctor_set(x_3339, 1, x_3300);
return x_3339;
}
else
{
lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; 
lean_dec(x_3282);
lean_dec(x_14);
lean_dec(x_5);
x_3340 = lean_ctor_get(x_3289, 0);
lean_inc(x_3340);
x_3341 = lean_ctor_get(x_3289, 1);
lean_inc(x_3341);
if (lean_is_exclusive(x_3289)) {
 lean_ctor_release(x_3289, 0);
 lean_ctor_release(x_3289, 1);
 x_3342 = x_3289;
} else {
 lean_dec_ref(x_3289);
 x_3342 = lean_box(0);
}
if (lean_is_scalar(x_3342)) {
 x_3343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3343 = x_3342;
}
lean_ctor_set(x_3343, 0, x_3340);
lean_ctor_set(x_3343, 1, x_3341);
return x_3343;
}
}
else
{
lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; uint8_t x_3347; 
lean_dec(x_14);
x_3344 = lean_ctor_get(x_3280, 0);
lean_inc(x_3344);
lean_dec(x_3280);
x_3345 = lean_ctor_get(x_3344, 0);
lean_inc(x_3345);
x_3346 = lean_ctor_get(x_3344, 1);
lean_inc(x_3346);
lean_dec(x_3344);
x_3347 = l_Lean_Syntax_isNone(x_3346);
lean_dec(x_3346);
if (x_3347 == 0)
{
lean_object* x_3348; lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; 
lean_dec(x_3345);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3348 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_3349 = l_Lean_Elab_Term_throwErrorAt___rarg(x_3278, x_3348, x_5, x_6);
lean_dec(x_3278);
x_3350 = lean_ctor_get(x_3349, 0);
lean_inc(x_3350);
x_3351 = lean_ctor_get(x_3349, 1);
lean_inc(x_3351);
if (lean_is_exclusive(x_3349)) {
 lean_ctor_release(x_3349, 0);
 lean_ctor_release(x_3349, 1);
 x_3352 = x_3349;
} else {
 lean_dec_ref(x_3349);
 x_3352 = lean_box(0);
}
if (lean_is_scalar(x_3352)) {
 x_3353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3353 = x_3352;
}
lean_ctor_set(x_3353, 0, x_3350);
lean_ctor_set(x_3353, 1, x_3351);
return x_3353;
}
else
{
lean_object* x_3354; lean_object* x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; 
x_3354 = l_Lean_mkHole(x_3278);
lean_dec(x_3278);
x_3355 = lean_unsigned_to_nat(1u);
x_3356 = lean_nat_add(x_3, x_3355);
lean_dec(x_3);
x_3357 = l_Lean_Elab_Term_mkExplicitBinder(x_3345, x_3354);
x_3358 = lean_array_push(x_4, x_3357);
x_3 = x_3356;
x_4 = x_3358;
goto _start;
}
}
}
else
{
lean_object* x_3360; uint8_t x_3361; 
lean_dec(x_3095);
x_3360 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_3361 = lean_string_dec_eq(x_22, x_3360);
if (x_3361 == 0)
{
lean_object* x_3362; uint8_t x_3363; 
x_3362 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_3363 = lean_string_dec_eq(x_22, x_3362);
if (x_3363 == 0)
{
lean_object* x_3364; uint8_t x_3365; 
x_3364 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_3365 = lean_string_dec_eq(x_22, x_3364);
if (x_3365 == 0)
{
lean_object* x_3366; uint8_t x_3367; 
x_3366 = l_Lean_mkHole___closed__1;
x_3367 = lean_string_dec_eq(x_22, x_3366);
if (x_3367 == 0)
{
lean_object* x_3368; uint8_t x_3369; 
x_3368 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_3369 = lean_string_dec_eq(x_22, x_3368);
if (x_3369 == 0)
{
lean_object* x_3370; lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; uint8_t x_3374; lean_object* x_3375; 
if (lean_is_scalar(x_3102)) {
 x_3370 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3370 = x_3102;
}
lean_ctor_set(x_3370, 0, x_19);
lean_ctor_set(x_3370, 1, x_3103);
lean_ctor_set_usize(x_3370, 2, x_3101);
if (lean_is_scalar(x_3099)) {
 x_3371 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3371 = x_3099;
}
lean_ctor_set(x_3371, 0, x_3370);
lean_ctor_set(x_3371, 1, x_3186);
lean_ctor_set_usize(x_3371, 2, x_3098);
x_3372 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3372, 0, x_3371);
lean_ctor_set(x_3372, 1, x_3273);
lean_ctor_set_usize(x_3372, 2, x_3096);
lean_ctor_set(x_15, 0, x_3372);
x_3373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3373, 0, x_15);
lean_ctor_set(x_3373, 1, x_20);
x_3374 = 1;
lean_inc(x_3373);
x_3375 = l_Lean_Syntax_isTermId_x3f(x_3373, x_3374);
if (lean_obj_tag(x_3375) == 0)
{
lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; 
lean_dec(x_3373);
x_3376 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3377 = lean_ctor_get(x_3376, 0);
lean_inc(x_3377);
x_3378 = lean_ctor_get(x_3376, 1);
lean_inc(x_3378);
lean_dec(x_3376);
x_3379 = lean_unsigned_to_nat(1u);
x_3380 = lean_nat_add(x_3, x_3379);
lean_dec(x_3);
x_3381 = l_Lean_mkHole(x_14);
lean_inc(x_3377);
x_3382 = l_Lean_Elab_Term_mkExplicitBinder(x_3377, x_3381);
x_3383 = lean_array_push(x_4, x_3382);
lean_inc(x_5);
x_3384 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3380, x_3383, x_5, x_3378);
if (lean_obj_tag(x_3384) == 0)
{
lean_object* x_3385; lean_object* x_3386; lean_object* x_3387; lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; lean_object* x_3429; lean_object* x_3430; lean_object* x_3431; lean_object* x_3432; lean_object* x_3433; lean_object* x_3434; 
x_3385 = lean_ctor_get(x_3384, 0);
lean_inc(x_3385);
x_3386 = lean_ctor_get(x_3385, 1);
lean_inc(x_3386);
x_3387 = lean_ctor_get(x_3384, 1);
lean_inc(x_3387);
lean_dec(x_3384);
x_3388 = lean_ctor_get(x_3385, 0);
lean_inc(x_3388);
if (lean_is_exclusive(x_3385)) {
 lean_ctor_release(x_3385, 0);
 lean_ctor_release(x_3385, 1);
 x_3389 = x_3385;
} else {
 lean_dec_ref(x_3385);
 x_3389 = lean_box(0);
}
x_3390 = lean_ctor_get(x_3386, 0);
lean_inc(x_3390);
if (lean_is_exclusive(x_3386)) {
 lean_ctor_release(x_3386, 0);
 lean_ctor_release(x_3386, 1);
 x_3391 = x_3386;
} else {
 lean_dec_ref(x_3386);
 x_3391 = lean_box(0);
}
x_3392 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3387);
lean_dec(x_5);
x_3393 = lean_ctor_get(x_3392, 1);
lean_inc(x_3393);
lean_dec(x_3392);
x_3394 = l_Lean_Elab_Term_getMainModule___rarg(x_3393);
x_3395 = lean_ctor_get(x_3394, 1);
lean_inc(x_3395);
if (lean_is_exclusive(x_3394)) {
 lean_ctor_release(x_3394, 0);
 lean_ctor_release(x_3394, 1);
 x_3396 = x_3394;
} else {
 lean_dec_ref(x_3394);
 x_3396 = lean_box(0);
}
x_3397 = l_Array_empty___closed__1;
x_3398 = lean_array_push(x_3397, x_3377);
x_3399 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3400 = lean_array_push(x_3398, x_3399);
x_3401 = l_Lean_mkTermIdFromIdent___closed__2;
x_3402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3402, 0, x_3401);
lean_ctor_set(x_3402, 1, x_3400);
x_3403 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3404 = lean_array_push(x_3403, x_3402);
x_3405 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3406, 0, x_3405);
lean_ctor_set(x_3406, 1, x_3404);
x_3407 = lean_array_push(x_3397, x_3406);
x_3408 = l_Lean_nullKind___closed__2;
x_3409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3409, 0, x_3408);
lean_ctor_set(x_3409, 1, x_3407);
x_3410 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3411 = lean_array_push(x_3410, x_3409);
x_3412 = lean_array_push(x_3411, x_3399);
x_3413 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3414 = lean_array_push(x_3412, x_3413);
x_3415 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3416 = lean_array_push(x_3414, x_3415);
lean_inc(x_14);
x_3417 = lean_array_push(x_3397, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3418 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3418 = lean_box(0);
}
if (lean_is_scalar(x_3418)) {
 x_3419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3419 = x_3418;
}
lean_ctor_set(x_3419, 0, x_3408);
lean_ctor_set(x_3419, 1, x_3417);
x_3420 = lean_array_push(x_3397, x_3419);
x_3421 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3422 = lean_array_push(x_3420, x_3421);
x_3423 = lean_array_push(x_3422, x_3390);
x_3424 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3425, 0, x_3424);
lean_ctor_set(x_3425, 1, x_3423);
x_3426 = lean_array_push(x_3397, x_3425);
x_3427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3427, 0, x_3408);
lean_ctor_set(x_3427, 1, x_3426);
x_3428 = lean_array_push(x_3416, x_3427);
x_3429 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3430, 0, x_3429);
lean_ctor_set(x_3430, 1, x_3428);
x_3431 = lean_box(x_3374);
if (lean_is_scalar(x_3391)) {
 x_3432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3432 = x_3391;
}
lean_ctor_set(x_3432, 0, x_3430);
lean_ctor_set(x_3432, 1, x_3431);
if (lean_is_scalar(x_3389)) {
 x_3433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3433 = x_3389;
}
lean_ctor_set(x_3433, 0, x_3388);
lean_ctor_set(x_3433, 1, x_3432);
if (lean_is_scalar(x_3396)) {
 x_3434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3434 = x_3396;
}
lean_ctor_set(x_3434, 0, x_3433);
lean_ctor_set(x_3434, 1, x_3395);
return x_3434;
}
else
{
lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; lean_object* x_3438; 
lean_dec(x_3377);
lean_dec(x_14);
lean_dec(x_5);
x_3435 = lean_ctor_get(x_3384, 0);
lean_inc(x_3435);
x_3436 = lean_ctor_get(x_3384, 1);
lean_inc(x_3436);
if (lean_is_exclusive(x_3384)) {
 lean_ctor_release(x_3384, 0);
 lean_ctor_release(x_3384, 1);
 x_3437 = x_3384;
} else {
 lean_dec_ref(x_3384);
 x_3437 = lean_box(0);
}
if (lean_is_scalar(x_3437)) {
 x_3438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3438 = x_3437;
}
lean_ctor_set(x_3438, 0, x_3435);
lean_ctor_set(x_3438, 1, x_3436);
return x_3438;
}
}
else
{
lean_object* x_3439; lean_object* x_3440; lean_object* x_3441; uint8_t x_3442; 
lean_dec(x_14);
x_3439 = lean_ctor_get(x_3375, 0);
lean_inc(x_3439);
lean_dec(x_3375);
x_3440 = lean_ctor_get(x_3439, 0);
lean_inc(x_3440);
x_3441 = lean_ctor_get(x_3439, 1);
lean_inc(x_3441);
lean_dec(x_3439);
x_3442 = l_Lean_Syntax_isNone(x_3441);
lean_dec(x_3441);
if (x_3442 == 0)
{
lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; lean_object* x_3448; 
lean_dec(x_3440);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3443 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_3444 = l_Lean_Elab_Term_throwErrorAt___rarg(x_3373, x_3443, x_5, x_6);
lean_dec(x_3373);
x_3445 = lean_ctor_get(x_3444, 0);
lean_inc(x_3445);
x_3446 = lean_ctor_get(x_3444, 1);
lean_inc(x_3446);
if (lean_is_exclusive(x_3444)) {
 lean_ctor_release(x_3444, 0);
 lean_ctor_release(x_3444, 1);
 x_3447 = x_3444;
} else {
 lean_dec_ref(x_3444);
 x_3447 = lean_box(0);
}
if (lean_is_scalar(x_3447)) {
 x_3448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3448 = x_3447;
}
lean_ctor_set(x_3448, 0, x_3445);
lean_ctor_set(x_3448, 1, x_3446);
return x_3448;
}
else
{
lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; 
x_3449 = l_Lean_mkHole(x_3373);
lean_dec(x_3373);
x_3450 = lean_unsigned_to_nat(1u);
x_3451 = lean_nat_add(x_3, x_3450);
lean_dec(x_3);
x_3452 = l_Lean_Elab_Term_mkExplicitBinder(x_3440, x_3449);
x_3453 = lean_array_push(x_4, x_3452);
x_3 = x_3451;
x_4 = x_3453;
goto _start;
}
}
}
else
{
lean_object* x_3455; lean_object* x_3456; uint8_t x_3457; 
lean_dec(x_3102);
lean_dec(x_3099);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3455 = lean_unsigned_to_nat(1u);
x_3456 = l_Lean_Syntax_getArg(x_14, x_3455);
x_3457 = l_Lean_Syntax_isNone(x_3456);
if (x_3457 == 0)
{
lean_object* x_3458; lean_object* x_3459; lean_object* x_3460; uint8_t x_3461; 
x_3458 = lean_unsigned_to_nat(0u);
x_3459 = l_Lean_Syntax_getArg(x_3456, x_3458);
x_3460 = l_Lean_Syntax_getArg(x_3456, x_3455);
lean_dec(x_3456);
x_3461 = l_Lean_Syntax_isNone(x_3460);
if (x_3461 == 0)
{
lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; uint8_t x_3469; 
x_3462 = l_Lean_Syntax_getArg(x_3460, x_3458);
lean_dec(x_3460);
lean_inc(x_3462);
x_3463 = l_Lean_Syntax_getKind(x_3462);
x_3464 = lean_name_mk_string(x_19, x_3103);
x_3465 = lean_name_mk_string(x_3464, x_3186);
x_3466 = lean_name_mk_string(x_3465, x_3273);
x_3467 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_3468 = lean_name_mk_string(x_3466, x_3467);
x_3469 = lean_name_eq(x_3463, x_3468);
lean_dec(x_3468);
lean_dec(x_3463);
if (x_3469 == 0)
{
lean_object* x_3470; lean_object* x_3471; lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; lean_object* x_3477; 
lean_dec(x_3462);
lean_dec(x_3459);
x_3470 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3471 = lean_ctor_get(x_3470, 0);
lean_inc(x_3471);
x_3472 = lean_ctor_get(x_3470, 1);
lean_inc(x_3472);
lean_dec(x_3470);
x_3473 = lean_nat_add(x_3, x_3455);
lean_dec(x_3);
x_3474 = l_Lean_mkHole(x_14);
lean_inc(x_3471);
x_3475 = l_Lean_Elab_Term_mkExplicitBinder(x_3471, x_3474);
x_3476 = lean_array_push(x_4, x_3475);
lean_inc(x_5);
x_3477 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3473, x_3476, x_5, x_3472);
if (lean_obj_tag(x_3477) == 0)
{
lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3499; lean_object* x_3500; lean_object* x_3501; lean_object* x_3502; lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; lean_object* x_3507; lean_object* x_3508; lean_object* x_3509; lean_object* x_3510; lean_object* x_3511; lean_object* x_3512; lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; uint8_t x_3524; lean_object* x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; 
x_3478 = lean_ctor_get(x_3477, 0);
lean_inc(x_3478);
x_3479 = lean_ctor_get(x_3478, 1);
lean_inc(x_3479);
x_3480 = lean_ctor_get(x_3477, 1);
lean_inc(x_3480);
lean_dec(x_3477);
x_3481 = lean_ctor_get(x_3478, 0);
lean_inc(x_3481);
if (lean_is_exclusive(x_3478)) {
 lean_ctor_release(x_3478, 0);
 lean_ctor_release(x_3478, 1);
 x_3482 = x_3478;
} else {
 lean_dec_ref(x_3478);
 x_3482 = lean_box(0);
}
x_3483 = lean_ctor_get(x_3479, 0);
lean_inc(x_3483);
if (lean_is_exclusive(x_3479)) {
 lean_ctor_release(x_3479, 0);
 lean_ctor_release(x_3479, 1);
 x_3484 = x_3479;
} else {
 lean_dec_ref(x_3479);
 x_3484 = lean_box(0);
}
x_3485 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3480);
lean_dec(x_5);
x_3486 = lean_ctor_get(x_3485, 1);
lean_inc(x_3486);
lean_dec(x_3485);
x_3487 = l_Lean_Elab_Term_getMainModule___rarg(x_3486);
x_3488 = lean_ctor_get(x_3487, 1);
lean_inc(x_3488);
if (lean_is_exclusive(x_3487)) {
 lean_ctor_release(x_3487, 0);
 lean_ctor_release(x_3487, 1);
 x_3489 = x_3487;
} else {
 lean_dec_ref(x_3487);
 x_3489 = lean_box(0);
}
x_3490 = l_Array_empty___closed__1;
x_3491 = lean_array_push(x_3490, x_3471);
x_3492 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3493 = lean_array_push(x_3491, x_3492);
x_3494 = l_Lean_mkTermIdFromIdent___closed__2;
x_3495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3495, 0, x_3494);
lean_ctor_set(x_3495, 1, x_3493);
x_3496 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3497 = lean_array_push(x_3496, x_3495);
x_3498 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3499, 0, x_3498);
lean_ctor_set(x_3499, 1, x_3497);
x_3500 = lean_array_push(x_3490, x_3499);
x_3501 = l_Lean_nullKind___closed__2;
x_3502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3502, 0, x_3501);
lean_ctor_set(x_3502, 1, x_3500);
x_3503 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3504 = lean_array_push(x_3503, x_3502);
x_3505 = lean_array_push(x_3504, x_3492);
x_3506 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3507 = lean_array_push(x_3505, x_3506);
x_3508 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3509 = lean_array_push(x_3507, x_3508);
lean_inc(x_14);
x_3510 = lean_array_push(x_3490, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3511 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3511 = lean_box(0);
}
if (lean_is_scalar(x_3511)) {
 x_3512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3512 = x_3511;
}
lean_ctor_set(x_3512, 0, x_3501);
lean_ctor_set(x_3512, 1, x_3510);
x_3513 = lean_array_push(x_3490, x_3512);
x_3514 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3515 = lean_array_push(x_3513, x_3514);
x_3516 = lean_array_push(x_3515, x_3483);
x_3517 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3518, 0, x_3517);
lean_ctor_set(x_3518, 1, x_3516);
x_3519 = lean_array_push(x_3490, x_3518);
x_3520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3520, 0, x_3501);
lean_ctor_set(x_3520, 1, x_3519);
x_3521 = lean_array_push(x_3509, x_3520);
x_3522 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3523, 0, x_3522);
lean_ctor_set(x_3523, 1, x_3521);
x_3524 = 1;
x_3525 = lean_box(x_3524);
if (lean_is_scalar(x_3484)) {
 x_3526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3526 = x_3484;
}
lean_ctor_set(x_3526, 0, x_3523);
lean_ctor_set(x_3526, 1, x_3525);
if (lean_is_scalar(x_3482)) {
 x_3527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3527 = x_3482;
}
lean_ctor_set(x_3527, 0, x_3481);
lean_ctor_set(x_3527, 1, x_3526);
if (lean_is_scalar(x_3489)) {
 x_3528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3528 = x_3489;
}
lean_ctor_set(x_3528, 0, x_3527);
lean_ctor_set(x_3528, 1, x_3488);
return x_3528;
}
else
{
lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; 
lean_dec(x_3471);
lean_dec(x_14);
lean_dec(x_5);
x_3529 = lean_ctor_get(x_3477, 0);
lean_inc(x_3529);
x_3530 = lean_ctor_get(x_3477, 1);
lean_inc(x_3530);
if (lean_is_exclusive(x_3477)) {
 lean_ctor_release(x_3477, 0);
 lean_ctor_release(x_3477, 1);
 x_3531 = x_3477;
} else {
 lean_dec_ref(x_3477);
 x_3531 = lean_box(0);
}
if (lean_is_scalar(x_3531)) {
 x_3532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3532 = x_3531;
}
lean_ctor_set(x_3532, 0, x_3529);
lean_ctor_set(x_3532, 1, x_3530);
return x_3532;
}
}
else
{
lean_object* x_3533; lean_object* x_3534; lean_object* x_3535; 
x_3533 = l_Lean_Syntax_getArg(x_3462, x_3455);
lean_dec(x_3462);
x_3534 = l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(x_3459, x_5, x_6);
x_3535 = lean_ctor_get(x_3534, 0);
lean_inc(x_3535);
if (lean_obj_tag(x_3535) == 0)
{
lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; lean_object* x_3541; lean_object* x_3542; lean_object* x_3543; lean_object* x_3544; 
lean_dec(x_3533);
x_3536 = lean_ctor_get(x_3534, 1);
lean_inc(x_3536);
lean_dec(x_3534);
x_3537 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_3536);
x_3538 = lean_ctor_get(x_3537, 0);
lean_inc(x_3538);
x_3539 = lean_ctor_get(x_3537, 1);
lean_inc(x_3539);
lean_dec(x_3537);
x_3540 = lean_nat_add(x_3, x_3455);
lean_dec(x_3);
x_3541 = l_Lean_mkHole(x_14);
lean_inc(x_3538);
x_3542 = l_Lean_Elab_Term_mkExplicitBinder(x_3538, x_3541);
x_3543 = lean_array_push(x_4, x_3542);
lean_inc(x_5);
x_3544 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3540, x_3543, x_5, x_3539);
if (lean_obj_tag(x_3544) == 0)
{
lean_object* x_3545; lean_object* x_3546; lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; lean_object* x_3554; lean_object* x_3555; lean_object* x_3556; lean_object* x_3557; lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; lean_object* x_3573; lean_object* x_3574; lean_object* x_3575; lean_object* x_3576; lean_object* x_3577; lean_object* x_3578; lean_object* x_3579; lean_object* x_3580; lean_object* x_3581; lean_object* x_3582; lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; uint8_t x_3591; lean_object* x_3592; lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; 
x_3545 = lean_ctor_get(x_3544, 0);
lean_inc(x_3545);
x_3546 = lean_ctor_get(x_3545, 1);
lean_inc(x_3546);
x_3547 = lean_ctor_get(x_3544, 1);
lean_inc(x_3547);
lean_dec(x_3544);
x_3548 = lean_ctor_get(x_3545, 0);
lean_inc(x_3548);
if (lean_is_exclusive(x_3545)) {
 lean_ctor_release(x_3545, 0);
 lean_ctor_release(x_3545, 1);
 x_3549 = x_3545;
} else {
 lean_dec_ref(x_3545);
 x_3549 = lean_box(0);
}
x_3550 = lean_ctor_get(x_3546, 0);
lean_inc(x_3550);
if (lean_is_exclusive(x_3546)) {
 lean_ctor_release(x_3546, 0);
 lean_ctor_release(x_3546, 1);
 x_3551 = x_3546;
} else {
 lean_dec_ref(x_3546);
 x_3551 = lean_box(0);
}
x_3552 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3547);
lean_dec(x_5);
x_3553 = lean_ctor_get(x_3552, 1);
lean_inc(x_3553);
lean_dec(x_3552);
x_3554 = l_Lean_Elab_Term_getMainModule___rarg(x_3553);
x_3555 = lean_ctor_get(x_3554, 1);
lean_inc(x_3555);
if (lean_is_exclusive(x_3554)) {
 lean_ctor_release(x_3554, 0);
 lean_ctor_release(x_3554, 1);
 x_3556 = x_3554;
} else {
 lean_dec_ref(x_3554);
 x_3556 = lean_box(0);
}
x_3557 = l_Array_empty___closed__1;
x_3558 = lean_array_push(x_3557, x_3538);
x_3559 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3560 = lean_array_push(x_3558, x_3559);
x_3561 = l_Lean_mkTermIdFromIdent___closed__2;
x_3562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3562, 0, x_3561);
lean_ctor_set(x_3562, 1, x_3560);
x_3563 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3564 = lean_array_push(x_3563, x_3562);
x_3565 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3566, 0, x_3565);
lean_ctor_set(x_3566, 1, x_3564);
x_3567 = lean_array_push(x_3557, x_3566);
x_3568 = l_Lean_nullKind___closed__2;
x_3569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3569, 0, x_3568);
lean_ctor_set(x_3569, 1, x_3567);
x_3570 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3571 = lean_array_push(x_3570, x_3569);
x_3572 = lean_array_push(x_3571, x_3559);
x_3573 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3574 = lean_array_push(x_3572, x_3573);
x_3575 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3576 = lean_array_push(x_3574, x_3575);
lean_inc(x_14);
x_3577 = lean_array_push(x_3557, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3578 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3578 = lean_box(0);
}
if (lean_is_scalar(x_3578)) {
 x_3579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3579 = x_3578;
}
lean_ctor_set(x_3579, 0, x_3568);
lean_ctor_set(x_3579, 1, x_3577);
x_3580 = lean_array_push(x_3557, x_3579);
x_3581 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3582 = lean_array_push(x_3580, x_3581);
x_3583 = lean_array_push(x_3582, x_3550);
x_3584 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3585, 0, x_3584);
lean_ctor_set(x_3585, 1, x_3583);
x_3586 = lean_array_push(x_3557, x_3585);
x_3587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3587, 0, x_3568);
lean_ctor_set(x_3587, 1, x_3586);
x_3588 = lean_array_push(x_3576, x_3587);
x_3589 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3590, 0, x_3589);
lean_ctor_set(x_3590, 1, x_3588);
x_3591 = 1;
x_3592 = lean_box(x_3591);
if (lean_is_scalar(x_3551)) {
 x_3593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3593 = x_3551;
}
lean_ctor_set(x_3593, 0, x_3590);
lean_ctor_set(x_3593, 1, x_3592);
if (lean_is_scalar(x_3549)) {
 x_3594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3594 = x_3549;
}
lean_ctor_set(x_3594, 0, x_3548);
lean_ctor_set(x_3594, 1, x_3593);
if (lean_is_scalar(x_3556)) {
 x_3595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3595 = x_3556;
}
lean_ctor_set(x_3595, 0, x_3594);
lean_ctor_set(x_3595, 1, x_3555);
return x_3595;
}
else
{
lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; lean_object* x_3599; 
lean_dec(x_3538);
lean_dec(x_14);
lean_dec(x_5);
x_3596 = lean_ctor_get(x_3544, 0);
lean_inc(x_3596);
x_3597 = lean_ctor_get(x_3544, 1);
lean_inc(x_3597);
if (lean_is_exclusive(x_3544)) {
 lean_ctor_release(x_3544, 0);
 lean_ctor_release(x_3544, 1);
 x_3598 = x_3544;
} else {
 lean_dec_ref(x_3544);
 x_3598 = lean_box(0);
}
if (lean_is_scalar(x_3598)) {
 x_3599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3599 = x_3598;
}
lean_ctor_set(x_3599, 0, x_3596);
lean_ctor_set(x_3599, 1, x_3597);
return x_3599;
}
}
else
{
lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; lean_object* x_3603; lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; 
lean_dec(x_14);
x_3600 = lean_ctor_get(x_3534, 1);
lean_inc(x_3600);
lean_dec(x_3534);
x_3601 = lean_ctor_get(x_3535, 0);
lean_inc(x_3601);
lean_dec(x_3535);
x_3602 = lean_nat_add(x_3, x_3455);
lean_dec(x_3);
x_3603 = x_3601;
x_3604 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(x_3533, x_3458, x_3603);
x_3605 = x_3604;
x_3606 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_3605, x_3605, x_3458, x_4);
lean_dec(x_3605);
x_3 = x_3602;
x_4 = x_3606;
x_6 = x_3600;
goto _start;
}
}
}
else
{
lean_object* x_3608; lean_object* x_3609; lean_object* x_3610; lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; lean_object* x_3614; lean_object* x_3615; 
lean_dec(x_3460);
lean_dec(x_3459);
x_3608 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3609 = lean_ctor_get(x_3608, 0);
lean_inc(x_3609);
x_3610 = lean_ctor_get(x_3608, 1);
lean_inc(x_3610);
lean_dec(x_3608);
x_3611 = lean_nat_add(x_3, x_3455);
lean_dec(x_3);
x_3612 = l_Lean_mkHole(x_14);
lean_inc(x_3609);
x_3613 = l_Lean_Elab_Term_mkExplicitBinder(x_3609, x_3612);
x_3614 = lean_array_push(x_4, x_3613);
lean_inc(x_5);
x_3615 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3611, x_3614, x_5, x_3610);
if (lean_obj_tag(x_3615) == 0)
{
lean_object* x_3616; lean_object* x_3617; lean_object* x_3618; lean_object* x_3619; lean_object* x_3620; lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; lean_object* x_3626; lean_object* x_3627; lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; lean_object* x_3631; lean_object* x_3632; lean_object* x_3633; lean_object* x_3634; lean_object* x_3635; lean_object* x_3636; lean_object* x_3637; lean_object* x_3638; lean_object* x_3639; lean_object* x_3640; lean_object* x_3641; lean_object* x_3642; lean_object* x_3643; lean_object* x_3644; lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; lean_object* x_3648; lean_object* x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; uint8_t x_3662; lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; 
x_3616 = lean_ctor_get(x_3615, 0);
lean_inc(x_3616);
x_3617 = lean_ctor_get(x_3616, 1);
lean_inc(x_3617);
x_3618 = lean_ctor_get(x_3615, 1);
lean_inc(x_3618);
lean_dec(x_3615);
x_3619 = lean_ctor_get(x_3616, 0);
lean_inc(x_3619);
if (lean_is_exclusive(x_3616)) {
 lean_ctor_release(x_3616, 0);
 lean_ctor_release(x_3616, 1);
 x_3620 = x_3616;
} else {
 lean_dec_ref(x_3616);
 x_3620 = lean_box(0);
}
x_3621 = lean_ctor_get(x_3617, 0);
lean_inc(x_3621);
if (lean_is_exclusive(x_3617)) {
 lean_ctor_release(x_3617, 0);
 lean_ctor_release(x_3617, 1);
 x_3622 = x_3617;
} else {
 lean_dec_ref(x_3617);
 x_3622 = lean_box(0);
}
x_3623 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3618);
lean_dec(x_5);
x_3624 = lean_ctor_get(x_3623, 1);
lean_inc(x_3624);
lean_dec(x_3623);
x_3625 = l_Lean_Elab_Term_getMainModule___rarg(x_3624);
x_3626 = lean_ctor_get(x_3625, 1);
lean_inc(x_3626);
if (lean_is_exclusive(x_3625)) {
 lean_ctor_release(x_3625, 0);
 lean_ctor_release(x_3625, 1);
 x_3627 = x_3625;
} else {
 lean_dec_ref(x_3625);
 x_3627 = lean_box(0);
}
x_3628 = l_Array_empty___closed__1;
x_3629 = lean_array_push(x_3628, x_3609);
x_3630 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3631 = lean_array_push(x_3629, x_3630);
x_3632 = l_Lean_mkTermIdFromIdent___closed__2;
x_3633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3633, 0, x_3632);
lean_ctor_set(x_3633, 1, x_3631);
x_3634 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3635 = lean_array_push(x_3634, x_3633);
x_3636 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3637, 0, x_3636);
lean_ctor_set(x_3637, 1, x_3635);
x_3638 = lean_array_push(x_3628, x_3637);
x_3639 = l_Lean_nullKind___closed__2;
x_3640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3640, 0, x_3639);
lean_ctor_set(x_3640, 1, x_3638);
x_3641 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3642 = lean_array_push(x_3641, x_3640);
x_3643 = lean_array_push(x_3642, x_3630);
x_3644 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3645 = lean_array_push(x_3643, x_3644);
x_3646 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3647 = lean_array_push(x_3645, x_3646);
lean_inc(x_14);
x_3648 = lean_array_push(x_3628, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3649 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3649 = lean_box(0);
}
if (lean_is_scalar(x_3649)) {
 x_3650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3650 = x_3649;
}
lean_ctor_set(x_3650, 0, x_3639);
lean_ctor_set(x_3650, 1, x_3648);
x_3651 = lean_array_push(x_3628, x_3650);
x_3652 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3653 = lean_array_push(x_3651, x_3652);
x_3654 = lean_array_push(x_3653, x_3621);
x_3655 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3656, 0, x_3655);
lean_ctor_set(x_3656, 1, x_3654);
x_3657 = lean_array_push(x_3628, x_3656);
x_3658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3658, 0, x_3639);
lean_ctor_set(x_3658, 1, x_3657);
x_3659 = lean_array_push(x_3647, x_3658);
x_3660 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3661, 0, x_3660);
lean_ctor_set(x_3661, 1, x_3659);
x_3662 = 1;
x_3663 = lean_box(x_3662);
if (lean_is_scalar(x_3622)) {
 x_3664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3664 = x_3622;
}
lean_ctor_set(x_3664, 0, x_3661);
lean_ctor_set(x_3664, 1, x_3663);
if (lean_is_scalar(x_3620)) {
 x_3665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3665 = x_3620;
}
lean_ctor_set(x_3665, 0, x_3619);
lean_ctor_set(x_3665, 1, x_3664);
if (lean_is_scalar(x_3627)) {
 x_3666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3666 = x_3627;
}
lean_ctor_set(x_3666, 0, x_3665);
lean_ctor_set(x_3666, 1, x_3626);
return x_3666;
}
else
{
lean_object* x_3667; lean_object* x_3668; lean_object* x_3669; lean_object* x_3670; 
lean_dec(x_3609);
lean_dec(x_14);
lean_dec(x_5);
x_3667 = lean_ctor_get(x_3615, 0);
lean_inc(x_3667);
x_3668 = lean_ctor_get(x_3615, 1);
lean_inc(x_3668);
if (lean_is_exclusive(x_3615)) {
 lean_ctor_release(x_3615, 0);
 lean_ctor_release(x_3615, 1);
 x_3669 = x_3615;
} else {
 lean_dec_ref(x_3615);
 x_3669 = lean_box(0);
}
if (lean_is_scalar(x_3669)) {
 x_3670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3670 = x_3669;
}
lean_ctor_set(x_3670, 0, x_3667);
lean_ctor_set(x_3670, 1, x_3668);
return x_3670;
}
}
}
else
{
lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; lean_object* x_3677; lean_object* x_3678; 
lean_dec(x_3456);
x_3671 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3672 = lean_ctor_get(x_3671, 0);
lean_inc(x_3672);
x_3673 = lean_ctor_get(x_3671, 1);
lean_inc(x_3673);
lean_dec(x_3671);
x_3674 = lean_nat_add(x_3, x_3455);
lean_dec(x_3);
x_3675 = l_Lean_mkHole(x_14);
lean_inc(x_3672);
x_3676 = l_Lean_Elab_Term_mkExplicitBinder(x_3672, x_3675);
x_3677 = lean_array_push(x_4, x_3676);
lean_inc(x_5);
x_3678 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3674, x_3677, x_5, x_3673);
if (lean_obj_tag(x_3678) == 0)
{
lean_object* x_3679; lean_object* x_3680; lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; lean_object* x_3695; lean_object* x_3696; lean_object* x_3697; lean_object* x_3698; lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; lean_object* x_3702; lean_object* x_3703; lean_object* x_3704; lean_object* x_3705; lean_object* x_3706; lean_object* x_3707; lean_object* x_3708; lean_object* x_3709; lean_object* x_3710; lean_object* x_3711; lean_object* x_3712; lean_object* x_3713; lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; lean_object* x_3717; lean_object* x_3718; lean_object* x_3719; lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; lean_object* x_3724; uint8_t x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; 
x_3679 = lean_ctor_get(x_3678, 0);
lean_inc(x_3679);
x_3680 = lean_ctor_get(x_3679, 1);
lean_inc(x_3680);
x_3681 = lean_ctor_get(x_3678, 1);
lean_inc(x_3681);
lean_dec(x_3678);
x_3682 = lean_ctor_get(x_3679, 0);
lean_inc(x_3682);
if (lean_is_exclusive(x_3679)) {
 lean_ctor_release(x_3679, 0);
 lean_ctor_release(x_3679, 1);
 x_3683 = x_3679;
} else {
 lean_dec_ref(x_3679);
 x_3683 = lean_box(0);
}
x_3684 = lean_ctor_get(x_3680, 0);
lean_inc(x_3684);
if (lean_is_exclusive(x_3680)) {
 lean_ctor_release(x_3680, 0);
 lean_ctor_release(x_3680, 1);
 x_3685 = x_3680;
} else {
 lean_dec_ref(x_3680);
 x_3685 = lean_box(0);
}
x_3686 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3681);
lean_dec(x_5);
x_3687 = lean_ctor_get(x_3686, 1);
lean_inc(x_3687);
lean_dec(x_3686);
x_3688 = l_Lean_Elab_Term_getMainModule___rarg(x_3687);
x_3689 = lean_ctor_get(x_3688, 1);
lean_inc(x_3689);
if (lean_is_exclusive(x_3688)) {
 lean_ctor_release(x_3688, 0);
 lean_ctor_release(x_3688, 1);
 x_3690 = x_3688;
} else {
 lean_dec_ref(x_3688);
 x_3690 = lean_box(0);
}
x_3691 = l_Array_empty___closed__1;
x_3692 = lean_array_push(x_3691, x_3672);
x_3693 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3694 = lean_array_push(x_3692, x_3693);
x_3695 = l_Lean_mkTermIdFromIdent___closed__2;
x_3696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3696, 0, x_3695);
lean_ctor_set(x_3696, 1, x_3694);
x_3697 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3698 = lean_array_push(x_3697, x_3696);
x_3699 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3700, 0, x_3699);
lean_ctor_set(x_3700, 1, x_3698);
x_3701 = lean_array_push(x_3691, x_3700);
x_3702 = l_Lean_nullKind___closed__2;
x_3703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3703, 0, x_3702);
lean_ctor_set(x_3703, 1, x_3701);
x_3704 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3705 = lean_array_push(x_3704, x_3703);
x_3706 = lean_array_push(x_3705, x_3693);
x_3707 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3708 = lean_array_push(x_3706, x_3707);
x_3709 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3710 = lean_array_push(x_3708, x_3709);
lean_inc(x_14);
x_3711 = lean_array_push(x_3691, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3712 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3712 = lean_box(0);
}
if (lean_is_scalar(x_3712)) {
 x_3713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3713 = x_3712;
}
lean_ctor_set(x_3713, 0, x_3702);
lean_ctor_set(x_3713, 1, x_3711);
x_3714 = lean_array_push(x_3691, x_3713);
x_3715 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3716 = lean_array_push(x_3714, x_3715);
x_3717 = lean_array_push(x_3716, x_3684);
x_3718 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3719, 0, x_3718);
lean_ctor_set(x_3719, 1, x_3717);
x_3720 = lean_array_push(x_3691, x_3719);
x_3721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3721, 0, x_3702);
lean_ctor_set(x_3721, 1, x_3720);
x_3722 = lean_array_push(x_3710, x_3721);
x_3723 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3724, 0, x_3723);
lean_ctor_set(x_3724, 1, x_3722);
x_3725 = 1;
x_3726 = lean_box(x_3725);
if (lean_is_scalar(x_3685)) {
 x_3727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3727 = x_3685;
}
lean_ctor_set(x_3727, 0, x_3724);
lean_ctor_set(x_3727, 1, x_3726);
if (lean_is_scalar(x_3683)) {
 x_3728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3728 = x_3683;
}
lean_ctor_set(x_3728, 0, x_3682);
lean_ctor_set(x_3728, 1, x_3727);
if (lean_is_scalar(x_3690)) {
 x_3729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3729 = x_3690;
}
lean_ctor_set(x_3729, 0, x_3728);
lean_ctor_set(x_3729, 1, x_3689);
return x_3729;
}
else
{
lean_object* x_3730; lean_object* x_3731; lean_object* x_3732; lean_object* x_3733; 
lean_dec(x_3672);
lean_dec(x_14);
lean_dec(x_5);
x_3730 = lean_ctor_get(x_3678, 0);
lean_inc(x_3730);
x_3731 = lean_ctor_get(x_3678, 1);
lean_inc(x_3731);
if (lean_is_exclusive(x_3678)) {
 lean_ctor_release(x_3678, 0);
 lean_ctor_release(x_3678, 1);
 x_3732 = x_3678;
} else {
 lean_dec_ref(x_3678);
 x_3732 = lean_box(0);
}
if (lean_is_scalar(x_3732)) {
 x_3733 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3733 = x_3732;
}
lean_ctor_set(x_3733, 0, x_3730);
lean_ctor_set(x_3733, 1, x_3731);
return x_3733;
}
}
}
}
else
{
lean_object* x_3734; lean_object* x_3735; lean_object* x_3736; lean_object* x_3737; lean_object* x_3738; lean_object* x_3739; lean_object* x_3740; 
lean_dec(x_3102);
lean_dec(x_3099);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3734 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3735 = lean_ctor_get(x_3734, 0);
lean_inc(x_3735);
x_3736 = lean_ctor_get(x_3734, 1);
lean_inc(x_3736);
lean_dec(x_3734);
x_3737 = lean_unsigned_to_nat(1u);
x_3738 = lean_nat_add(x_3, x_3737);
lean_dec(x_3);
x_3739 = l_Lean_Elab_Term_mkExplicitBinder(x_3735, x_14);
x_3740 = lean_array_push(x_4, x_3739);
x_3 = x_3738;
x_4 = x_3740;
x_6 = x_3736;
goto _start;
}
}
else
{
lean_object* x_3742; lean_object* x_3743; lean_object* x_3744; 
lean_dec(x_3102);
lean_dec(x_3099);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3742 = lean_unsigned_to_nat(1u);
x_3743 = lean_nat_add(x_3, x_3742);
lean_dec(x_3);
x_3744 = lean_array_push(x_4, x_14);
x_3 = x_3743;
x_4 = x_3744;
goto _start;
}
}
else
{
lean_object* x_3746; lean_object* x_3747; lean_object* x_3748; 
lean_dec(x_3102);
lean_dec(x_3099);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3746 = lean_unsigned_to_nat(1u);
x_3747 = lean_nat_add(x_3, x_3746);
lean_dec(x_3);
x_3748 = lean_array_push(x_4, x_14);
x_3 = x_3747;
x_4 = x_3748;
goto _start;
}
}
else
{
lean_object* x_3750; lean_object* x_3751; lean_object* x_3752; 
lean_dec(x_3102);
lean_dec(x_3099);
lean_free_object(x_15);
lean_dec(x_22);
lean_dec(x_20);
x_3750 = lean_unsigned_to_nat(1u);
x_3751 = lean_nat_add(x_3, x_3750);
lean_dec(x_3);
x_3752 = lean_array_push(x_4, x_14);
x_3 = x_3751;
x_4 = x_3752;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_3754; size_t x_3755; lean_object* x_3756; size_t x_3757; lean_object* x_3758; lean_object* x_3759; size_t x_3760; lean_object* x_3761; lean_object* x_3762; size_t x_3763; lean_object* x_3764; lean_object* x_3765; uint8_t x_3766; 
x_3754 = lean_ctor_get(x_15, 1);
x_3755 = lean_ctor_get_usize(x_15, 2);
lean_inc(x_3754);
lean_dec(x_15);
x_3756 = lean_ctor_get(x_16, 1);
lean_inc(x_3756);
x_3757 = lean_ctor_get_usize(x_16, 2);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_3758 = x_16;
} else {
 lean_dec_ref(x_16);
 x_3758 = lean_box(0);
}
x_3759 = lean_ctor_get(x_17, 1);
lean_inc(x_3759);
x_3760 = lean_ctor_get_usize(x_17, 2);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_3761 = x_17;
} else {
 lean_dec_ref(x_17);
 x_3761 = lean_box(0);
}
x_3762 = lean_ctor_get(x_18, 1);
lean_inc(x_3762);
x_3763 = lean_ctor_get_usize(x_18, 2);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_3764 = x_18;
} else {
 lean_dec_ref(x_18);
 x_3764 = lean_box(0);
}
x_3765 = l_Lean_mkAppStx___closed__1;
x_3766 = lean_string_dec_eq(x_3762, x_3765);
lean_dec(x_3762);
if (x_3766 == 0)
{
uint8_t x_3767; lean_object* x_3768; 
lean_dec(x_3764);
lean_dec(x_3761);
lean_dec(x_3759);
lean_dec(x_3758);
lean_dec(x_3756);
lean_dec(x_3754);
lean_dec(x_20);
x_3767 = 1;
lean_inc(x_14);
x_3768 = l_Lean_Syntax_isTermId_x3f(x_14, x_3767);
if (lean_obj_tag(x_3768) == 0)
{
lean_object* x_3769; lean_object* x_3770; lean_object* x_3771; lean_object* x_3772; lean_object* x_3773; lean_object* x_3774; lean_object* x_3775; lean_object* x_3776; lean_object* x_3777; 
x_3769 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3770 = lean_ctor_get(x_3769, 0);
lean_inc(x_3770);
x_3771 = lean_ctor_get(x_3769, 1);
lean_inc(x_3771);
lean_dec(x_3769);
x_3772 = lean_unsigned_to_nat(1u);
x_3773 = lean_nat_add(x_3, x_3772);
lean_dec(x_3);
x_3774 = l_Lean_mkHole(x_14);
lean_inc(x_3770);
x_3775 = l_Lean_Elab_Term_mkExplicitBinder(x_3770, x_3774);
x_3776 = lean_array_push(x_4, x_3775);
lean_inc(x_5);
x_3777 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3773, x_3776, x_5, x_3771);
if (lean_obj_tag(x_3777) == 0)
{
lean_object* x_3778; lean_object* x_3779; lean_object* x_3780; lean_object* x_3781; lean_object* x_3782; lean_object* x_3783; lean_object* x_3784; lean_object* x_3785; lean_object* x_3786; lean_object* x_3787; lean_object* x_3788; lean_object* x_3789; lean_object* x_3790; lean_object* x_3791; lean_object* x_3792; lean_object* x_3793; lean_object* x_3794; lean_object* x_3795; lean_object* x_3796; lean_object* x_3797; lean_object* x_3798; lean_object* x_3799; lean_object* x_3800; lean_object* x_3801; lean_object* x_3802; lean_object* x_3803; lean_object* x_3804; lean_object* x_3805; lean_object* x_3806; lean_object* x_3807; lean_object* x_3808; lean_object* x_3809; lean_object* x_3810; lean_object* x_3811; lean_object* x_3812; lean_object* x_3813; lean_object* x_3814; lean_object* x_3815; lean_object* x_3816; lean_object* x_3817; lean_object* x_3818; lean_object* x_3819; lean_object* x_3820; lean_object* x_3821; lean_object* x_3822; lean_object* x_3823; lean_object* x_3824; lean_object* x_3825; lean_object* x_3826; lean_object* x_3827; 
x_3778 = lean_ctor_get(x_3777, 0);
lean_inc(x_3778);
x_3779 = lean_ctor_get(x_3778, 1);
lean_inc(x_3779);
x_3780 = lean_ctor_get(x_3777, 1);
lean_inc(x_3780);
lean_dec(x_3777);
x_3781 = lean_ctor_get(x_3778, 0);
lean_inc(x_3781);
if (lean_is_exclusive(x_3778)) {
 lean_ctor_release(x_3778, 0);
 lean_ctor_release(x_3778, 1);
 x_3782 = x_3778;
} else {
 lean_dec_ref(x_3778);
 x_3782 = lean_box(0);
}
x_3783 = lean_ctor_get(x_3779, 0);
lean_inc(x_3783);
if (lean_is_exclusive(x_3779)) {
 lean_ctor_release(x_3779, 0);
 lean_ctor_release(x_3779, 1);
 x_3784 = x_3779;
} else {
 lean_dec_ref(x_3779);
 x_3784 = lean_box(0);
}
x_3785 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3780);
lean_dec(x_5);
x_3786 = lean_ctor_get(x_3785, 1);
lean_inc(x_3786);
lean_dec(x_3785);
x_3787 = l_Lean_Elab_Term_getMainModule___rarg(x_3786);
x_3788 = lean_ctor_get(x_3787, 1);
lean_inc(x_3788);
if (lean_is_exclusive(x_3787)) {
 lean_ctor_release(x_3787, 0);
 lean_ctor_release(x_3787, 1);
 x_3789 = x_3787;
} else {
 lean_dec_ref(x_3787);
 x_3789 = lean_box(0);
}
x_3790 = l_Array_empty___closed__1;
x_3791 = lean_array_push(x_3790, x_3770);
x_3792 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3793 = lean_array_push(x_3791, x_3792);
x_3794 = l_Lean_mkTermIdFromIdent___closed__2;
x_3795 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3795, 0, x_3794);
lean_ctor_set(x_3795, 1, x_3793);
x_3796 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3797 = lean_array_push(x_3796, x_3795);
x_3798 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3799, 0, x_3798);
lean_ctor_set(x_3799, 1, x_3797);
x_3800 = lean_array_push(x_3790, x_3799);
x_3801 = l_Lean_nullKind___closed__2;
x_3802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3802, 0, x_3801);
lean_ctor_set(x_3802, 1, x_3800);
x_3803 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3804 = lean_array_push(x_3803, x_3802);
x_3805 = lean_array_push(x_3804, x_3792);
x_3806 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3807 = lean_array_push(x_3805, x_3806);
x_3808 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3809 = lean_array_push(x_3807, x_3808);
lean_inc(x_14);
x_3810 = lean_array_push(x_3790, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3811 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3811 = lean_box(0);
}
if (lean_is_scalar(x_3811)) {
 x_3812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3812 = x_3811;
}
lean_ctor_set(x_3812, 0, x_3801);
lean_ctor_set(x_3812, 1, x_3810);
x_3813 = lean_array_push(x_3790, x_3812);
x_3814 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3815 = lean_array_push(x_3813, x_3814);
x_3816 = lean_array_push(x_3815, x_3783);
x_3817 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3818, 0, x_3817);
lean_ctor_set(x_3818, 1, x_3816);
x_3819 = lean_array_push(x_3790, x_3818);
x_3820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3820, 0, x_3801);
lean_ctor_set(x_3820, 1, x_3819);
x_3821 = lean_array_push(x_3809, x_3820);
x_3822 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3823, 0, x_3822);
lean_ctor_set(x_3823, 1, x_3821);
x_3824 = lean_box(x_3767);
if (lean_is_scalar(x_3784)) {
 x_3825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3825 = x_3784;
}
lean_ctor_set(x_3825, 0, x_3823);
lean_ctor_set(x_3825, 1, x_3824);
if (lean_is_scalar(x_3782)) {
 x_3826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3826 = x_3782;
}
lean_ctor_set(x_3826, 0, x_3781);
lean_ctor_set(x_3826, 1, x_3825);
if (lean_is_scalar(x_3789)) {
 x_3827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3827 = x_3789;
}
lean_ctor_set(x_3827, 0, x_3826);
lean_ctor_set(x_3827, 1, x_3788);
return x_3827;
}
else
{
lean_object* x_3828; lean_object* x_3829; lean_object* x_3830; lean_object* x_3831; 
lean_dec(x_3770);
lean_dec(x_14);
lean_dec(x_5);
x_3828 = lean_ctor_get(x_3777, 0);
lean_inc(x_3828);
x_3829 = lean_ctor_get(x_3777, 1);
lean_inc(x_3829);
if (lean_is_exclusive(x_3777)) {
 lean_ctor_release(x_3777, 0);
 lean_ctor_release(x_3777, 1);
 x_3830 = x_3777;
} else {
 lean_dec_ref(x_3777);
 x_3830 = lean_box(0);
}
if (lean_is_scalar(x_3830)) {
 x_3831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3831 = x_3830;
}
lean_ctor_set(x_3831, 0, x_3828);
lean_ctor_set(x_3831, 1, x_3829);
return x_3831;
}
}
else
{
lean_object* x_3832; lean_object* x_3833; lean_object* x_3834; uint8_t x_3835; 
x_3832 = lean_ctor_get(x_3768, 0);
lean_inc(x_3832);
lean_dec(x_3768);
x_3833 = lean_ctor_get(x_3832, 0);
lean_inc(x_3833);
x_3834 = lean_ctor_get(x_3832, 1);
lean_inc(x_3834);
lean_dec(x_3832);
x_3835 = l_Lean_Syntax_isNone(x_3834);
lean_dec(x_3834);
if (x_3835 == 0)
{
lean_object* x_3836; lean_object* x_3837; lean_object* x_3838; lean_object* x_3839; lean_object* x_3840; lean_object* x_3841; 
lean_dec(x_3833);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3836 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_3837 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_3836, x_5, x_6);
lean_dec(x_14);
x_3838 = lean_ctor_get(x_3837, 0);
lean_inc(x_3838);
x_3839 = lean_ctor_get(x_3837, 1);
lean_inc(x_3839);
if (lean_is_exclusive(x_3837)) {
 lean_ctor_release(x_3837, 0);
 lean_ctor_release(x_3837, 1);
 x_3840 = x_3837;
} else {
 lean_dec_ref(x_3837);
 x_3840 = lean_box(0);
}
if (lean_is_scalar(x_3840)) {
 x_3841 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3841 = x_3840;
}
lean_ctor_set(x_3841, 0, x_3838);
lean_ctor_set(x_3841, 1, x_3839);
return x_3841;
}
else
{
lean_object* x_3842; lean_object* x_3843; lean_object* x_3844; lean_object* x_3845; lean_object* x_3846; 
x_3842 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_3843 = lean_unsigned_to_nat(1u);
x_3844 = lean_nat_add(x_3, x_3843);
lean_dec(x_3);
x_3845 = l_Lean_Elab_Term_mkExplicitBinder(x_3833, x_3842);
x_3846 = lean_array_push(x_4, x_3845);
x_3 = x_3844;
x_4 = x_3846;
goto _start;
}
}
}
else
{
lean_object* x_3848; uint8_t x_3849; 
x_3848 = l_Lean_mkAppStx___closed__3;
x_3849 = lean_string_dec_eq(x_3759, x_3848);
if (x_3849 == 0)
{
lean_object* x_3850; lean_object* x_3851; lean_object* x_3852; lean_object* x_3853; lean_object* x_3854; uint8_t x_3855; lean_object* x_3856; 
if (lean_is_scalar(x_3764)) {
 x_3850 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3850 = x_3764;
}
lean_ctor_set(x_3850, 0, x_19);
lean_ctor_set(x_3850, 1, x_3765);
lean_ctor_set_usize(x_3850, 2, x_3763);
if (lean_is_scalar(x_3761)) {
 x_3851 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3851 = x_3761;
}
lean_ctor_set(x_3851, 0, x_3850);
lean_ctor_set(x_3851, 1, x_3759);
lean_ctor_set_usize(x_3851, 2, x_3760);
if (lean_is_scalar(x_3758)) {
 x_3852 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3852 = x_3758;
}
lean_ctor_set(x_3852, 0, x_3851);
lean_ctor_set(x_3852, 1, x_3756);
lean_ctor_set_usize(x_3852, 2, x_3757);
x_3853 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3853, 0, x_3852);
lean_ctor_set(x_3853, 1, x_3754);
lean_ctor_set_usize(x_3853, 2, x_3755);
x_3854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3854, 0, x_3853);
lean_ctor_set(x_3854, 1, x_20);
x_3855 = 1;
lean_inc(x_3854);
x_3856 = l_Lean_Syntax_isTermId_x3f(x_3854, x_3855);
if (lean_obj_tag(x_3856) == 0)
{
lean_object* x_3857; lean_object* x_3858; lean_object* x_3859; lean_object* x_3860; lean_object* x_3861; lean_object* x_3862; lean_object* x_3863; lean_object* x_3864; lean_object* x_3865; 
lean_dec(x_3854);
x_3857 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3858 = lean_ctor_get(x_3857, 0);
lean_inc(x_3858);
x_3859 = lean_ctor_get(x_3857, 1);
lean_inc(x_3859);
lean_dec(x_3857);
x_3860 = lean_unsigned_to_nat(1u);
x_3861 = lean_nat_add(x_3, x_3860);
lean_dec(x_3);
x_3862 = l_Lean_mkHole(x_14);
lean_inc(x_3858);
x_3863 = l_Lean_Elab_Term_mkExplicitBinder(x_3858, x_3862);
x_3864 = lean_array_push(x_4, x_3863);
lean_inc(x_5);
x_3865 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3861, x_3864, x_5, x_3859);
if (lean_obj_tag(x_3865) == 0)
{
lean_object* x_3866; lean_object* x_3867; lean_object* x_3868; lean_object* x_3869; lean_object* x_3870; lean_object* x_3871; lean_object* x_3872; lean_object* x_3873; lean_object* x_3874; lean_object* x_3875; lean_object* x_3876; lean_object* x_3877; lean_object* x_3878; lean_object* x_3879; lean_object* x_3880; lean_object* x_3881; lean_object* x_3882; lean_object* x_3883; lean_object* x_3884; lean_object* x_3885; lean_object* x_3886; lean_object* x_3887; lean_object* x_3888; lean_object* x_3889; lean_object* x_3890; lean_object* x_3891; lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; lean_object* x_3896; lean_object* x_3897; lean_object* x_3898; lean_object* x_3899; lean_object* x_3900; lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; lean_object* x_3904; lean_object* x_3905; lean_object* x_3906; lean_object* x_3907; lean_object* x_3908; lean_object* x_3909; lean_object* x_3910; lean_object* x_3911; lean_object* x_3912; lean_object* x_3913; lean_object* x_3914; lean_object* x_3915; 
x_3866 = lean_ctor_get(x_3865, 0);
lean_inc(x_3866);
x_3867 = lean_ctor_get(x_3866, 1);
lean_inc(x_3867);
x_3868 = lean_ctor_get(x_3865, 1);
lean_inc(x_3868);
lean_dec(x_3865);
x_3869 = lean_ctor_get(x_3866, 0);
lean_inc(x_3869);
if (lean_is_exclusive(x_3866)) {
 lean_ctor_release(x_3866, 0);
 lean_ctor_release(x_3866, 1);
 x_3870 = x_3866;
} else {
 lean_dec_ref(x_3866);
 x_3870 = lean_box(0);
}
x_3871 = lean_ctor_get(x_3867, 0);
lean_inc(x_3871);
if (lean_is_exclusive(x_3867)) {
 lean_ctor_release(x_3867, 0);
 lean_ctor_release(x_3867, 1);
 x_3872 = x_3867;
} else {
 lean_dec_ref(x_3867);
 x_3872 = lean_box(0);
}
x_3873 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3868);
lean_dec(x_5);
x_3874 = lean_ctor_get(x_3873, 1);
lean_inc(x_3874);
lean_dec(x_3873);
x_3875 = l_Lean_Elab_Term_getMainModule___rarg(x_3874);
x_3876 = lean_ctor_get(x_3875, 1);
lean_inc(x_3876);
if (lean_is_exclusive(x_3875)) {
 lean_ctor_release(x_3875, 0);
 lean_ctor_release(x_3875, 1);
 x_3877 = x_3875;
} else {
 lean_dec_ref(x_3875);
 x_3877 = lean_box(0);
}
x_3878 = l_Array_empty___closed__1;
x_3879 = lean_array_push(x_3878, x_3858);
x_3880 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3881 = lean_array_push(x_3879, x_3880);
x_3882 = l_Lean_mkTermIdFromIdent___closed__2;
x_3883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3883, 0, x_3882);
lean_ctor_set(x_3883, 1, x_3881);
x_3884 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3885 = lean_array_push(x_3884, x_3883);
x_3886 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3887, 0, x_3886);
lean_ctor_set(x_3887, 1, x_3885);
x_3888 = lean_array_push(x_3878, x_3887);
x_3889 = l_Lean_nullKind___closed__2;
x_3890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3890, 0, x_3889);
lean_ctor_set(x_3890, 1, x_3888);
x_3891 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3892 = lean_array_push(x_3891, x_3890);
x_3893 = lean_array_push(x_3892, x_3880);
x_3894 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3895 = lean_array_push(x_3893, x_3894);
x_3896 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3897 = lean_array_push(x_3895, x_3896);
lean_inc(x_14);
x_3898 = lean_array_push(x_3878, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3899 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3899 = lean_box(0);
}
if (lean_is_scalar(x_3899)) {
 x_3900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3900 = x_3899;
}
lean_ctor_set(x_3900, 0, x_3889);
lean_ctor_set(x_3900, 1, x_3898);
x_3901 = lean_array_push(x_3878, x_3900);
x_3902 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3903 = lean_array_push(x_3901, x_3902);
x_3904 = lean_array_push(x_3903, x_3871);
x_3905 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3906, 0, x_3905);
lean_ctor_set(x_3906, 1, x_3904);
x_3907 = lean_array_push(x_3878, x_3906);
x_3908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3908, 0, x_3889);
lean_ctor_set(x_3908, 1, x_3907);
x_3909 = lean_array_push(x_3897, x_3908);
x_3910 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3911 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3911, 0, x_3910);
lean_ctor_set(x_3911, 1, x_3909);
x_3912 = lean_box(x_3855);
if (lean_is_scalar(x_3872)) {
 x_3913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3913 = x_3872;
}
lean_ctor_set(x_3913, 0, x_3911);
lean_ctor_set(x_3913, 1, x_3912);
if (lean_is_scalar(x_3870)) {
 x_3914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3914 = x_3870;
}
lean_ctor_set(x_3914, 0, x_3869);
lean_ctor_set(x_3914, 1, x_3913);
if (lean_is_scalar(x_3877)) {
 x_3915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3915 = x_3877;
}
lean_ctor_set(x_3915, 0, x_3914);
lean_ctor_set(x_3915, 1, x_3876);
return x_3915;
}
else
{
lean_object* x_3916; lean_object* x_3917; lean_object* x_3918; lean_object* x_3919; 
lean_dec(x_3858);
lean_dec(x_14);
lean_dec(x_5);
x_3916 = lean_ctor_get(x_3865, 0);
lean_inc(x_3916);
x_3917 = lean_ctor_get(x_3865, 1);
lean_inc(x_3917);
if (lean_is_exclusive(x_3865)) {
 lean_ctor_release(x_3865, 0);
 lean_ctor_release(x_3865, 1);
 x_3918 = x_3865;
} else {
 lean_dec_ref(x_3865);
 x_3918 = lean_box(0);
}
if (lean_is_scalar(x_3918)) {
 x_3919 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3919 = x_3918;
}
lean_ctor_set(x_3919, 0, x_3916);
lean_ctor_set(x_3919, 1, x_3917);
return x_3919;
}
}
else
{
lean_object* x_3920; lean_object* x_3921; lean_object* x_3922; uint8_t x_3923; 
lean_dec(x_14);
x_3920 = lean_ctor_get(x_3856, 0);
lean_inc(x_3920);
lean_dec(x_3856);
x_3921 = lean_ctor_get(x_3920, 0);
lean_inc(x_3921);
x_3922 = lean_ctor_get(x_3920, 1);
lean_inc(x_3922);
lean_dec(x_3920);
x_3923 = l_Lean_Syntax_isNone(x_3922);
lean_dec(x_3922);
if (x_3923 == 0)
{
lean_object* x_3924; lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; lean_object* x_3928; lean_object* x_3929; 
lean_dec(x_3921);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_3924 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_3925 = l_Lean_Elab_Term_throwErrorAt___rarg(x_3854, x_3924, x_5, x_6);
lean_dec(x_3854);
x_3926 = lean_ctor_get(x_3925, 0);
lean_inc(x_3926);
x_3927 = lean_ctor_get(x_3925, 1);
lean_inc(x_3927);
if (lean_is_exclusive(x_3925)) {
 lean_ctor_release(x_3925, 0);
 lean_ctor_release(x_3925, 1);
 x_3928 = x_3925;
} else {
 lean_dec_ref(x_3925);
 x_3928 = lean_box(0);
}
if (lean_is_scalar(x_3928)) {
 x_3929 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3929 = x_3928;
}
lean_ctor_set(x_3929, 0, x_3926);
lean_ctor_set(x_3929, 1, x_3927);
return x_3929;
}
else
{
lean_object* x_3930; lean_object* x_3931; lean_object* x_3932; lean_object* x_3933; lean_object* x_3934; 
x_3930 = l_Lean_mkHole(x_3854);
lean_dec(x_3854);
x_3931 = lean_unsigned_to_nat(1u);
x_3932 = lean_nat_add(x_3, x_3931);
lean_dec(x_3);
x_3933 = l_Lean_Elab_Term_mkExplicitBinder(x_3921, x_3930);
x_3934 = lean_array_push(x_4, x_3933);
x_3 = x_3932;
x_4 = x_3934;
goto _start;
}
}
}
else
{
lean_object* x_3936; uint8_t x_3937; 
lean_dec(x_3759);
x_3936 = l_Lean_mkAppStx___closed__5;
x_3937 = lean_string_dec_eq(x_3756, x_3936);
if (x_3937 == 0)
{
lean_object* x_3938; lean_object* x_3939; lean_object* x_3940; lean_object* x_3941; lean_object* x_3942; uint8_t x_3943; lean_object* x_3944; 
if (lean_is_scalar(x_3764)) {
 x_3938 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3938 = x_3764;
}
lean_ctor_set(x_3938, 0, x_19);
lean_ctor_set(x_3938, 1, x_3765);
lean_ctor_set_usize(x_3938, 2, x_3763);
if (lean_is_scalar(x_3761)) {
 x_3939 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3939 = x_3761;
}
lean_ctor_set(x_3939, 0, x_3938);
lean_ctor_set(x_3939, 1, x_3848);
lean_ctor_set_usize(x_3939, 2, x_3760);
if (lean_is_scalar(x_3758)) {
 x_3940 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_3940 = x_3758;
}
lean_ctor_set(x_3940, 0, x_3939);
lean_ctor_set(x_3940, 1, x_3756);
lean_ctor_set_usize(x_3940, 2, x_3757);
x_3941 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_3941, 0, x_3940);
lean_ctor_set(x_3941, 1, x_3754);
lean_ctor_set_usize(x_3941, 2, x_3755);
x_3942 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3942, 0, x_3941);
lean_ctor_set(x_3942, 1, x_20);
x_3943 = 1;
lean_inc(x_3942);
x_3944 = l_Lean_Syntax_isTermId_x3f(x_3942, x_3943);
if (lean_obj_tag(x_3944) == 0)
{
lean_object* x_3945; lean_object* x_3946; lean_object* x_3947; lean_object* x_3948; lean_object* x_3949; lean_object* x_3950; lean_object* x_3951; lean_object* x_3952; lean_object* x_3953; 
lean_dec(x_3942);
x_3945 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_3946 = lean_ctor_get(x_3945, 0);
lean_inc(x_3946);
x_3947 = lean_ctor_get(x_3945, 1);
lean_inc(x_3947);
lean_dec(x_3945);
x_3948 = lean_unsigned_to_nat(1u);
x_3949 = lean_nat_add(x_3, x_3948);
lean_dec(x_3);
x_3950 = l_Lean_mkHole(x_14);
lean_inc(x_3946);
x_3951 = l_Lean_Elab_Term_mkExplicitBinder(x_3946, x_3950);
x_3952 = lean_array_push(x_4, x_3951);
lean_inc(x_5);
x_3953 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3949, x_3952, x_5, x_3947);
if (lean_obj_tag(x_3953) == 0)
{
lean_object* x_3954; lean_object* x_3955; lean_object* x_3956; lean_object* x_3957; lean_object* x_3958; lean_object* x_3959; lean_object* x_3960; lean_object* x_3961; lean_object* x_3962; lean_object* x_3963; lean_object* x_3964; lean_object* x_3965; lean_object* x_3966; lean_object* x_3967; lean_object* x_3968; lean_object* x_3969; lean_object* x_3970; lean_object* x_3971; lean_object* x_3972; lean_object* x_3973; lean_object* x_3974; lean_object* x_3975; lean_object* x_3976; lean_object* x_3977; lean_object* x_3978; lean_object* x_3979; lean_object* x_3980; lean_object* x_3981; lean_object* x_3982; lean_object* x_3983; lean_object* x_3984; lean_object* x_3985; lean_object* x_3986; lean_object* x_3987; lean_object* x_3988; lean_object* x_3989; lean_object* x_3990; lean_object* x_3991; lean_object* x_3992; lean_object* x_3993; lean_object* x_3994; lean_object* x_3995; lean_object* x_3996; lean_object* x_3997; lean_object* x_3998; lean_object* x_3999; lean_object* x_4000; lean_object* x_4001; lean_object* x_4002; lean_object* x_4003; 
x_3954 = lean_ctor_get(x_3953, 0);
lean_inc(x_3954);
x_3955 = lean_ctor_get(x_3954, 1);
lean_inc(x_3955);
x_3956 = lean_ctor_get(x_3953, 1);
lean_inc(x_3956);
lean_dec(x_3953);
x_3957 = lean_ctor_get(x_3954, 0);
lean_inc(x_3957);
if (lean_is_exclusive(x_3954)) {
 lean_ctor_release(x_3954, 0);
 lean_ctor_release(x_3954, 1);
 x_3958 = x_3954;
} else {
 lean_dec_ref(x_3954);
 x_3958 = lean_box(0);
}
x_3959 = lean_ctor_get(x_3955, 0);
lean_inc(x_3959);
if (lean_is_exclusive(x_3955)) {
 lean_ctor_release(x_3955, 0);
 lean_ctor_release(x_3955, 1);
 x_3960 = x_3955;
} else {
 lean_dec_ref(x_3955);
 x_3960 = lean_box(0);
}
x_3961 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_3956);
lean_dec(x_5);
x_3962 = lean_ctor_get(x_3961, 1);
lean_inc(x_3962);
lean_dec(x_3961);
x_3963 = l_Lean_Elab_Term_getMainModule___rarg(x_3962);
x_3964 = lean_ctor_get(x_3963, 1);
lean_inc(x_3964);
if (lean_is_exclusive(x_3963)) {
 lean_ctor_release(x_3963, 0);
 lean_ctor_release(x_3963, 1);
 x_3965 = x_3963;
} else {
 lean_dec_ref(x_3963);
 x_3965 = lean_box(0);
}
x_3966 = l_Array_empty___closed__1;
x_3967 = lean_array_push(x_3966, x_3946);
x_3968 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3969 = lean_array_push(x_3967, x_3968);
x_3970 = l_Lean_mkTermIdFromIdent___closed__2;
x_3971 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3971, 0, x_3970);
lean_ctor_set(x_3971, 1, x_3969);
x_3972 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_3973 = lean_array_push(x_3972, x_3971);
x_3974 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_3975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3975, 0, x_3974);
lean_ctor_set(x_3975, 1, x_3973);
x_3976 = lean_array_push(x_3966, x_3975);
x_3977 = l_Lean_nullKind___closed__2;
x_3978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3978, 0, x_3977);
lean_ctor_set(x_3978, 1, x_3976);
x_3979 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_3980 = lean_array_push(x_3979, x_3978);
x_3981 = lean_array_push(x_3980, x_3968);
x_3982 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_3983 = lean_array_push(x_3981, x_3982);
x_3984 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_3985 = lean_array_push(x_3983, x_3984);
lean_inc(x_14);
x_3986 = lean_array_push(x_3966, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3987 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3987 = lean_box(0);
}
if (lean_is_scalar(x_3987)) {
 x_3988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3988 = x_3987;
}
lean_ctor_set(x_3988, 0, x_3977);
lean_ctor_set(x_3988, 1, x_3986);
x_3989 = lean_array_push(x_3966, x_3988);
x_3990 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3991 = lean_array_push(x_3989, x_3990);
x_3992 = lean_array_push(x_3991, x_3959);
x_3993 = l_Lean_Parser_Term_matchAlt___closed__2;
x_3994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3994, 0, x_3993);
lean_ctor_set(x_3994, 1, x_3992);
x_3995 = lean_array_push(x_3966, x_3994);
x_3996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3996, 0, x_3977);
lean_ctor_set(x_3996, 1, x_3995);
x_3997 = lean_array_push(x_3985, x_3996);
x_3998 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3999, 0, x_3998);
lean_ctor_set(x_3999, 1, x_3997);
x_4000 = lean_box(x_3943);
if (lean_is_scalar(x_3960)) {
 x_4001 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4001 = x_3960;
}
lean_ctor_set(x_4001, 0, x_3999);
lean_ctor_set(x_4001, 1, x_4000);
if (lean_is_scalar(x_3958)) {
 x_4002 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4002 = x_3958;
}
lean_ctor_set(x_4002, 0, x_3957);
lean_ctor_set(x_4002, 1, x_4001);
if (lean_is_scalar(x_3965)) {
 x_4003 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4003 = x_3965;
}
lean_ctor_set(x_4003, 0, x_4002);
lean_ctor_set(x_4003, 1, x_3964);
return x_4003;
}
else
{
lean_object* x_4004; lean_object* x_4005; lean_object* x_4006; lean_object* x_4007; 
lean_dec(x_3946);
lean_dec(x_14);
lean_dec(x_5);
x_4004 = lean_ctor_get(x_3953, 0);
lean_inc(x_4004);
x_4005 = lean_ctor_get(x_3953, 1);
lean_inc(x_4005);
if (lean_is_exclusive(x_3953)) {
 lean_ctor_release(x_3953, 0);
 lean_ctor_release(x_3953, 1);
 x_4006 = x_3953;
} else {
 lean_dec_ref(x_3953);
 x_4006 = lean_box(0);
}
if (lean_is_scalar(x_4006)) {
 x_4007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4007 = x_4006;
}
lean_ctor_set(x_4007, 0, x_4004);
lean_ctor_set(x_4007, 1, x_4005);
return x_4007;
}
}
else
{
lean_object* x_4008; lean_object* x_4009; lean_object* x_4010; uint8_t x_4011; 
lean_dec(x_14);
x_4008 = lean_ctor_get(x_3944, 0);
lean_inc(x_4008);
lean_dec(x_3944);
x_4009 = lean_ctor_get(x_4008, 0);
lean_inc(x_4009);
x_4010 = lean_ctor_get(x_4008, 1);
lean_inc(x_4010);
lean_dec(x_4008);
x_4011 = l_Lean_Syntax_isNone(x_4010);
lean_dec(x_4010);
if (x_4011 == 0)
{
lean_object* x_4012; lean_object* x_4013; lean_object* x_4014; lean_object* x_4015; lean_object* x_4016; lean_object* x_4017; 
lean_dec(x_4009);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4012 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_4013 = l_Lean_Elab_Term_throwErrorAt___rarg(x_3942, x_4012, x_5, x_6);
lean_dec(x_3942);
x_4014 = lean_ctor_get(x_4013, 0);
lean_inc(x_4014);
x_4015 = lean_ctor_get(x_4013, 1);
lean_inc(x_4015);
if (lean_is_exclusive(x_4013)) {
 lean_ctor_release(x_4013, 0);
 lean_ctor_release(x_4013, 1);
 x_4016 = x_4013;
} else {
 lean_dec_ref(x_4013);
 x_4016 = lean_box(0);
}
if (lean_is_scalar(x_4016)) {
 x_4017 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4017 = x_4016;
}
lean_ctor_set(x_4017, 0, x_4014);
lean_ctor_set(x_4017, 1, x_4015);
return x_4017;
}
else
{
lean_object* x_4018; lean_object* x_4019; lean_object* x_4020; lean_object* x_4021; lean_object* x_4022; 
x_4018 = l_Lean_mkHole(x_3942);
lean_dec(x_3942);
x_4019 = lean_unsigned_to_nat(1u);
x_4020 = lean_nat_add(x_3, x_4019);
lean_dec(x_3);
x_4021 = l_Lean_Elab_Term_mkExplicitBinder(x_4009, x_4018);
x_4022 = lean_array_push(x_4, x_4021);
x_3 = x_4020;
x_4 = x_4022;
goto _start;
}
}
}
else
{
lean_object* x_4024; uint8_t x_4025; 
lean_dec(x_3756);
x_4024 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_4025 = lean_string_dec_eq(x_3754, x_4024);
if (x_4025 == 0)
{
lean_object* x_4026; uint8_t x_4027; 
x_4026 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_4027 = lean_string_dec_eq(x_3754, x_4026);
if (x_4027 == 0)
{
lean_object* x_4028; uint8_t x_4029; 
x_4028 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_4029 = lean_string_dec_eq(x_3754, x_4028);
if (x_4029 == 0)
{
lean_object* x_4030; uint8_t x_4031; 
x_4030 = l_Lean_mkHole___closed__1;
x_4031 = lean_string_dec_eq(x_3754, x_4030);
if (x_4031 == 0)
{
lean_object* x_4032; uint8_t x_4033; 
x_4032 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_4033 = lean_string_dec_eq(x_3754, x_4032);
if (x_4033 == 0)
{
lean_object* x_4034; lean_object* x_4035; lean_object* x_4036; lean_object* x_4037; lean_object* x_4038; uint8_t x_4039; lean_object* x_4040; 
if (lean_is_scalar(x_3764)) {
 x_4034 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_4034 = x_3764;
}
lean_ctor_set(x_4034, 0, x_19);
lean_ctor_set(x_4034, 1, x_3765);
lean_ctor_set_usize(x_4034, 2, x_3763);
if (lean_is_scalar(x_3761)) {
 x_4035 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_4035 = x_3761;
}
lean_ctor_set(x_4035, 0, x_4034);
lean_ctor_set(x_4035, 1, x_3848);
lean_ctor_set_usize(x_4035, 2, x_3760);
if (lean_is_scalar(x_3758)) {
 x_4036 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_4036 = x_3758;
}
lean_ctor_set(x_4036, 0, x_4035);
lean_ctor_set(x_4036, 1, x_3936);
lean_ctor_set_usize(x_4036, 2, x_3757);
x_4037 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_4037, 0, x_4036);
lean_ctor_set(x_4037, 1, x_3754);
lean_ctor_set_usize(x_4037, 2, x_3755);
x_4038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4038, 0, x_4037);
lean_ctor_set(x_4038, 1, x_20);
x_4039 = 1;
lean_inc(x_4038);
x_4040 = l_Lean_Syntax_isTermId_x3f(x_4038, x_4039);
if (lean_obj_tag(x_4040) == 0)
{
lean_object* x_4041; lean_object* x_4042; lean_object* x_4043; lean_object* x_4044; lean_object* x_4045; lean_object* x_4046; lean_object* x_4047; lean_object* x_4048; lean_object* x_4049; 
lean_dec(x_4038);
x_4041 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4042 = lean_ctor_get(x_4041, 0);
lean_inc(x_4042);
x_4043 = lean_ctor_get(x_4041, 1);
lean_inc(x_4043);
lean_dec(x_4041);
x_4044 = lean_unsigned_to_nat(1u);
x_4045 = lean_nat_add(x_3, x_4044);
lean_dec(x_3);
x_4046 = l_Lean_mkHole(x_14);
lean_inc(x_4042);
x_4047 = l_Lean_Elab_Term_mkExplicitBinder(x_4042, x_4046);
x_4048 = lean_array_push(x_4, x_4047);
lean_inc(x_5);
x_4049 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4045, x_4048, x_5, x_4043);
if (lean_obj_tag(x_4049) == 0)
{
lean_object* x_4050; lean_object* x_4051; lean_object* x_4052; lean_object* x_4053; lean_object* x_4054; lean_object* x_4055; lean_object* x_4056; lean_object* x_4057; lean_object* x_4058; lean_object* x_4059; lean_object* x_4060; lean_object* x_4061; lean_object* x_4062; lean_object* x_4063; lean_object* x_4064; lean_object* x_4065; lean_object* x_4066; lean_object* x_4067; lean_object* x_4068; lean_object* x_4069; lean_object* x_4070; lean_object* x_4071; lean_object* x_4072; lean_object* x_4073; lean_object* x_4074; lean_object* x_4075; lean_object* x_4076; lean_object* x_4077; lean_object* x_4078; lean_object* x_4079; lean_object* x_4080; lean_object* x_4081; lean_object* x_4082; lean_object* x_4083; lean_object* x_4084; lean_object* x_4085; lean_object* x_4086; lean_object* x_4087; lean_object* x_4088; lean_object* x_4089; lean_object* x_4090; lean_object* x_4091; lean_object* x_4092; lean_object* x_4093; lean_object* x_4094; lean_object* x_4095; lean_object* x_4096; lean_object* x_4097; lean_object* x_4098; lean_object* x_4099; 
x_4050 = lean_ctor_get(x_4049, 0);
lean_inc(x_4050);
x_4051 = lean_ctor_get(x_4050, 1);
lean_inc(x_4051);
x_4052 = lean_ctor_get(x_4049, 1);
lean_inc(x_4052);
lean_dec(x_4049);
x_4053 = lean_ctor_get(x_4050, 0);
lean_inc(x_4053);
if (lean_is_exclusive(x_4050)) {
 lean_ctor_release(x_4050, 0);
 lean_ctor_release(x_4050, 1);
 x_4054 = x_4050;
} else {
 lean_dec_ref(x_4050);
 x_4054 = lean_box(0);
}
x_4055 = lean_ctor_get(x_4051, 0);
lean_inc(x_4055);
if (lean_is_exclusive(x_4051)) {
 lean_ctor_release(x_4051, 0);
 lean_ctor_release(x_4051, 1);
 x_4056 = x_4051;
} else {
 lean_dec_ref(x_4051);
 x_4056 = lean_box(0);
}
x_4057 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4052);
lean_dec(x_5);
x_4058 = lean_ctor_get(x_4057, 1);
lean_inc(x_4058);
lean_dec(x_4057);
x_4059 = l_Lean_Elab_Term_getMainModule___rarg(x_4058);
x_4060 = lean_ctor_get(x_4059, 1);
lean_inc(x_4060);
if (lean_is_exclusive(x_4059)) {
 lean_ctor_release(x_4059, 0);
 lean_ctor_release(x_4059, 1);
 x_4061 = x_4059;
} else {
 lean_dec_ref(x_4059);
 x_4061 = lean_box(0);
}
x_4062 = l_Array_empty___closed__1;
x_4063 = lean_array_push(x_4062, x_4042);
x_4064 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4065 = lean_array_push(x_4063, x_4064);
x_4066 = l_Lean_mkTermIdFromIdent___closed__2;
x_4067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4067, 0, x_4066);
lean_ctor_set(x_4067, 1, x_4065);
x_4068 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4069 = lean_array_push(x_4068, x_4067);
x_4070 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4071 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4071, 0, x_4070);
lean_ctor_set(x_4071, 1, x_4069);
x_4072 = lean_array_push(x_4062, x_4071);
x_4073 = l_Lean_nullKind___closed__2;
x_4074 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4074, 0, x_4073);
lean_ctor_set(x_4074, 1, x_4072);
x_4075 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4076 = lean_array_push(x_4075, x_4074);
x_4077 = lean_array_push(x_4076, x_4064);
x_4078 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4079 = lean_array_push(x_4077, x_4078);
x_4080 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4081 = lean_array_push(x_4079, x_4080);
lean_inc(x_14);
x_4082 = lean_array_push(x_4062, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4083 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4083 = lean_box(0);
}
if (lean_is_scalar(x_4083)) {
 x_4084 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4084 = x_4083;
}
lean_ctor_set(x_4084, 0, x_4073);
lean_ctor_set(x_4084, 1, x_4082);
x_4085 = lean_array_push(x_4062, x_4084);
x_4086 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4087 = lean_array_push(x_4085, x_4086);
x_4088 = lean_array_push(x_4087, x_4055);
x_4089 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4090, 0, x_4089);
lean_ctor_set(x_4090, 1, x_4088);
x_4091 = lean_array_push(x_4062, x_4090);
x_4092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4092, 0, x_4073);
lean_ctor_set(x_4092, 1, x_4091);
x_4093 = lean_array_push(x_4081, x_4092);
x_4094 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4095, 0, x_4094);
lean_ctor_set(x_4095, 1, x_4093);
x_4096 = lean_box(x_4039);
if (lean_is_scalar(x_4056)) {
 x_4097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4097 = x_4056;
}
lean_ctor_set(x_4097, 0, x_4095);
lean_ctor_set(x_4097, 1, x_4096);
if (lean_is_scalar(x_4054)) {
 x_4098 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4098 = x_4054;
}
lean_ctor_set(x_4098, 0, x_4053);
lean_ctor_set(x_4098, 1, x_4097);
if (lean_is_scalar(x_4061)) {
 x_4099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4099 = x_4061;
}
lean_ctor_set(x_4099, 0, x_4098);
lean_ctor_set(x_4099, 1, x_4060);
return x_4099;
}
else
{
lean_object* x_4100; lean_object* x_4101; lean_object* x_4102; lean_object* x_4103; 
lean_dec(x_4042);
lean_dec(x_14);
lean_dec(x_5);
x_4100 = lean_ctor_get(x_4049, 0);
lean_inc(x_4100);
x_4101 = lean_ctor_get(x_4049, 1);
lean_inc(x_4101);
if (lean_is_exclusive(x_4049)) {
 lean_ctor_release(x_4049, 0);
 lean_ctor_release(x_4049, 1);
 x_4102 = x_4049;
} else {
 lean_dec_ref(x_4049);
 x_4102 = lean_box(0);
}
if (lean_is_scalar(x_4102)) {
 x_4103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4103 = x_4102;
}
lean_ctor_set(x_4103, 0, x_4100);
lean_ctor_set(x_4103, 1, x_4101);
return x_4103;
}
}
else
{
lean_object* x_4104; lean_object* x_4105; lean_object* x_4106; uint8_t x_4107; 
lean_dec(x_14);
x_4104 = lean_ctor_get(x_4040, 0);
lean_inc(x_4104);
lean_dec(x_4040);
x_4105 = lean_ctor_get(x_4104, 0);
lean_inc(x_4105);
x_4106 = lean_ctor_get(x_4104, 1);
lean_inc(x_4106);
lean_dec(x_4104);
x_4107 = l_Lean_Syntax_isNone(x_4106);
lean_dec(x_4106);
if (x_4107 == 0)
{
lean_object* x_4108; lean_object* x_4109; lean_object* x_4110; lean_object* x_4111; lean_object* x_4112; lean_object* x_4113; 
lean_dec(x_4105);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4108 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_4109 = l_Lean_Elab_Term_throwErrorAt___rarg(x_4038, x_4108, x_5, x_6);
lean_dec(x_4038);
x_4110 = lean_ctor_get(x_4109, 0);
lean_inc(x_4110);
x_4111 = lean_ctor_get(x_4109, 1);
lean_inc(x_4111);
if (lean_is_exclusive(x_4109)) {
 lean_ctor_release(x_4109, 0);
 lean_ctor_release(x_4109, 1);
 x_4112 = x_4109;
} else {
 lean_dec_ref(x_4109);
 x_4112 = lean_box(0);
}
if (lean_is_scalar(x_4112)) {
 x_4113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4113 = x_4112;
}
lean_ctor_set(x_4113, 0, x_4110);
lean_ctor_set(x_4113, 1, x_4111);
return x_4113;
}
else
{
lean_object* x_4114; lean_object* x_4115; lean_object* x_4116; lean_object* x_4117; lean_object* x_4118; 
x_4114 = l_Lean_mkHole(x_4038);
lean_dec(x_4038);
x_4115 = lean_unsigned_to_nat(1u);
x_4116 = lean_nat_add(x_3, x_4115);
lean_dec(x_3);
x_4117 = l_Lean_Elab_Term_mkExplicitBinder(x_4105, x_4114);
x_4118 = lean_array_push(x_4, x_4117);
x_3 = x_4116;
x_4 = x_4118;
goto _start;
}
}
}
else
{
lean_object* x_4120; lean_object* x_4121; uint8_t x_4122; 
lean_dec(x_3764);
lean_dec(x_3761);
lean_dec(x_3758);
lean_dec(x_3754);
lean_dec(x_20);
x_4120 = lean_unsigned_to_nat(1u);
x_4121 = l_Lean_Syntax_getArg(x_14, x_4120);
x_4122 = l_Lean_Syntax_isNone(x_4121);
if (x_4122 == 0)
{
lean_object* x_4123; lean_object* x_4124; lean_object* x_4125; uint8_t x_4126; 
x_4123 = lean_unsigned_to_nat(0u);
x_4124 = l_Lean_Syntax_getArg(x_4121, x_4123);
x_4125 = l_Lean_Syntax_getArg(x_4121, x_4120);
lean_dec(x_4121);
x_4126 = l_Lean_Syntax_isNone(x_4125);
if (x_4126 == 0)
{
lean_object* x_4127; lean_object* x_4128; lean_object* x_4129; lean_object* x_4130; lean_object* x_4131; lean_object* x_4132; lean_object* x_4133; uint8_t x_4134; 
x_4127 = l_Lean_Syntax_getArg(x_4125, x_4123);
lean_dec(x_4125);
lean_inc(x_4127);
x_4128 = l_Lean_Syntax_getKind(x_4127);
x_4129 = lean_name_mk_string(x_19, x_3765);
x_4130 = lean_name_mk_string(x_4129, x_3848);
x_4131 = lean_name_mk_string(x_4130, x_3936);
x_4132 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_4133 = lean_name_mk_string(x_4131, x_4132);
x_4134 = lean_name_eq(x_4128, x_4133);
lean_dec(x_4133);
lean_dec(x_4128);
if (x_4134 == 0)
{
lean_object* x_4135; lean_object* x_4136; lean_object* x_4137; lean_object* x_4138; lean_object* x_4139; lean_object* x_4140; lean_object* x_4141; lean_object* x_4142; 
lean_dec(x_4127);
lean_dec(x_4124);
x_4135 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4136 = lean_ctor_get(x_4135, 0);
lean_inc(x_4136);
x_4137 = lean_ctor_get(x_4135, 1);
lean_inc(x_4137);
lean_dec(x_4135);
x_4138 = lean_nat_add(x_3, x_4120);
lean_dec(x_3);
x_4139 = l_Lean_mkHole(x_14);
lean_inc(x_4136);
x_4140 = l_Lean_Elab_Term_mkExplicitBinder(x_4136, x_4139);
x_4141 = lean_array_push(x_4, x_4140);
lean_inc(x_5);
x_4142 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4138, x_4141, x_5, x_4137);
if (lean_obj_tag(x_4142) == 0)
{
lean_object* x_4143; lean_object* x_4144; lean_object* x_4145; lean_object* x_4146; lean_object* x_4147; lean_object* x_4148; lean_object* x_4149; lean_object* x_4150; lean_object* x_4151; lean_object* x_4152; lean_object* x_4153; lean_object* x_4154; lean_object* x_4155; lean_object* x_4156; lean_object* x_4157; lean_object* x_4158; lean_object* x_4159; lean_object* x_4160; lean_object* x_4161; lean_object* x_4162; lean_object* x_4163; lean_object* x_4164; lean_object* x_4165; lean_object* x_4166; lean_object* x_4167; lean_object* x_4168; lean_object* x_4169; lean_object* x_4170; lean_object* x_4171; lean_object* x_4172; lean_object* x_4173; lean_object* x_4174; lean_object* x_4175; lean_object* x_4176; lean_object* x_4177; lean_object* x_4178; lean_object* x_4179; lean_object* x_4180; lean_object* x_4181; lean_object* x_4182; lean_object* x_4183; lean_object* x_4184; lean_object* x_4185; lean_object* x_4186; lean_object* x_4187; lean_object* x_4188; uint8_t x_4189; lean_object* x_4190; lean_object* x_4191; lean_object* x_4192; lean_object* x_4193; 
x_4143 = lean_ctor_get(x_4142, 0);
lean_inc(x_4143);
x_4144 = lean_ctor_get(x_4143, 1);
lean_inc(x_4144);
x_4145 = lean_ctor_get(x_4142, 1);
lean_inc(x_4145);
lean_dec(x_4142);
x_4146 = lean_ctor_get(x_4143, 0);
lean_inc(x_4146);
if (lean_is_exclusive(x_4143)) {
 lean_ctor_release(x_4143, 0);
 lean_ctor_release(x_4143, 1);
 x_4147 = x_4143;
} else {
 lean_dec_ref(x_4143);
 x_4147 = lean_box(0);
}
x_4148 = lean_ctor_get(x_4144, 0);
lean_inc(x_4148);
if (lean_is_exclusive(x_4144)) {
 lean_ctor_release(x_4144, 0);
 lean_ctor_release(x_4144, 1);
 x_4149 = x_4144;
} else {
 lean_dec_ref(x_4144);
 x_4149 = lean_box(0);
}
x_4150 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4145);
lean_dec(x_5);
x_4151 = lean_ctor_get(x_4150, 1);
lean_inc(x_4151);
lean_dec(x_4150);
x_4152 = l_Lean_Elab_Term_getMainModule___rarg(x_4151);
x_4153 = lean_ctor_get(x_4152, 1);
lean_inc(x_4153);
if (lean_is_exclusive(x_4152)) {
 lean_ctor_release(x_4152, 0);
 lean_ctor_release(x_4152, 1);
 x_4154 = x_4152;
} else {
 lean_dec_ref(x_4152);
 x_4154 = lean_box(0);
}
x_4155 = l_Array_empty___closed__1;
x_4156 = lean_array_push(x_4155, x_4136);
x_4157 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4158 = lean_array_push(x_4156, x_4157);
x_4159 = l_Lean_mkTermIdFromIdent___closed__2;
x_4160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4160, 0, x_4159);
lean_ctor_set(x_4160, 1, x_4158);
x_4161 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4162 = lean_array_push(x_4161, x_4160);
x_4163 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4164, 0, x_4163);
lean_ctor_set(x_4164, 1, x_4162);
x_4165 = lean_array_push(x_4155, x_4164);
x_4166 = l_Lean_nullKind___closed__2;
x_4167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4167, 0, x_4166);
lean_ctor_set(x_4167, 1, x_4165);
x_4168 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4169 = lean_array_push(x_4168, x_4167);
x_4170 = lean_array_push(x_4169, x_4157);
x_4171 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4172 = lean_array_push(x_4170, x_4171);
x_4173 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4174 = lean_array_push(x_4172, x_4173);
lean_inc(x_14);
x_4175 = lean_array_push(x_4155, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4176 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4176 = lean_box(0);
}
if (lean_is_scalar(x_4176)) {
 x_4177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4177 = x_4176;
}
lean_ctor_set(x_4177, 0, x_4166);
lean_ctor_set(x_4177, 1, x_4175);
x_4178 = lean_array_push(x_4155, x_4177);
x_4179 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4180 = lean_array_push(x_4178, x_4179);
x_4181 = lean_array_push(x_4180, x_4148);
x_4182 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4183, 0, x_4182);
lean_ctor_set(x_4183, 1, x_4181);
x_4184 = lean_array_push(x_4155, x_4183);
x_4185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4185, 0, x_4166);
lean_ctor_set(x_4185, 1, x_4184);
x_4186 = lean_array_push(x_4174, x_4185);
x_4187 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4188, 0, x_4187);
lean_ctor_set(x_4188, 1, x_4186);
x_4189 = 1;
x_4190 = lean_box(x_4189);
if (lean_is_scalar(x_4149)) {
 x_4191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4191 = x_4149;
}
lean_ctor_set(x_4191, 0, x_4188);
lean_ctor_set(x_4191, 1, x_4190);
if (lean_is_scalar(x_4147)) {
 x_4192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4192 = x_4147;
}
lean_ctor_set(x_4192, 0, x_4146);
lean_ctor_set(x_4192, 1, x_4191);
if (lean_is_scalar(x_4154)) {
 x_4193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4193 = x_4154;
}
lean_ctor_set(x_4193, 0, x_4192);
lean_ctor_set(x_4193, 1, x_4153);
return x_4193;
}
else
{
lean_object* x_4194; lean_object* x_4195; lean_object* x_4196; lean_object* x_4197; 
lean_dec(x_4136);
lean_dec(x_14);
lean_dec(x_5);
x_4194 = lean_ctor_get(x_4142, 0);
lean_inc(x_4194);
x_4195 = lean_ctor_get(x_4142, 1);
lean_inc(x_4195);
if (lean_is_exclusive(x_4142)) {
 lean_ctor_release(x_4142, 0);
 lean_ctor_release(x_4142, 1);
 x_4196 = x_4142;
} else {
 lean_dec_ref(x_4142);
 x_4196 = lean_box(0);
}
if (lean_is_scalar(x_4196)) {
 x_4197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4197 = x_4196;
}
lean_ctor_set(x_4197, 0, x_4194);
lean_ctor_set(x_4197, 1, x_4195);
return x_4197;
}
}
else
{
lean_object* x_4198; lean_object* x_4199; lean_object* x_4200; 
x_4198 = l_Lean_Syntax_getArg(x_4127, x_4120);
lean_dec(x_4127);
x_4199 = l___private_Lean_Elab_Binders_10__getFunBinderIds_x3f(x_4124, x_5, x_6);
x_4200 = lean_ctor_get(x_4199, 0);
lean_inc(x_4200);
if (lean_obj_tag(x_4200) == 0)
{
lean_object* x_4201; lean_object* x_4202; lean_object* x_4203; lean_object* x_4204; lean_object* x_4205; lean_object* x_4206; lean_object* x_4207; lean_object* x_4208; lean_object* x_4209; 
lean_dec(x_4198);
x_4201 = lean_ctor_get(x_4199, 1);
lean_inc(x_4201);
lean_dec(x_4199);
x_4202 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_4201);
x_4203 = lean_ctor_get(x_4202, 0);
lean_inc(x_4203);
x_4204 = lean_ctor_get(x_4202, 1);
lean_inc(x_4204);
lean_dec(x_4202);
x_4205 = lean_nat_add(x_3, x_4120);
lean_dec(x_3);
x_4206 = l_Lean_mkHole(x_14);
lean_inc(x_4203);
x_4207 = l_Lean_Elab_Term_mkExplicitBinder(x_4203, x_4206);
x_4208 = lean_array_push(x_4, x_4207);
lean_inc(x_5);
x_4209 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4205, x_4208, x_5, x_4204);
if (lean_obj_tag(x_4209) == 0)
{
lean_object* x_4210; lean_object* x_4211; lean_object* x_4212; lean_object* x_4213; lean_object* x_4214; lean_object* x_4215; lean_object* x_4216; lean_object* x_4217; lean_object* x_4218; lean_object* x_4219; lean_object* x_4220; lean_object* x_4221; lean_object* x_4222; lean_object* x_4223; lean_object* x_4224; lean_object* x_4225; lean_object* x_4226; lean_object* x_4227; lean_object* x_4228; lean_object* x_4229; lean_object* x_4230; lean_object* x_4231; lean_object* x_4232; lean_object* x_4233; lean_object* x_4234; lean_object* x_4235; lean_object* x_4236; lean_object* x_4237; lean_object* x_4238; lean_object* x_4239; lean_object* x_4240; lean_object* x_4241; lean_object* x_4242; lean_object* x_4243; lean_object* x_4244; lean_object* x_4245; lean_object* x_4246; lean_object* x_4247; lean_object* x_4248; lean_object* x_4249; lean_object* x_4250; lean_object* x_4251; lean_object* x_4252; lean_object* x_4253; lean_object* x_4254; lean_object* x_4255; uint8_t x_4256; lean_object* x_4257; lean_object* x_4258; lean_object* x_4259; lean_object* x_4260; 
x_4210 = lean_ctor_get(x_4209, 0);
lean_inc(x_4210);
x_4211 = lean_ctor_get(x_4210, 1);
lean_inc(x_4211);
x_4212 = lean_ctor_get(x_4209, 1);
lean_inc(x_4212);
lean_dec(x_4209);
x_4213 = lean_ctor_get(x_4210, 0);
lean_inc(x_4213);
if (lean_is_exclusive(x_4210)) {
 lean_ctor_release(x_4210, 0);
 lean_ctor_release(x_4210, 1);
 x_4214 = x_4210;
} else {
 lean_dec_ref(x_4210);
 x_4214 = lean_box(0);
}
x_4215 = lean_ctor_get(x_4211, 0);
lean_inc(x_4215);
if (lean_is_exclusive(x_4211)) {
 lean_ctor_release(x_4211, 0);
 lean_ctor_release(x_4211, 1);
 x_4216 = x_4211;
} else {
 lean_dec_ref(x_4211);
 x_4216 = lean_box(0);
}
x_4217 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4212);
lean_dec(x_5);
x_4218 = lean_ctor_get(x_4217, 1);
lean_inc(x_4218);
lean_dec(x_4217);
x_4219 = l_Lean_Elab_Term_getMainModule___rarg(x_4218);
x_4220 = lean_ctor_get(x_4219, 1);
lean_inc(x_4220);
if (lean_is_exclusive(x_4219)) {
 lean_ctor_release(x_4219, 0);
 lean_ctor_release(x_4219, 1);
 x_4221 = x_4219;
} else {
 lean_dec_ref(x_4219);
 x_4221 = lean_box(0);
}
x_4222 = l_Array_empty___closed__1;
x_4223 = lean_array_push(x_4222, x_4203);
x_4224 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4225 = lean_array_push(x_4223, x_4224);
x_4226 = l_Lean_mkTermIdFromIdent___closed__2;
x_4227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4227, 0, x_4226);
lean_ctor_set(x_4227, 1, x_4225);
x_4228 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4229 = lean_array_push(x_4228, x_4227);
x_4230 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4231, 0, x_4230);
lean_ctor_set(x_4231, 1, x_4229);
x_4232 = lean_array_push(x_4222, x_4231);
x_4233 = l_Lean_nullKind___closed__2;
x_4234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4234, 0, x_4233);
lean_ctor_set(x_4234, 1, x_4232);
x_4235 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4236 = lean_array_push(x_4235, x_4234);
x_4237 = lean_array_push(x_4236, x_4224);
x_4238 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4239 = lean_array_push(x_4237, x_4238);
x_4240 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4241 = lean_array_push(x_4239, x_4240);
lean_inc(x_14);
x_4242 = lean_array_push(x_4222, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4243 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4243 = lean_box(0);
}
if (lean_is_scalar(x_4243)) {
 x_4244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4244 = x_4243;
}
lean_ctor_set(x_4244, 0, x_4233);
lean_ctor_set(x_4244, 1, x_4242);
x_4245 = lean_array_push(x_4222, x_4244);
x_4246 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4247 = lean_array_push(x_4245, x_4246);
x_4248 = lean_array_push(x_4247, x_4215);
x_4249 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4250, 0, x_4249);
lean_ctor_set(x_4250, 1, x_4248);
x_4251 = lean_array_push(x_4222, x_4250);
x_4252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4252, 0, x_4233);
lean_ctor_set(x_4252, 1, x_4251);
x_4253 = lean_array_push(x_4241, x_4252);
x_4254 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4255, 0, x_4254);
lean_ctor_set(x_4255, 1, x_4253);
x_4256 = 1;
x_4257 = lean_box(x_4256);
if (lean_is_scalar(x_4216)) {
 x_4258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4258 = x_4216;
}
lean_ctor_set(x_4258, 0, x_4255);
lean_ctor_set(x_4258, 1, x_4257);
if (lean_is_scalar(x_4214)) {
 x_4259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4259 = x_4214;
}
lean_ctor_set(x_4259, 0, x_4213);
lean_ctor_set(x_4259, 1, x_4258);
if (lean_is_scalar(x_4221)) {
 x_4260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4260 = x_4221;
}
lean_ctor_set(x_4260, 0, x_4259);
lean_ctor_set(x_4260, 1, x_4220);
return x_4260;
}
else
{
lean_object* x_4261; lean_object* x_4262; lean_object* x_4263; lean_object* x_4264; 
lean_dec(x_4203);
lean_dec(x_14);
lean_dec(x_5);
x_4261 = lean_ctor_get(x_4209, 0);
lean_inc(x_4261);
x_4262 = lean_ctor_get(x_4209, 1);
lean_inc(x_4262);
if (lean_is_exclusive(x_4209)) {
 lean_ctor_release(x_4209, 0);
 lean_ctor_release(x_4209, 1);
 x_4263 = x_4209;
} else {
 lean_dec_ref(x_4209);
 x_4263 = lean_box(0);
}
if (lean_is_scalar(x_4263)) {
 x_4264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4264 = x_4263;
}
lean_ctor_set(x_4264, 0, x_4261);
lean_ctor_set(x_4264, 1, x_4262);
return x_4264;
}
}
else
{
lean_object* x_4265; lean_object* x_4266; lean_object* x_4267; lean_object* x_4268; lean_object* x_4269; lean_object* x_4270; lean_object* x_4271; 
lean_dec(x_14);
x_4265 = lean_ctor_get(x_4199, 1);
lean_inc(x_4265);
lean_dec(x_4199);
x_4266 = lean_ctor_get(x_4200, 0);
lean_inc(x_4266);
lean_dec(x_4200);
x_4267 = lean_nat_add(x_3, x_4120);
lean_dec(x_3);
x_4268 = x_4266;
x_4269 = l_Array_umapMAux___main___at___private_Lean_Elab_Binders_11__expandFunBindersAux___main___spec__1(x_4198, x_4123, x_4268);
x_4270 = x_4269;
x_4271 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_4270, x_4270, x_4123, x_4);
lean_dec(x_4270);
x_3 = x_4267;
x_4 = x_4271;
x_6 = x_4265;
goto _start;
}
}
}
else
{
lean_object* x_4273; lean_object* x_4274; lean_object* x_4275; lean_object* x_4276; lean_object* x_4277; lean_object* x_4278; lean_object* x_4279; lean_object* x_4280; 
lean_dec(x_4125);
lean_dec(x_4124);
x_4273 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4274 = lean_ctor_get(x_4273, 0);
lean_inc(x_4274);
x_4275 = lean_ctor_get(x_4273, 1);
lean_inc(x_4275);
lean_dec(x_4273);
x_4276 = lean_nat_add(x_3, x_4120);
lean_dec(x_3);
x_4277 = l_Lean_mkHole(x_14);
lean_inc(x_4274);
x_4278 = l_Lean_Elab_Term_mkExplicitBinder(x_4274, x_4277);
x_4279 = lean_array_push(x_4, x_4278);
lean_inc(x_5);
x_4280 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4276, x_4279, x_5, x_4275);
if (lean_obj_tag(x_4280) == 0)
{
lean_object* x_4281; lean_object* x_4282; lean_object* x_4283; lean_object* x_4284; lean_object* x_4285; lean_object* x_4286; lean_object* x_4287; lean_object* x_4288; lean_object* x_4289; lean_object* x_4290; lean_object* x_4291; lean_object* x_4292; lean_object* x_4293; lean_object* x_4294; lean_object* x_4295; lean_object* x_4296; lean_object* x_4297; lean_object* x_4298; lean_object* x_4299; lean_object* x_4300; lean_object* x_4301; lean_object* x_4302; lean_object* x_4303; lean_object* x_4304; lean_object* x_4305; lean_object* x_4306; lean_object* x_4307; lean_object* x_4308; lean_object* x_4309; lean_object* x_4310; lean_object* x_4311; lean_object* x_4312; lean_object* x_4313; lean_object* x_4314; lean_object* x_4315; lean_object* x_4316; lean_object* x_4317; lean_object* x_4318; lean_object* x_4319; lean_object* x_4320; lean_object* x_4321; lean_object* x_4322; lean_object* x_4323; lean_object* x_4324; lean_object* x_4325; lean_object* x_4326; uint8_t x_4327; lean_object* x_4328; lean_object* x_4329; lean_object* x_4330; lean_object* x_4331; 
x_4281 = lean_ctor_get(x_4280, 0);
lean_inc(x_4281);
x_4282 = lean_ctor_get(x_4281, 1);
lean_inc(x_4282);
x_4283 = lean_ctor_get(x_4280, 1);
lean_inc(x_4283);
lean_dec(x_4280);
x_4284 = lean_ctor_get(x_4281, 0);
lean_inc(x_4284);
if (lean_is_exclusive(x_4281)) {
 lean_ctor_release(x_4281, 0);
 lean_ctor_release(x_4281, 1);
 x_4285 = x_4281;
} else {
 lean_dec_ref(x_4281);
 x_4285 = lean_box(0);
}
x_4286 = lean_ctor_get(x_4282, 0);
lean_inc(x_4286);
if (lean_is_exclusive(x_4282)) {
 lean_ctor_release(x_4282, 0);
 lean_ctor_release(x_4282, 1);
 x_4287 = x_4282;
} else {
 lean_dec_ref(x_4282);
 x_4287 = lean_box(0);
}
x_4288 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4283);
lean_dec(x_5);
x_4289 = lean_ctor_get(x_4288, 1);
lean_inc(x_4289);
lean_dec(x_4288);
x_4290 = l_Lean_Elab_Term_getMainModule___rarg(x_4289);
x_4291 = lean_ctor_get(x_4290, 1);
lean_inc(x_4291);
if (lean_is_exclusive(x_4290)) {
 lean_ctor_release(x_4290, 0);
 lean_ctor_release(x_4290, 1);
 x_4292 = x_4290;
} else {
 lean_dec_ref(x_4290);
 x_4292 = lean_box(0);
}
x_4293 = l_Array_empty___closed__1;
x_4294 = lean_array_push(x_4293, x_4274);
x_4295 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4296 = lean_array_push(x_4294, x_4295);
x_4297 = l_Lean_mkTermIdFromIdent___closed__2;
x_4298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4298, 0, x_4297);
lean_ctor_set(x_4298, 1, x_4296);
x_4299 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4300 = lean_array_push(x_4299, x_4298);
x_4301 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4302, 0, x_4301);
lean_ctor_set(x_4302, 1, x_4300);
x_4303 = lean_array_push(x_4293, x_4302);
x_4304 = l_Lean_nullKind___closed__2;
x_4305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4305, 0, x_4304);
lean_ctor_set(x_4305, 1, x_4303);
x_4306 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4307 = lean_array_push(x_4306, x_4305);
x_4308 = lean_array_push(x_4307, x_4295);
x_4309 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4310 = lean_array_push(x_4308, x_4309);
x_4311 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4312 = lean_array_push(x_4310, x_4311);
lean_inc(x_14);
x_4313 = lean_array_push(x_4293, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4314 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4314 = lean_box(0);
}
if (lean_is_scalar(x_4314)) {
 x_4315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4315 = x_4314;
}
lean_ctor_set(x_4315, 0, x_4304);
lean_ctor_set(x_4315, 1, x_4313);
x_4316 = lean_array_push(x_4293, x_4315);
x_4317 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4318 = lean_array_push(x_4316, x_4317);
x_4319 = lean_array_push(x_4318, x_4286);
x_4320 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4321, 0, x_4320);
lean_ctor_set(x_4321, 1, x_4319);
x_4322 = lean_array_push(x_4293, x_4321);
x_4323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4323, 0, x_4304);
lean_ctor_set(x_4323, 1, x_4322);
x_4324 = lean_array_push(x_4312, x_4323);
x_4325 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4326, 0, x_4325);
lean_ctor_set(x_4326, 1, x_4324);
x_4327 = 1;
x_4328 = lean_box(x_4327);
if (lean_is_scalar(x_4287)) {
 x_4329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4329 = x_4287;
}
lean_ctor_set(x_4329, 0, x_4326);
lean_ctor_set(x_4329, 1, x_4328);
if (lean_is_scalar(x_4285)) {
 x_4330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4330 = x_4285;
}
lean_ctor_set(x_4330, 0, x_4284);
lean_ctor_set(x_4330, 1, x_4329);
if (lean_is_scalar(x_4292)) {
 x_4331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4331 = x_4292;
}
lean_ctor_set(x_4331, 0, x_4330);
lean_ctor_set(x_4331, 1, x_4291);
return x_4331;
}
else
{
lean_object* x_4332; lean_object* x_4333; lean_object* x_4334; lean_object* x_4335; 
lean_dec(x_4274);
lean_dec(x_14);
lean_dec(x_5);
x_4332 = lean_ctor_get(x_4280, 0);
lean_inc(x_4332);
x_4333 = lean_ctor_get(x_4280, 1);
lean_inc(x_4333);
if (lean_is_exclusive(x_4280)) {
 lean_ctor_release(x_4280, 0);
 lean_ctor_release(x_4280, 1);
 x_4334 = x_4280;
} else {
 lean_dec_ref(x_4280);
 x_4334 = lean_box(0);
}
if (lean_is_scalar(x_4334)) {
 x_4335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4335 = x_4334;
}
lean_ctor_set(x_4335, 0, x_4332);
lean_ctor_set(x_4335, 1, x_4333);
return x_4335;
}
}
}
else
{
lean_object* x_4336; lean_object* x_4337; lean_object* x_4338; lean_object* x_4339; lean_object* x_4340; lean_object* x_4341; lean_object* x_4342; lean_object* x_4343; 
lean_dec(x_4121);
x_4336 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4337 = lean_ctor_get(x_4336, 0);
lean_inc(x_4337);
x_4338 = lean_ctor_get(x_4336, 1);
lean_inc(x_4338);
lean_dec(x_4336);
x_4339 = lean_nat_add(x_3, x_4120);
lean_dec(x_3);
x_4340 = l_Lean_mkHole(x_14);
lean_inc(x_4337);
x_4341 = l_Lean_Elab_Term_mkExplicitBinder(x_4337, x_4340);
x_4342 = lean_array_push(x_4, x_4341);
lean_inc(x_5);
x_4343 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4339, x_4342, x_5, x_4338);
if (lean_obj_tag(x_4343) == 0)
{
lean_object* x_4344; lean_object* x_4345; lean_object* x_4346; lean_object* x_4347; lean_object* x_4348; lean_object* x_4349; lean_object* x_4350; lean_object* x_4351; lean_object* x_4352; lean_object* x_4353; lean_object* x_4354; lean_object* x_4355; lean_object* x_4356; lean_object* x_4357; lean_object* x_4358; lean_object* x_4359; lean_object* x_4360; lean_object* x_4361; lean_object* x_4362; lean_object* x_4363; lean_object* x_4364; lean_object* x_4365; lean_object* x_4366; lean_object* x_4367; lean_object* x_4368; lean_object* x_4369; lean_object* x_4370; lean_object* x_4371; lean_object* x_4372; lean_object* x_4373; lean_object* x_4374; lean_object* x_4375; lean_object* x_4376; lean_object* x_4377; lean_object* x_4378; lean_object* x_4379; lean_object* x_4380; lean_object* x_4381; lean_object* x_4382; lean_object* x_4383; lean_object* x_4384; lean_object* x_4385; lean_object* x_4386; lean_object* x_4387; lean_object* x_4388; lean_object* x_4389; uint8_t x_4390; lean_object* x_4391; lean_object* x_4392; lean_object* x_4393; lean_object* x_4394; 
x_4344 = lean_ctor_get(x_4343, 0);
lean_inc(x_4344);
x_4345 = lean_ctor_get(x_4344, 1);
lean_inc(x_4345);
x_4346 = lean_ctor_get(x_4343, 1);
lean_inc(x_4346);
lean_dec(x_4343);
x_4347 = lean_ctor_get(x_4344, 0);
lean_inc(x_4347);
if (lean_is_exclusive(x_4344)) {
 lean_ctor_release(x_4344, 0);
 lean_ctor_release(x_4344, 1);
 x_4348 = x_4344;
} else {
 lean_dec_ref(x_4344);
 x_4348 = lean_box(0);
}
x_4349 = lean_ctor_get(x_4345, 0);
lean_inc(x_4349);
if (lean_is_exclusive(x_4345)) {
 lean_ctor_release(x_4345, 0);
 lean_ctor_release(x_4345, 1);
 x_4350 = x_4345;
} else {
 lean_dec_ref(x_4345);
 x_4350 = lean_box(0);
}
x_4351 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4346);
lean_dec(x_5);
x_4352 = lean_ctor_get(x_4351, 1);
lean_inc(x_4352);
lean_dec(x_4351);
x_4353 = l_Lean_Elab_Term_getMainModule___rarg(x_4352);
x_4354 = lean_ctor_get(x_4353, 1);
lean_inc(x_4354);
if (lean_is_exclusive(x_4353)) {
 lean_ctor_release(x_4353, 0);
 lean_ctor_release(x_4353, 1);
 x_4355 = x_4353;
} else {
 lean_dec_ref(x_4353);
 x_4355 = lean_box(0);
}
x_4356 = l_Array_empty___closed__1;
x_4357 = lean_array_push(x_4356, x_4337);
x_4358 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4359 = lean_array_push(x_4357, x_4358);
x_4360 = l_Lean_mkTermIdFromIdent___closed__2;
x_4361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4361, 0, x_4360);
lean_ctor_set(x_4361, 1, x_4359);
x_4362 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4363 = lean_array_push(x_4362, x_4361);
x_4364 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4365, 0, x_4364);
lean_ctor_set(x_4365, 1, x_4363);
x_4366 = lean_array_push(x_4356, x_4365);
x_4367 = l_Lean_nullKind___closed__2;
x_4368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4368, 0, x_4367);
lean_ctor_set(x_4368, 1, x_4366);
x_4369 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4370 = lean_array_push(x_4369, x_4368);
x_4371 = lean_array_push(x_4370, x_4358);
x_4372 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4373 = lean_array_push(x_4371, x_4372);
x_4374 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4375 = lean_array_push(x_4373, x_4374);
lean_inc(x_14);
x_4376 = lean_array_push(x_4356, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4377 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4377 = lean_box(0);
}
if (lean_is_scalar(x_4377)) {
 x_4378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4378 = x_4377;
}
lean_ctor_set(x_4378, 0, x_4367);
lean_ctor_set(x_4378, 1, x_4376);
x_4379 = lean_array_push(x_4356, x_4378);
x_4380 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4381 = lean_array_push(x_4379, x_4380);
x_4382 = lean_array_push(x_4381, x_4349);
x_4383 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4384, 0, x_4383);
lean_ctor_set(x_4384, 1, x_4382);
x_4385 = lean_array_push(x_4356, x_4384);
x_4386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4386, 0, x_4367);
lean_ctor_set(x_4386, 1, x_4385);
x_4387 = lean_array_push(x_4375, x_4386);
x_4388 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4389, 0, x_4388);
lean_ctor_set(x_4389, 1, x_4387);
x_4390 = 1;
x_4391 = lean_box(x_4390);
if (lean_is_scalar(x_4350)) {
 x_4392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4392 = x_4350;
}
lean_ctor_set(x_4392, 0, x_4389);
lean_ctor_set(x_4392, 1, x_4391);
if (lean_is_scalar(x_4348)) {
 x_4393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4393 = x_4348;
}
lean_ctor_set(x_4393, 0, x_4347);
lean_ctor_set(x_4393, 1, x_4392);
if (lean_is_scalar(x_4355)) {
 x_4394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4394 = x_4355;
}
lean_ctor_set(x_4394, 0, x_4393);
lean_ctor_set(x_4394, 1, x_4354);
return x_4394;
}
else
{
lean_object* x_4395; lean_object* x_4396; lean_object* x_4397; lean_object* x_4398; 
lean_dec(x_4337);
lean_dec(x_14);
lean_dec(x_5);
x_4395 = lean_ctor_get(x_4343, 0);
lean_inc(x_4395);
x_4396 = lean_ctor_get(x_4343, 1);
lean_inc(x_4396);
if (lean_is_exclusive(x_4343)) {
 lean_ctor_release(x_4343, 0);
 lean_ctor_release(x_4343, 1);
 x_4397 = x_4343;
} else {
 lean_dec_ref(x_4343);
 x_4397 = lean_box(0);
}
if (lean_is_scalar(x_4397)) {
 x_4398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4398 = x_4397;
}
lean_ctor_set(x_4398, 0, x_4395);
lean_ctor_set(x_4398, 1, x_4396);
return x_4398;
}
}
}
}
else
{
lean_object* x_4399; lean_object* x_4400; lean_object* x_4401; lean_object* x_4402; lean_object* x_4403; lean_object* x_4404; lean_object* x_4405; 
lean_dec(x_3764);
lean_dec(x_3761);
lean_dec(x_3758);
lean_dec(x_3754);
lean_dec(x_20);
x_4399 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4400 = lean_ctor_get(x_4399, 0);
lean_inc(x_4400);
x_4401 = lean_ctor_get(x_4399, 1);
lean_inc(x_4401);
lean_dec(x_4399);
x_4402 = lean_unsigned_to_nat(1u);
x_4403 = lean_nat_add(x_3, x_4402);
lean_dec(x_3);
x_4404 = l_Lean_Elab_Term_mkExplicitBinder(x_4400, x_14);
x_4405 = lean_array_push(x_4, x_4404);
x_3 = x_4403;
x_4 = x_4405;
x_6 = x_4401;
goto _start;
}
}
else
{
lean_object* x_4407; lean_object* x_4408; lean_object* x_4409; 
lean_dec(x_3764);
lean_dec(x_3761);
lean_dec(x_3758);
lean_dec(x_3754);
lean_dec(x_20);
x_4407 = lean_unsigned_to_nat(1u);
x_4408 = lean_nat_add(x_3, x_4407);
lean_dec(x_3);
x_4409 = lean_array_push(x_4, x_14);
x_3 = x_4408;
x_4 = x_4409;
goto _start;
}
}
else
{
lean_object* x_4411; lean_object* x_4412; lean_object* x_4413; 
lean_dec(x_3764);
lean_dec(x_3761);
lean_dec(x_3758);
lean_dec(x_3754);
lean_dec(x_20);
x_4411 = lean_unsigned_to_nat(1u);
x_4412 = lean_nat_add(x_3, x_4411);
lean_dec(x_3);
x_4413 = lean_array_push(x_4, x_14);
x_3 = x_4412;
x_4 = x_4413;
goto _start;
}
}
else
{
lean_object* x_4415; lean_object* x_4416; lean_object* x_4417; 
lean_dec(x_3764);
lean_dec(x_3761);
lean_dec(x_3758);
lean_dec(x_3754);
lean_dec(x_20);
x_4415 = lean_unsigned_to_nat(1u);
x_4416 = lean_nat_add(x_3, x_4415);
lean_dec(x_3);
x_4417 = lean_array_push(x_4, x_14);
x_3 = x_4416;
x_4 = x_4417;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_4419; lean_object* x_4420; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_4419 = 1;
lean_inc(x_14);
x_4420 = l_Lean_Syntax_isTermId_x3f(x_14, x_4419);
if (lean_obj_tag(x_4420) == 0)
{
lean_object* x_4421; lean_object* x_4422; lean_object* x_4423; lean_object* x_4424; lean_object* x_4425; lean_object* x_4426; lean_object* x_4427; lean_object* x_4428; lean_object* x_4429; 
x_4421 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4422 = lean_ctor_get(x_4421, 0);
lean_inc(x_4422);
x_4423 = lean_ctor_get(x_4421, 1);
lean_inc(x_4423);
lean_dec(x_4421);
x_4424 = lean_unsigned_to_nat(1u);
x_4425 = lean_nat_add(x_3, x_4424);
lean_dec(x_3);
x_4426 = l_Lean_mkHole(x_14);
lean_inc(x_4422);
x_4427 = l_Lean_Elab_Term_mkExplicitBinder(x_4422, x_4426);
x_4428 = lean_array_push(x_4, x_4427);
lean_inc(x_5);
x_4429 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4425, x_4428, x_5, x_4423);
if (lean_obj_tag(x_4429) == 0)
{
lean_object* x_4430; lean_object* x_4431; lean_object* x_4432; uint8_t x_4433; 
x_4430 = lean_ctor_get(x_4429, 0);
lean_inc(x_4430);
x_4431 = lean_ctor_get(x_4430, 1);
lean_inc(x_4431);
x_4432 = lean_ctor_get(x_4429, 1);
lean_inc(x_4432);
lean_dec(x_4429);
x_4433 = !lean_is_exclusive(x_4430);
if (x_4433 == 0)
{
lean_object* x_4434; uint8_t x_4435; 
x_4434 = lean_ctor_get(x_4430, 1);
lean_dec(x_4434);
x_4435 = !lean_is_exclusive(x_4431);
if (x_4435 == 0)
{
lean_object* x_4436; lean_object* x_4437; lean_object* x_4438; lean_object* x_4439; lean_object* x_4440; uint8_t x_4441; 
x_4436 = lean_ctor_get(x_4431, 0);
x_4437 = lean_ctor_get(x_4431, 1);
lean_dec(x_4437);
x_4438 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4432);
lean_dec(x_5);
x_4439 = lean_ctor_get(x_4438, 1);
lean_inc(x_4439);
lean_dec(x_4438);
x_4440 = l_Lean_Elab_Term_getMainModule___rarg(x_4439);
x_4441 = !lean_is_exclusive(x_4440);
if (x_4441 == 0)
{
lean_object* x_4442; lean_object* x_4443; lean_object* x_4444; lean_object* x_4445; lean_object* x_4446; lean_object* x_4447; lean_object* x_4448; lean_object* x_4449; lean_object* x_4450; lean_object* x_4451; lean_object* x_4452; lean_object* x_4453; lean_object* x_4454; lean_object* x_4455; lean_object* x_4456; lean_object* x_4457; lean_object* x_4458; lean_object* x_4459; lean_object* x_4460; lean_object* x_4461; lean_object* x_4462; lean_object* x_4463; uint8_t x_4464; 
x_4442 = lean_ctor_get(x_4440, 0);
lean_dec(x_4442);
x_4443 = l_Array_empty___closed__1;
x_4444 = lean_array_push(x_4443, x_4422);
x_4445 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4446 = lean_array_push(x_4444, x_4445);
x_4447 = l_Lean_mkTermIdFromIdent___closed__2;
x_4448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4448, 0, x_4447);
lean_ctor_set(x_4448, 1, x_4446);
x_4449 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4450 = lean_array_push(x_4449, x_4448);
x_4451 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4452, 0, x_4451);
lean_ctor_set(x_4452, 1, x_4450);
x_4453 = lean_array_push(x_4443, x_4452);
x_4454 = l_Lean_nullKind___closed__2;
x_4455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4455, 0, x_4454);
lean_ctor_set(x_4455, 1, x_4453);
x_4456 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4457 = lean_array_push(x_4456, x_4455);
x_4458 = lean_array_push(x_4457, x_4445);
x_4459 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4460 = lean_array_push(x_4458, x_4459);
x_4461 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4462 = lean_array_push(x_4460, x_4461);
lean_inc(x_14);
x_4463 = lean_array_push(x_4443, x_14);
x_4464 = !lean_is_exclusive(x_14);
if (x_4464 == 0)
{
lean_object* x_4465; lean_object* x_4466; lean_object* x_4467; lean_object* x_4468; lean_object* x_4469; lean_object* x_4470; lean_object* x_4471; lean_object* x_4472; lean_object* x_4473; lean_object* x_4474; lean_object* x_4475; lean_object* x_4476; lean_object* x_4477; lean_object* x_4478; 
x_4465 = lean_ctor_get(x_14, 1);
lean_dec(x_4465);
x_4466 = lean_ctor_get(x_14, 0);
lean_dec(x_4466);
lean_ctor_set(x_14, 1, x_4463);
lean_ctor_set(x_14, 0, x_4454);
x_4467 = lean_array_push(x_4443, x_14);
x_4468 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4469 = lean_array_push(x_4467, x_4468);
x_4470 = lean_array_push(x_4469, x_4436);
x_4471 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4472, 0, x_4471);
lean_ctor_set(x_4472, 1, x_4470);
x_4473 = lean_array_push(x_4443, x_4472);
x_4474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4474, 0, x_4454);
lean_ctor_set(x_4474, 1, x_4473);
x_4475 = lean_array_push(x_4462, x_4474);
x_4476 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4477, 0, x_4476);
lean_ctor_set(x_4477, 1, x_4475);
x_4478 = lean_box(x_4419);
lean_ctor_set(x_4431, 1, x_4478);
lean_ctor_set(x_4431, 0, x_4477);
lean_ctor_set(x_4440, 0, x_4430);
return x_4440;
}
else
{
lean_object* x_4479; lean_object* x_4480; lean_object* x_4481; lean_object* x_4482; lean_object* x_4483; lean_object* x_4484; lean_object* x_4485; lean_object* x_4486; lean_object* x_4487; lean_object* x_4488; lean_object* x_4489; lean_object* x_4490; lean_object* x_4491; 
lean_dec(x_14);
x_4479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4479, 0, x_4454);
lean_ctor_set(x_4479, 1, x_4463);
x_4480 = lean_array_push(x_4443, x_4479);
x_4481 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4482 = lean_array_push(x_4480, x_4481);
x_4483 = lean_array_push(x_4482, x_4436);
x_4484 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4485, 0, x_4484);
lean_ctor_set(x_4485, 1, x_4483);
x_4486 = lean_array_push(x_4443, x_4485);
x_4487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4487, 0, x_4454);
lean_ctor_set(x_4487, 1, x_4486);
x_4488 = lean_array_push(x_4462, x_4487);
x_4489 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4490, 0, x_4489);
lean_ctor_set(x_4490, 1, x_4488);
x_4491 = lean_box(x_4419);
lean_ctor_set(x_4431, 1, x_4491);
lean_ctor_set(x_4431, 0, x_4490);
lean_ctor_set(x_4440, 0, x_4430);
return x_4440;
}
}
else
{
lean_object* x_4492; lean_object* x_4493; lean_object* x_4494; lean_object* x_4495; lean_object* x_4496; lean_object* x_4497; lean_object* x_4498; lean_object* x_4499; lean_object* x_4500; lean_object* x_4501; lean_object* x_4502; lean_object* x_4503; lean_object* x_4504; lean_object* x_4505; lean_object* x_4506; lean_object* x_4507; lean_object* x_4508; lean_object* x_4509; lean_object* x_4510; lean_object* x_4511; lean_object* x_4512; lean_object* x_4513; lean_object* x_4514; lean_object* x_4515; lean_object* x_4516; lean_object* x_4517; lean_object* x_4518; lean_object* x_4519; lean_object* x_4520; lean_object* x_4521; lean_object* x_4522; lean_object* x_4523; lean_object* x_4524; lean_object* x_4525; lean_object* x_4526; lean_object* x_4527; lean_object* x_4528; 
x_4492 = lean_ctor_get(x_4440, 1);
lean_inc(x_4492);
lean_dec(x_4440);
x_4493 = l_Array_empty___closed__1;
x_4494 = lean_array_push(x_4493, x_4422);
x_4495 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4496 = lean_array_push(x_4494, x_4495);
x_4497 = l_Lean_mkTermIdFromIdent___closed__2;
x_4498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4498, 0, x_4497);
lean_ctor_set(x_4498, 1, x_4496);
x_4499 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4500 = lean_array_push(x_4499, x_4498);
x_4501 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4502, 0, x_4501);
lean_ctor_set(x_4502, 1, x_4500);
x_4503 = lean_array_push(x_4493, x_4502);
x_4504 = l_Lean_nullKind___closed__2;
x_4505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4505, 0, x_4504);
lean_ctor_set(x_4505, 1, x_4503);
x_4506 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4507 = lean_array_push(x_4506, x_4505);
x_4508 = lean_array_push(x_4507, x_4495);
x_4509 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4510 = lean_array_push(x_4508, x_4509);
x_4511 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4512 = lean_array_push(x_4510, x_4511);
lean_inc(x_14);
x_4513 = lean_array_push(x_4493, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4514 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4514 = lean_box(0);
}
if (lean_is_scalar(x_4514)) {
 x_4515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4515 = x_4514;
}
lean_ctor_set(x_4515, 0, x_4504);
lean_ctor_set(x_4515, 1, x_4513);
x_4516 = lean_array_push(x_4493, x_4515);
x_4517 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4518 = lean_array_push(x_4516, x_4517);
x_4519 = lean_array_push(x_4518, x_4436);
x_4520 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4521, 0, x_4520);
lean_ctor_set(x_4521, 1, x_4519);
x_4522 = lean_array_push(x_4493, x_4521);
x_4523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4523, 0, x_4504);
lean_ctor_set(x_4523, 1, x_4522);
x_4524 = lean_array_push(x_4512, x_4523);
x_4525 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4526, 0, x_4525);
lean_ctor_set(x_4526, 1, x_4524);
x_4527 = lean_box(x_4419);
lean_ctor_set(x_4431, 1, x_4527);
lean_ctor_set(x_4431, 0, x_4526);
x_4528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4528, 0, x_4430);
lean_ctor_set(x_4528, 1, x_4492);
return x_4528;
}
}
else
{
lean_object* x_4529; lean_object* x_4530; lean_object* x_4531; lean_object* x_4532; lean_object* x_4533; lean_object* x_4534; lean_object* x_4535; lean_object* x_4536; lean_object* x_4537; lean_object* x_4538; lean_object* x_4539; lean_object* x_4540; lean_object* x_4541; lean_object* x_4542; lean_object* x_4543; lean_object* x_4544; lean_object* x_4545; lean_object* x_4546; lean_object* x_4547; lean_object* x_4548; lean_object* x_4549; lean_object* x_4550; lean_object* x_4551; lean_object* x_4552; lean_object* x_4553; lean_object* x_4554; lean_object* x_4555; lean_object* x_4556; lean_object* x_4557; lean_object* x_4558; lean_object* x_4559; lean_object* x_4560; lean_object* x_4561; lean_object* x_4562; lean_object* x_4563; lean_object* x_4564; lean_object* x_4565; lean_object* x_4566; lean_object* x_4567; lean_object* x_4568; lean_object* x_4569; lean_object* x_4570; lean_object* x_4571; 
x_4529 = lean_ctor_get(x_4431, 0);
lean_inc(x_4529);
lean_dec(x_4431);
x_4530 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4432);
lean_dec(x_5);
x_4531 = lean_ctor_get(x_4530, 1);
lean_inc(x_4531);
lean_dec(x_4530);
x_4532 = l_Lean_Elab_Term_getMainModule___rarg(x_4531);
x_4533 = lean_ctor_get(x_4532, 1);
lean_inc(x_4533);
if (lean_is_exclusive(x_4532)) {
 lean_ctor_release(x_4532, 0);
 lean_ctor_release(x_4532, 1);
 x_4534 = x_4532;
} else {
 lean_dec_ref(x_4532);
 x_4534 = lean_box(0);
}
x_4535 = l_Array_empty___closed__1;
x_4536 = lean_array_push(x_4535, x_4422);
x_4537 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4538 = lean_array_push(x_4536, x_4537);
x_4539 = l_Lean_mkTermIdFromIdent___closed__2;
x_4540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4540, 0, x_4539);
lean_ctor_set(x_4540, 1, x_4538);
x_4541 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4542 = lean_array_push(x_4541, x_4540);
x_4543 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4544, 0, x_4543);
lean_ctor_set(x_4544, 1, x_4542);
x_4545 = lean_array_push(x_4535, x_4544);
x_4546 = l_Lean_nullKind___closed__2;
x_4547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4547, 0, x_4546);
lean_ctor_set(x_4547, 1, x_4545);
x_4548 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4549 = lean_array_push(x_4548, x_4547);
x_4550 = lean_array_push(x_4549, x_4537);
x_4551 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4552 = lean_array_push(x_4550, x_4551);
x_4553 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4554 = lean_array_push(x_4552, x_4553);
lean_inc(x_14);
x_4555 = lean_array_push(x_4535, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4556 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4556 = lean_box(0);
}
if (lean_is_scalar(x_4556)) {
 x_4557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4557 = x_4556;
}
lean_ctor_set(x_4557, 0, x_4546);
lean_ctor_set(x_4557, 1, x_4555);
x_4558 = lean_array_push(x_4535, x_4557);
x_4559 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4560 = lean_array_push(x_4558, x_4559);
x_4561 = lean_array_push(x_4560, x_4529);
x_4562 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4563, 0, x_4562);
lean_ctor_set(x_4563, 1, x_4561);
x_4564 = lean_array_push(x_4535, x_4563);
x_4565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4565, 0, x_4546);
lean_ctor_set(x_4565, 1, x_4564);
x_4566 = lean_array_push(x_4554, x_4565);
x_4567 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4568, 0, x_4567);
lean_ctor_set(x_4568, 1, x_4566);
x_4569 = lean_box(x_4419);
x_4570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4570, 0, x_4568);
lean_ctor_set(x_4570, 1, x_4569);
lean_ctor_set(x_4430, 1, x_4570);
if (lean_is_scalar(x_4534)) {
 x_4571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4571 = x_4534;
}
lean_ctor_set(x_4571, 0, x_4430);
lean_ctor_set(x_4571, 1, x_4533);
return x_4571;
}
}
else
{
lean_object* x_4572; lean_object* x_4573; lean_object* x_4574; lean_object* x_4575; lean_object* x_4576; lean_object* x_4577; lean_object* x_4578; lean_object* x_4579; lean_object* x_4580; lean_object* x_4581; lean_object* x_4582; lean_object* x_4583; lean_object* x_4584; lean_object* x_4585; lean_object* x_4586; lean_object* x_4587; lean_object* x_4588; lean_object* x_4589; lean_object* x_4590; lean_object* x_4591; lean_object* x_4592; lean_object* x_4593; lean_object* x_4594; lean_object* x_4595; lean_object* x_4596; lean_object* x_4597; lean_object* x_4598; lean_object* x_4599; lean_object* x_4600; lean_object* x_4601; lean_object* x_4602; lean_object* x_4603; lean_object* x_4604; lean_object* x_4605; lean_object* x_4606; lean_object* x_4607; lean_object* x_4608; lean_object* x_4609; lean_object* x_4610; lean_object* x_4611; lean_object* x_4612; lean_object* x_4613; lean_object* x_4614; lean_object* x_4615; lean_object* x_4616; lean_object* x_4617; 
x_4572 = lean_ctor_get(x_4430, 0);
lean_inc(x_4572);
lean_dec(x_4430);
x_4573 = lean_ctor_get(x_4431, 0);
lean_inc(x_4573);
if (lean_is_exclusive(x_4431)) {
 lean_ctor_release(x_4431, 0);
 lean_ctor_release(x_4431, 1);
 x_4574 = x_4431;
} else {
 lean_dec_ref(x_4431);
 x_4574 = lean_box(0);
}
x_4575 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4432);
lean_dec(x_5);
x_4576 = lean_ctor_get(x_4575, 1);
lean_inc(x_4576);
lean_dec(x_4575);
x_4577 = l_Lean_Elab_Term_getMainModule___rarg(x_4576);
x_4578 = lean_ctor_get(x_4577, 1);
lean_inc(x_4578);
if (lean_is_exclusive(x_4577)) {
 lean_ctor_release(x_4577, 0);
 lean_ctor_release(x_4577, 1);
 x_4579 = x_4577;
} else {
 lean_dec_ref(x_4577);
 x_4579 = lean_box(0);
}
x_4580 = l_Array_empty___closed__1;
x_4581 = lean_array_push(x_4580, x_4422);
x_4582 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4583 = lean_array_push(x_4581, x_4582);
x_4584 = l_Lean_mkTermIdFromIdent___closed__2;
x_4585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4585, 0, x_4584);
lean_ctor_set(x_4585, 1, x_4583);
x_4586 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4587 = lean_array_push(x_4586, x_4585);
x_4588 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4589, 0, x_4588);
lean_ctor_set(x_4589, 1, x_4587);
x_4590 = lean_array_push(x_4580, x_4589);
x_4591 = l_Lean_nullKind___closed__2;
x_4592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4592, 0, x_4591);
lean_ctor_set(x_4592, 1, x_4590);
x_4593 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4594 = lean_array_push(x_4593, x_4592);
x_4595 = lean_array_push(x_4594, x_4582);
x_4596 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4597 = lean_array_push(x_4595, x_4596);
x_4598 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4599 = lean_array_push(x_4597, x_4598);
lean_inc(x_14);
x_4600 = lean_array_push(x_4580, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4601 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4601 = lean_box(0);
}
if (lean_is_scalar(x_4601)) {
 x_4602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4602 = x_4601;
}
lean_ctor_set(x_4602, 0, x_4591);
lean_ctor_set(x_4602, 1, x_4600);
x_4603 = lean_array_push(x_4580, x_4602);
x_4604 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4605 = lean_array_push(x_4603, x_4604);
x_4606 = lean_array_push(x_4605, x_4573);
x_4607 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4608, 0, x_4607);
lean_ctor_set(x_4608, 1, x_4606);
x_4609 = lean_array_push(x_4580, x_4608);
x_4610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4610, 0, x_4591);
lean_ctor_set(x_4610, 1, x_4609);
x_4611 = lean_array_push(x_4599, x_4610);
x_4612 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4613, 0, x_4612);
lean_ctor_set(x_4613, 1, x_4611);
x_4614 = lean_box(x_4419);
if (lean_is_scalar(x_4574)) {
 x_4615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4615 = x_4574;
}
lean_ctor_set(x_4615, 0, x_4613);
lean_ctor_set(x_4615, 1, x_4614);
x_4616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4616, 0, x_4572);
lean_ctor_set(x_4616, 1, x_4615);
if (lean_is_scalar(x_4579)) {
 x_4617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4617 = x_4579;
}
lean_ctor_set(x_4617, 0, x_4616);
lean_ctor_set(x_4617, 1, x_4578);
return x_4617;
}
}
else
{
uint8_t x_4618; 
lean_dec(x_4422);
lean_dec(x_14);
lean_dec(x_5);
x_4618 = !lean_is_exclusive(x_4429);
if (x_4618 == 0)
{
return x_4429;
}
else
{
lean_object* x_4619; lean_object* x_4620; lean_object* x_4621; 
x_4619 = lean_ctor_get(x_4429, 0);
x_4620 = lean_ctor_get(x_4429, 1);
lean_inc(x_4620);
lean_inc(x_4619);
lean_dec(x_4429);
x_4621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4621, 0, x_4619);
lean_ctor_set(x_4621, 1, x_4620);
return x_4621;
}
}
}
else
{
lean_object* x_4622; lean_object* x_4623; lean_object* x_4624; uint8_t x_4625; 
x_4622 = lean_ctor_get(x_4420, 0);
lean_inc(x_4622);
lean_dec(x_4420);
x_4623 = lean_ctor_get(x_4622, 0);
lean_inc(x_4623);
x_4624 = lean_ctor_get(x_4622, 1);
lean_inc(x_4624);
lean_dec(x_4622);
x_4625 = l_Lean_Syntax_isNone(x_4624);
lean_dec(x_4624);
if (x_4625 == 0)
{
lean_object* x_4626; lean_object* x_4627; uint8_t x_4628; 
lean_dec(x_4623);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4626 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_4627 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_4626, x_5, x_6);
lean_dec(x_14);
x_4628 = !lean_is_exclusive(x_4627);
if (x_4628 == 0)
{
return x_4627;
}
else
{
lean_object* x_4629; lean_object* x_4630; lean_object* x_4631; 
x_4629 = lean_ctor_get(x_4627, 0);
x_4630 = lean_ctor_get(x_4627, 1);
lean_inc(x_4630);
lean_inc(x_4629);
lean_dec(x_4627);
x_4631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4631, 0, x_4629);
lean_ctor_set(x_4631, 1, x_4630);
return x_4631;
}
}
else
{
lean_object* x_4632; lean_object* x_4633; lean_object* x_4634; lean_object* x_4635; lean_object* x_4636; 
x_4632 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_4633 = lean_unsigned_to_nat(1u);
x_4634 = lean_nat_add(x_3, x_4633);
lean_dec(x_3);
x_4635 = l_Lean_Elab_Term_mkExplicitBinder(x_4623, x_4632);
x_4636 = lean_array_push(x_4, x_4635);
x_3 = x_4634;
x_4 = x_4636;
goto _start;
}
}
}
}
else
{
uint8_t x_4638; lean_object* x_4639; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_4638 = 1;
lean_inc(x_14);
x_4639 = l_Lean_Syntax_isTermId_x3f(x_14, x_4638);
if (lean_obj_tag(x_4639) == 0)
{
lean_object* x_4640; lean_object* x_4641; lean_object* x_4642; lean_object* x_4643; lean_object* x_4644; lean_object* x_4645; lean_object* x_4646; lean_object* x_4647; lean_object* x_4648; 
x_4640 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4641 = lean_ctor_get(x_4640, 0);
lean_inc(x_4641);
x_4642 = lean_ctor_get(x_4640, 1);
lean_inc(x_4642);
lean_dec(x_4640);
x_4643 = lean_unsigned_to_nat(1u);
x_4644 = lean_nat_add(x_3, x_4643);
lean_dec(x_3);
x_4645 = l_Lean_mkHole(x_14);
lean_inc(x_4641);
x_4646 = l_Lean_Elab_Term_mkExplicitBinder(x_4641, x_4645);
x_4647 = lean_array_push(x_4, x_4646);
lean_inc(x_5);
x_4648 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4644, x_4647, x_5, x_4642);
if (lean_obj_tag(x_4648) == 0)
{
lean_object* x_4649; lean_object* x_4650; lean_object* x_4651; uint8_t x_4652; 
x_4649 = lean_ctor_get(x_4648, 0);
lean_inc(x_4649);
x_4650 = lean_ctor_get(x_4649, 1);
lean_inc(x_4650);
x_4651 = lean_ctor_get(x_4648, 1);
lean_inc(x_4651);
lean_dec(x_4648);
x_4652 = !lean_is_exclusive(x_4649);
if (x_4652 == 0)
{
lean_object* x_4653; uint8_t x_4654; 
x_4653 = lean_ctor_get(x_4649, 1);
lean_dec(x_4653);
x_4654 = !lean_is_exclusive(x_4650);
if (x_4654 == 0)
{
lean_object* x_4655; lean_object* x_4656; lean_object* x_4657; lean_object* x_4658; lean_object* x_4659; uint8_t x_4660; 
x_4655 = lean_ctor_get(x_4650, 0);
x_4656 = lean_ctor_get(x_4650, 1);
lean_dec(x_4656);
x_4657 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4651);
lean_dec(x_5);
x_4658 = lean_ctor_get(x_4657, 1);
lean_inc(x_4658);
lean_dec(x_4657);
x_4659 = l_Lean_Elab_Term_getMainModule___rarg(x_4658);
x_4660 = !lean_is_exclusive(x_4659);
if (x_4660 == 0)
{
lean_object* x_4661; lean_object* x_4662; lean_object* x_4663; lean_object* x_4664; lean_object* x_4665; lean_object* x_4666; lean_object* x_4667; lean_object* x_4668; lean_object* x_4669; lean_object* x_4670; lean_object* x_4671; lean_object* x_4672; lean_object* x_4673; lean_object* x_4674; lean_object* x_4675; lean_object* x_4676; lean_object* x_4677; lean_object* x_4678; lean_object* x_4679; lean_object* x_4680; lean_object* x_4681; lean_object* x_4682; uint8_t x_4683; 
x_4661 = lean_ctor_get(x_4659, 0);
lean_dec(x_4661);
x_4662 = l_Array_empty___closed__1;
x_4663 = lean_array_push(x_4662, x_4641);
x_4664 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4665 = lean_array_push(x_4663, x_4664);
x_4666 = l_Lean_mkTermIdFromIdent___closed__2;
x_4667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4667, 0, x_4666);
lean_ctor_set(x_4667, 1, x_4665);
x_4668 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4669 = lean_array_push(x_4668, x_4667);
x_4670 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4671, 0, x_4670);
lean_ctor_set(x_4671, 1, x_4669);
x_4672 = lean_array_push(x_4662, x_4671);
x_4673 = l_Lean_nullKind___closed__2;
x_4674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4674, 0, x_4673);
lean_ctor_set(x_4674, 1, x_4672);
x_4675 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4676 = lean_array_push(x_4675, x_4674);
x_4677 = lean_array_push(x_4676, x_4664);
x_4678 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4679 = lean_array_push(x_4677, x_4678);
x_4680 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4681 = lean_array_push(x_4679, x_4680);
lean_inc(x_14);
x_4682 = lean_array_push(x_4662, x_14);
x_4683 = !lean_is_exclusive(x_14);
if (x_4683 == 0)
{
lean_object* x_4684; lean_object* x_4685; lean_object* x_4686; lean_object* x_4687; lean_object* x_4688; lean_object* x_4689; lean_object* x_4690; lean_object* x_4691; lean_object* x_4692; lean_object* x_4693; lean_object* x_4694; lean_object* x_4695; lean_object* x_4696; lean_object* x_4697; 
x_4684 = lean_ctor_get(x_14, 1);
lean_dec(x_4684);
x_4685 = lean_ctor_get(x_14, 0);
lean_dec(x_4685);
lean_ctor_set(x_14, 1, x_4682);
lean_ctor_set(x_14, 0, x_4673);
x_4686 = lean_array_push(x_4662, x_14);
x_4687 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4688 = lean_array_push(x_4686, x_4687);
x_4689 = lean_array_push(x_4688, x_4655);
x_4690 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4691, 0, x_4690);
lean_ctor_set(x_4691, 1, x_4689);
x_4692 = lean_array_push(x_4662, x_4691);
x_4693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4693, 0, x_4673);
lean_ctor_set(x_4693, 1, x_4692);
x_4694 = lean_array_push(x_4681, x_4693);
x_4695 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4696, 0, x_4695);
lean_ctor_set(x_4696, 1, x_4694);
x_4697 = lean_box(x_4638);
lean_ctor_set(x_4650, 1, x_4697);
lean_ctor_set(x_4650, 0, x_4696);
lean_ctor_set(x_4659, 0, x_4649);
return x_4659;
}
else
{
lean_object* x_4698; lean_object* x_4699; lean_object* x_4700; lean_object* x_4701; lean_object* x_4702; lean_object* x_4703; lean_object* x_4704; lean_object* x_4705; lean_object* x_4706; lean_object* x_4707; lean_object* x_4708; lean_object* x_4709; lean_object* x_4710; 
lean_dec(x_14);
x_4698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4698, 0, x_4673);
lean_ctor_set(x_4698, 1, x_4682);
x_4699 = lean_array_push(x_4662, x_4698);
x_4700 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4701 = lean_array_push(x_4699, x_4700);
x_4702 = lean_array_push(x_4701, x_4655);
x_4703 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4704, 0, x_4703);
lean_ctor_set(x_4704, 1, x_4702);
x_4705 = lean_array_push(x_4662, x_4704);
x_4706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4706, 0, x_4673);
lean_ctor_set(x_4706, 1, x_4705);
x_4707 = lean_array_push(x_4681, x_4706);
x_4708 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4709, 0, x_4708);
lean_ctor_set(x_4709, 1, x_4707);
x_4710 = lean_box(x_4638);
lean_ctor_set(x_4650, 1, x_4710);
lean_ctor_set(x_4650, 0, x_4709);
lean_ctor_set(x_4659, 0, x_4649);
return x_4659;
}
}
else
{
lean_object* x_4711; lean_object* x_4712; lean_object* x_4713; lean_object* x_4714; lean_object* x_4715; lean_object* x_4716; lean_object* x_4717; lean_object* x_4718; lean_object* x_4719; lean_object* x_4720; lean_object* x_4721; lean_object* x_4722; lean_object* x_4723; lean_object* x_4724; lean_object* x_4725; lean_object* x_4726; lean_object* x_4727; lean_object* x_4728; lean_object* x_4729; lean_object* x_4730; lean_object* x_4731; lean_object* x_4732; lean_object* x_4733; lean_object* x_4734; lean_object* x_4735; lean_object* x_4736; lean_object* x_4737; lean_object* x_4738; lean_object* x_4739; lean_object* x_4740; lean_object* x_4741; lean_object* x_4742; lean_object* x_4743; lean_object* x_4744; lean_object* x_4745; lean_object* x_4746; lean_object* x_4747; 
x_4711 = lean_ctor_get(x_4659, 1);
lean_inc(x_4711);
lean_dec(x_4659);
x_4712 = l_Array_empty___closed__1;
x_4713 = lean_array_push(x_4712, x_4641);
x_4714 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4715 = lean_array_push(x_4713, x_4714);
x_4716 = l_Lean_mkTermIdFromIdent___closed__2;
x_4717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4717, 0, x_4716);
lean_ctor_set(x_4717, 1, x_4715);
x_4718 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4719 = lean_array_push(x_4718, x_4717);
x_4720 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4721, 0, x_4720);
lean_ctor_set(x_4721, 1, x_4719);
x_4722 = lean_array_push(x_4712, x_4721);
x_4723 = l_Lean_nullKind___closed__2;
x_4724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4724, 0, x_4723);
lean_ctor_set(x_4724, 1, x_4722);
x_4725 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4726 = lean_array_push(x_4725, x_4724);
x_4727 = lean_array_push(x_4726, x_4714);
x_4728 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4729 = lean_array_push(x_4727, x_4728);
x_4730 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4731 = lean_array_push(x_4729, x_4730);
lean_inc(x_14);
x_4732 = lean_array_push(x_4712, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4733 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4733 = lean_box(0);
}
if (lean_is_scalar(x_4733)) {
 x_4734 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4734 = x_4733;
}
lean_ctor_set(x_4734, 0, x_4723);
lean_ctor_set(x_4734, 1, x_4732);
x_4735 = lean_array_push(x_4712, x_4734);
x_4736 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4737 = lean_array_push(x_4735, x_4736);
x_4738 = lean_array_push(x_4737, x_4655);
x_4739 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4740, 0, x_4739);
lean_ctor_set(x_4740, 1, x_4738);
x_4741 = lean_array_push(x_4712, x_4740);
x_4742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4742, 0, x_4723);
lean_ctor_set(x_4742, 1, x_4741);
x_4743 = lean_array_push(x_4731, x_4742);
x_4744 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4745, 0, x_4744);
lean_ctor_set(x_4745, 1, x_4743);
x_4746 = lean_box(x_4638);
lean_ctor_set(x_4650, 1, x_4746);
lean_ctor_set(x_4650, 0, x_4745);
x_4747 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4747, 0, x_4649);
lean_ctor_set(x_4747, 1, x_4711);
return x_4747;
}
}
else
{
lean_object* x_4748; lean_object* x_4749; lean_object* x_4750; lean_object* x_4751; lean_object* x_4752; lean_object* x_4753; lean_object* x_4754; lean_object* x_4755; lean_object* x_4756; lean_object* x_4757; lean_object* x_4758; lean_object* x_4759; lean_object* x_4760; lean_object* x_4761; lean_object* x_4762; lean_object* x_4763; lean_object* x_4764; lean_object* x_4765; lean_object* x_4766; lean_object* x_4767; lean_object* x_4768; lean_object* x_4769; lean_object* x_4770; lean_object* x_4771; lean_object* x_4772; lean_object* x_4773; lean_object* x_4774; lean_object* x_4775; lean_object* x_4776; lean_object* x_4777; lean_object* x_4778; lean_object* x_4779; lean_object* x_4780; lean_object* x_4781; lean_object* x_4782; lean_object* x_4783; lean_object* x_4784; lean_object* x_4785; lean_object* x_4786; lean_object* x_4787; lean_object* x_4788; lean_object* x_4789; lean_object* x_4790; 
x_4748 = lean_ctor_get(x_4650, 0);
lean_inc(x_4748);
lean_dec(x_4650);
x_4749 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4651);
lean_dec(x_5);
x_4750 = lean_ctor_get(x_4749, 1);
lean_inc(x_4750);
lean_dec(x_4749);
x_4751 = l_Lean_Elab_Term_getMainModule___rarg(x_4750);
x_4752 = lean_ctor_get(x_4751, 1);
lean_inc(x_4752);
if (lean_is_exclusive(x_4751)) {
 lean_ctor_release(x_4751, 0);
 lean_ctor_release(x_4751, 1);
 x_4753 = x_4751;
} else {
 lean_dec_ref(x_4751);
 x_4753 = lean_box(0);
}
x_4754 = l_Array_empty___closed__1;
x_4755 = lean_array_push(x_4754, x_4641);
x_4756 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4757 = lean_array_push(x_4755, x_4756);
x_4758 = l_Lean_mkTermIdFromIdent___closed__2;
x_4759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4759, 0, x_4758);
lean_ctor_set(x_4759, 1, x_4757);
x_4760 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4761 = lean_array_push(x_4760, x_4759);
x_4762 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4763, 0, x_4762);
lean_ctor_set(x_4763, 1, x_4761);
x_4764 = lean_array_push(x_4754, x_4763);
x_4765 = l_Lean_nullKind___closed__2;
x_4766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4766, 0, x_4765);
lean_ctor_set(x_4766, 1, x_4764);
x_4767 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4768 = lean_array_push(x_4767, x_4766);
x_4769 = lean_array_push(x_4768, x_4756);
x_4770 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4771 = lean_array_push(x_4769, x_4770);
x_4772 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4773 = lean_array_push(x_4771, x_4772);
lean_inc(x_14);
x_4774 = lean_array_push(x_4754, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4775 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4775 = lean_box(0);
}
if (lean_is_scalar(x_4775)) {
 x_4776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4776 = x_4775;
}
lean_ctor_set(x_4776, 0, x_4765);
lean_ctor_set(x_4776, 1, x_4774);
x_4777 = lean_array_push(x_4754, x_4776);
x_4778 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4779 = lean_array_push(x_4777, x_4778);
x_4780 = lean_array_push(x_4779, x_4748);
x_4781 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4782, 0, x_4781);
lean_ctor_set(x_4782, 1, x_4780);
x_4783 = lean_array_push(x_4754, x_4782);
x_4784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4784, 0, x_4765);
lean_ctor_set(x_4784, 1, x_4783);
x_4785 = lean_array_push(x_4773, x_4784);
x_4786 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4787, 0, x_4786);
lean_ctor_set(x_4787, 1, x_4785);
x_4788 = lean_box(x_4638);
x_4789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4789, 0, x_4787);
lean_ctor_set(x_4789, 1, x_4788);
lean_ctor_set(x_4649, 1, x_4789);
if (lean_is_scalar(x_4753)) {
 x_4790 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4790 = x_4753;
}
lean_ctor_set(x_4790, 0, x_4649);
lean_ctor_set(x_4790, 1, x_4752);
return x_4790;
}
}
else
{
lean_object* x_4791; lean_object* x_4792; lean_object* x_4793; lean_object* x_4794; lean_object* x_4795; lean_object* x_4796; lean_object* x_4797; lean_object* x_4798; lean_object* x_4799; lean_object* x_4800; lean_object* x_4801; lean_object* x_4802; lean_object* x_4803; lean_object* x_4804; lean_object* x_4805; lean_object* x_4806; lean_object* x_4807; lean_object* x_4808; lean_object* x_4809; lean_object* x_4810; lean_object* x_4811; lean_object* x_4812; lean_object* x_4813; lean_object* x_4814; lean_object* x_4815; lean_object* x_4816; lean_object* x_4817; lean_object* x_4818; lean_object* x_4819; lean_object* x_4820; lean_object* x_4821; lean_object* x_4822; lean_object* x_4823; lean_object* x_4824; lean_object* x_4825; lean_object* x_4826; lean_object* x_4827; lean_object* x_4828; lean_object* x_4829; lean_object* x_4830; lean_object* x_4831; lean_object* x_4832; lean_object* x_4833; lean_object* x_4834; lean_object* x_4835; lean_object* x_4836; 
x_4791 = lean_ctor_get(x_4649, 0);
lean_inc(x_4791);
lean_dec(x_4649);
x_4792 = lean_ctor_get(x_4650, 0);
lean_inc(x_4792);
if (lean_is_exclusive(x_4650)) {
 lean_ctor_release(x_4650, 0);
 lean_ctor_release(x_4650, 1);
 x_4793 = x_4650;
} else {
 lean_dec_ref(x_4650);
 x_4793 = lean_box(0);
}
x_4794 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4651);
lean_dec(x_5);
x_4795 = lean_ctor_get(x_4794, 1);
lean_inc(x_4795);
lean_dec(x_4794);
x_4796 = l_Lean_Elab_Term_getMainModule___rarg(x_4795);
x_4797 = lean_ctor_get(x_4796, 1);
lean_inc(x_4797);
if (lean_is_exclusive(x_4796)) {
 lean_ctor_release(x_4796, 0);
 lean_ctor_release(x_4796, 1);
 x_4798 = x_4796;
} else {
 lean_dec_ref(x_4796);
 x_4798 = lean_box(0);
}
x_4799 = l_Array_empty___closed__1;
x_4800 = lean_array_push(x_4799, x_4641);
x_4801 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4802 = lean_array_push(x_4800, x_4801);
x_4803 = l_Lean_mkTermIdFromIdent___closed__2;
x_4804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4804, 0, x_4803);
lean_ctor_set(x_4804, 1, x_4802);
x_4805 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4806 = lean_array_push(x_4805, x_4804);
x_4807 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4808, 0, x_4807);
lean_ctor_set(x_4808, 1, x_4806);
x_4809 = lean_array_push(x_4799, x_4808);
x_4810 = l_Lean_nullKind___closed__2;
x_4811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4811, 0, x_4810);
lean_ctor_set(x_4811, 1, x_4809);
x_4812 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4813 = lean_array_push(x_4812, x_4811);
x_4814 = lean_array_push(x_4813, x_4801);
x_4815 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4816 = lean_array_push(x_4814, x_4815);
x_4817 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4818 = lean_array_push(x_4816, x_4817);
lean_inc(x_14);
x_4819 = lean_array_push(x_4799, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4820 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4820 = lean_box(0);
}
if (lean_is_scalar(x_4820)) {
 x_4821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4821 = x_4820;
}
lean_ctor_set(x_4821, 0, x_4810);
lean_ctor_set(x_4821, 1, x_4819);
x_4822 = lean_array_push(x_4799, x_4821);
x_4823 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4824 = lean_array_push(x_4822, x_4823);
x_4825 = lean_array_push(x_4824, x_4792);
x_4826 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4827, 0, x_4826);
lean_ctor_set(x_4827, 1, x_4825);
x_4828 = lean_array_push(x_4799, x_4827);
x_4829 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4829, 0, x_4810);
lean_ctor_set(x_4829, 1, x_4828);
x_4830 = lean_array_push(x_4818, x_4829);
x_4831 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4832, 0, x_4831);
lean_ctor_set(x_4832, 1, x_4830);
x_4833 = lean_box(x_4638);
if (lean_is_scalar(x_4793)) {
 x_4834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4834 = x_4793;
}
lean_ctor_set(x_4834, 0, x_4832);
lean_ctor_set(x_4834, 1, x_4833);
x_4835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4835, 0, x_4791);
lean_ctor_set(x_4835, 1, x_4834);
if (lean_is_scalar(x_4798)) {
 x_4836 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4836 = x_4798;
}
lean_ctor_set(x_4836, 0, x_4835);
lean_ctor_set(x_4836, 1, x_4797);
return x_4836;
}
}
else
{
uint8_t x_4837; 
lean_dec(x_4641);
lean_dec(x_14);
lean_dec(x_5);
x_4837 = !lean_is_exclusive(x_4648);
if (x_4837 == 0)
{
return x_4648;
}
else
{
lean_object* x_4838; lean_object* x_4839; lean_object* x_4840; 
x_4838 = lean_ctor_get(x_4648, 0);
x_4839 = lean_ctor_get(x_4648, 1);
lean_inc(x_4839);
lean_inc(x_4838);
lean_dec(x_4648);
x_4840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4840, 0, x_4838);
lean_ctor_set(x_4840, 1, x_4839);
return x_4840;
}
}
}
else
{
lean_object* x_4841; lean_object* x_4842; lean_object* x_4843; uint8_t x_4844; 
x_4841 = lean_ctor_get(x_4639, 0);
lean_inc(x_4841);
lean_dec(x_4639);
x_4842 = lean_ctor_get(x_4841, 0);
lean_inc(x_4842);
x_4843 = lean_ctor_get(x_4841, 1);
lean_inc(x_4843);
lean_dec(x_4841);
x_4844 = l_Lean_Syntax_isNone(x_4843);
lean_dec(x_4843);
if (x_4844 == 0)
{
lean_object* x_4845; lean_object* x_4846; uint8_t x_4847; 
lean_dec(x_4842);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_4845 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_4846 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_4845, x_5, x_6);
lean_dec(x_14);
x_4847 = !lean_is_exclusive(x_4846);
if (x_4847 == 0)
{
return x_4846;
}
else
{
lean_object* x_4848; lean_object* x_4849; lean_object* x_4850; 
x_4848 = lean_ctor_get(x_4846, 0);
x_4849 = lean_ctor_get(x_4846, 1);
lean_inc(x_4849);
lean_inc(x_4848);
lean_dec(x_4846);
x_4850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4850, 0, x_4848);
lean_ctor_set(x_4850, 1, x_4849);
return x_4850;
}
}
else
{
lean_object* x_4851; lean_object* x_4852; lean_object* x_4853; lean_object* x_4854; lean_object* x_4855; 
x_4851 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_4852 = lean_unsigned_to_nat(1u);
x_4853 = lean_nat_add(x_3, x_4852);
lean_dec(x_3);
x_4854 = l_Lean_Elab_Term_mkExplicitBinder(x_4842, x_4851);
x_4855 = lean_array_push(x_4, x_4854);
x_3 = x_4853;
x_4 = x_4855;
goto _start;
}
}
}
}
else
{
uint8_t x_4857; lean_object* x_4858; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_4857 = 1;
lean_inc(x_14);
x_4858 = l_Lean_Syntax_isTermId_x3f(x_14, x_4857);
if (lean_obj_tag(x_4858) == 0)
{
lean_object* x_4859; lean_object* x_4860; lean_object* x_4861; lean_object* x_4862; lean_object* x_4863; lean_object* x_4864; lean_object* x_4865; lean_object* x_4866; lean_object* x_4867; 
x_4859 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_4860 = lean_ctor_get(x_4859, 0);
lean_inc(x_4860);
x_4861 = lean_ctor_get(x_4859, 1);
lean_inc(x_4861);
lean_dec(x_4859);
x_4862 = lean_unsigned_to_nat(1u);
x_4863 = lean_nat_add(x_3, x_4862);
lean_dec(x_3);
x_4864 = l_Lean_mkHole(x_14);
lean_inc(x_4860);
x_4865 = l_Lean_Elab_Term_mkExplicitBinder(x_4860, x_4864);
x_4866 = lean_array_push(x_4, x_4865);
lean_inc(x_5);
x_4867 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_4863, x_4866, x_5, x_4861);
if (lean_obj_tag(x_4867) == 0)
{
lean_object* x_4868; lean_object* x_4869; lean_object* x_4870; uint8_t x_4871; 
x_4868 = lean_ctor_get(x_4867, 0);
lean_inc(x_4868);
x_4869 = lean_ctor_get(x_4868, 1);
lean_inc(x_4869);
x_4870 = lean_ctor_get(x_4867, 1);
lean_inc(x_4870);
lean_dec(x_4867);
x_4871 = !lean_is_exclusive(x_4868);
if (x_4871 == 0)
{
lean_object* x_4872; uint8_t x_4873; 
x_4872 = lean_ctor_get(x_4868, 1);
lean_dec(x_4872);
x_4873 = !lean_is_exclusive(x_4869);
if (x_4873 == 0)
{
lean_object* x_4874; lean_object* x_4875; lean_object* x_4876; lean_object* x_4877; lean_object* x_4878; uint8_t x_4879; 
x_4874 = lean_ctor_get(x_4869, 0);
x_4875 = lean_ctor_get(x_4869, 1);
lean_dec(x_4875);
x_4876 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4870);
lean_dec(x_5);
x_4877 = lean_ctor_get(x_4876, 1);
lean_inc(x_4877);
lean_dec(x_4876);
x_4878 = l_Lean_Elab_Term_getMainModule___rarg(x_4877);
x_4879 = !lean_is_exclusive(x_4878);
if (x_4879 == 0)
{
lean_object* x_4880; lean_object* x_4881; lean_object* x_4882; lean_object* x_4883; lean_object* x_4884; lean_object* x_4885; lean_object* x_4886; lean_object* x_4887; lean_object* x_4888; lean_object* x_4889; lean_object* x_4890; lean_object* x_4891; lean_object* x_4892; lean_object* x_4893; lean_object* x_4894; lean_object* x_4895; lean_object* x_4896; lean_object* x_4897; lean_object* x_4898; lean_object* x_4899; lean_object* x_4900; lean_object* x_4901; uint8_t x_4902; 
x_4880 = lean_ctor_get(x_4878, 0);
lean_dec(x_4880);
x_4881 = l_Array_empty___closed__1;
x_4882 = lean_array_push(x_4881, x_4860);
x_4883 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4884 = lean_array_push(x_4882, x_4883);
x_4885 = l_Lean_mkTermIdFromIdent___closed__2;
x_4886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4886, 0, x_4885);
lean_ctor_set(x_4886, 1, x_4884);
x_4887 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4888 = lean_array_push(x_4887, x_4886);
x_4889 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4890, 0, x_4889);
lean_ctor_set(x_4890, 1, x_4888);
x_4891 = lean_array_push(x_4881, x_4890);
x_4892 = l_Lean_nullKind___closed__2;
x_4893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4893, 0, x_4892);
lean_ctor_set(x_4893, 1, x_4891);
x_4894 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4895 = lean_array_push(x_4894, x_4893);
x_4896 = lean_array_push(x_4895, x_4883);
x_4897 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4898 = lean_array_push(x_4896, x_4897);
x_4899 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4900 = lean_array_push(x_4898, x_4899);
lean_inc(x_14);
x_4901 = lean_array_push(x_4881, x_14);
x_4902 = !lean_is_exclusive(x_14);
if (x_4902 == 0)
{
lean_object* x_4903; lean_object* x_4904; lean_object* x_4905; lean_object* x_4906; lean_object* x_4907; lean_object* x_4908; lean_object* x_4909; lean_object* x_4910; lean_object* x_4911; lean_object* x_4912; lean_object* x_4913; lean_object* x_4914; lean_object* x_4915; lean_object* x_4916; 
x_4903 = lean_ctor_get(x_14, 1);
lean_dec(x_4903);
x_4904 = lean_ctor_get(x_14, 0);
lean_dec(x_4904);
lean_ctor_set(x_14, 1, x_4901);
lean_ctor_set(x_14, 0, x_4892);
x_4905 = lean_array_push(x_4881, x_14);
x_4906 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4907 = lean_array_push(x_4905, x_4906);
x_4908 = lean_array_push(x_4907, x_4874);
x_4909 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4910 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4910, 0, x_4909);
lean_ctor_set(x_4910, 1, x_4908);
x_4911 = lean_array_push(x_4881, x_4910);
x_4912 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4912, 0, x_4892);
lean_ctor_set(x_4912, 1, x_4911);
x_4913 = lean_array_push(x_4900, x_4912);
x_4914 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4915, 0, x_4914);
lean_ctor_set(x_4915, 1, x_4913);
x_4916 = lean_box(x_4857);
lean_ctor_set(x_4869, 1, x_4916);
lean_ctor_set(x_4869, 0, x_4915);
lean_ctor_set(x_4878, 0, x_4868);
return x_4878;
}
else
{
lean_object* x_4917; lean_object* x_4918; lean_object* x_4919; lean_object* x_4920; lean_object* x_4921; lean_object* x_4922; lean_object* x_4923; lean_object* x_4924; lean_object* x_4925; lean_object* x_4926; lean_object* x_4927; lean_object* x_4928; lean_object* x_4929; 
lean_dec(x_14);
x_4917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4917, 0, x_4892);
lean_ctor_set(x_4917, 1, x_4901);
x_4918 = lean_array_push(x_4881, x_4917);
x_4919 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4920 = lean_array_push(x_4918, x_4919);
x_4921 = lean_array_push(x_4920, x_4874);
x_4922 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4923, 0, x_4922);
lean_ctor_set(x_4923, 1, x_4921);
x_4924 = lean_array_push(x_4881, x_4923);
x_4925 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4925, 0, x_4892);
lean_ctor_set(x_4925, 1, x_4924);
x_4926 = lean_array_push(x_4900, x_4925);
x_4927 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4928 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4928, 0, x_4927);
lean_ctor_set(x_4928, 1, x_4926);
x_4929 = lean_box(x_4857);
lean_ctor_set(x_4869, 1, x_4929);
lean_ctor_set(x_4869, 0, x_4928);
lean_ctor_set(x_4878, 0, x_4868);
return x_4878;
}
}
else
{
lean_object* x_4930; lean_object* x_4931; lean_object* x_4932; lean_object* x_4933; lean_object* x_4934; lean_object* x_4935; lean_object* x_4936; lean_object* x_4937; lean_object* x_4938; lean_object* x_4939; lean_object* x_4940; lean_object* x_4941; lean_object* x_4942; lean_object* x_4943; lean_object* x_4944; lean_object* x_4945; lean_object* x_4946; lean_object* x_4947; lean_object* x_4948; lean_object* x_4949; lean_object* x_4950; lean_object* x_4951; lean_object* x_4952; lean_object* x_4953; lean_object* x_4954; lean_object* x_4955; lean_object* x_4956; lean_object* x_4957; lean_object* x_4958; lean_object* x_4959; lean_object* x_4960; lean_object* x_4961; lean_object* x_4962; lean_object* x_4963; lean_object* x_4964; lean_object* x_4965; lean_object* x_4966; 
x_4930 = lean_ctor_get(x_4878, 1);
lean_inc(x_4930);
lean_dec(x_4878);
x_4931 = l_Array_empty___closed__1;
x_4932 = lean_array_push(x_4931, x_4860);
x_4933 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4934 = lean_array_push(x_4932, x_4933);
x_4935 = l_Lean_mkTermIdFromIdent___closed__2;
x_4936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4936, 0, x_4935);
lean_ctor_set(x_4936, 1, x_4934);
x_4937 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4938 = lean_array_push(x_4937, x_4936);
x_4939 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4940, 0, x_4939);
lean_ctor_set(x_4940, 1, x_4938);
x_4941 = lean_array_push(x_4931, x_4940);
x_4942 = l_Lean_nullKind___closed__2;
x_4943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4943, 0, x_4942);
lean_ctor_set(x_4943, 1, x_4941);
x_4944 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4945 = lean_array_push(x_4944, x_4943);
x_4946 = lean_array_push(x_4945, x_4933);
x_4947 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4948 = lean_array_push(x_4946, x_4947);
x_4949 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4950 = lean_array_push(x_4948, x_4949);
lean_inc(x_14);
x_4951 = lean_array_push(x_4931, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4952 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4952 = lean_box(0);
}
if (lean_is_scalar(x_4952)) {
 x_4953 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4953 = x_4952;
}
lean_ctor_set(x_4953, 0, x_4942);
lean_ctor_set(x_4953, 1, x_4951);
x_4954 = lean_array_push(x_4931, x_4953);
x_4955 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4956 = lean_array_push(x_4954, x_4955);
x_4957 = lean_array_push(x_4956, x_4874);
x_4958 = l_Lean_Parser_Term_matchAlt___closed__2;
x_4959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4959, 0, x_4958);
lean_ctor_set(x_4959, 1, x_4957);
x_4960 = lean_array_push(x_4931, x_4959);
x_4961 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4961, 0, x_4942);
lean_ctor_set(x_4961, 1, x_4960);
x_4962 = lean_array_push(x_4950, x_4961);
x_4963 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4964, 0, x_4963);
lean_ctor_set(x_4964, 1, x_4962);
x_4965 = lean_box(x_4857);
lean_ctor_set(x_4869, 1, x_4965);
lean_ctor_set(x_4869, 0, x_4964);
x_4966 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4966, 0, x_4868);
lean_ctor_set(x_4966, 1, x_4930);
return x_4966;
}
}
else
{
lean_object* x_4967; lean_object* x_4968; lean_object* x_4969; lean_object* x_4970; lean_object* x_4971; lean_object* x_4972; lean_object* x_4973; lean_object* x_4974; lean_object* x_4975; lean_object* x_4976; lean_object* x_4977; lean_object* x_4978; lean_object* x_4979; lean_object* x_4980; lean_object* x_4981; lean_object* x_4982; lean_object* x_4983; lean_object* x_4984; lean_object* x_4985; lean_object* x_4986; lean_object* x_4987; lean_object* x_4988; lean_object* x_4989; lean_object* x_4990; lean_object* x_4991; lean_object* x_4992; lean_object* x_4993; lean_object* x_4994; lean_object* x_4995; lean_object* x_4996; lean_object* x_4997; lean_object* x_4998; lean_object* x_4999; lean_object* x_5000; lean_object* x_5001; lean_object* x_5002; lean_object* x_5003; lean_object* x_5004; lean_object* x_5005; lean_object* x_5006; lean_object* x_5007; lean_object* x_5008; lean_object* x_5009; 
x_4967 = lean_ctor_get(x_4869, 0);
lean_inc(x_4967);
lean_dec(x_4869);
x_4968 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4870);
lean_dec(x_5);
x_4969 = lean_ctor_get(x_4968, 1);
lean_inc(x_4969);
lean_dec(x_4968);
x_4970 = l_Lean_Elab_Term_getMainModule___rarg(x_4969);
x_4971 = lean_ctor_get(x_4970, 1);
lean_inc(x_4971);
if (lean_is_exclusive(x_4970)) {
 lean_ctor_release(x_4970, 0);
 lean_ctor_release(x_4970, 1);
 x_4972 = x_4970;
} else {
 lean_dec_ref(x_4970);
 x_4972 = lean_box(0);
}
x_4973 = l_Array_empty___closed__1;
x_4974 = lean_array_push(x_4973, x_4860);
x_4975 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_4976 = lean_array_push(x_4974, x_4975);
x_4977 = l_Lean_mkTermIdFromIdent___closed__2;
x_4978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4978, 0, x_4977);
lean_ctor_set(x_4978, 1, x_4976);
x_4979 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_4980 = lean_array_push(x_4979, x_4978);
x_4981 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_4982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4982, 0, x_4981);
lean_ctor_set(x_4982, 1, x_4980);
x_4983 = lean_array_push(x_4973, x_4982);
x_4984 = l_Lean_nullKind___closed__2;
x_4985 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4985, 0, x_4984);
lean_ctor_set(x_4985, 1, x_4983);
x_4986 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4987 = lean_array_push(x_4986, x_4985);
x_4988 = lean_array_push(x_4987, x_4975);
x_4989 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_4990 = lean_array_push(x_4988, x_4989);
x_4991 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_4992 = lean_array_push(x_4990, x_4991);
lean_inc(x_14);
x_4993 = lean_array_push(x_4973, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_4994 = x_14;
} else {
 lean_dec_ref(x_14);
 x_4994 = lean_box(0);
}
if (lean_is_scalar(x_4994)) {
 x_4995 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4995 = x_4994;
}
lean_ctor_set(x_4995, 0, x_4984);
lean_ctor_set(x_4995, 1, x_4993);
x_4996 = lean_array_push(x_4973, x_4995);
x_4997 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_4998 = lean_array_push(x_4996, x_4997);
x_4999 = lean_array_push(x_4998, x_4967);
x_5000 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5001 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5001, 0, x_5000);
lean_ctor_set(x_5001, 1, x_4999);
x_5002 = lean_array_push(x_4973, x_5001);
x_5003 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5003, 0, x_4984);
lean_ctor_set(x_5003, 1, x_5002);
x_5004 = lean_array_push(x_4992, x_5003);
x_5005 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5006, 0, x_5005);
lean_ctor_set(x_5006, 1, x_5004);
x_5007 = lean_box(x_4857);
x_5008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5008, 0, x_5006);
lean_ctor_set(x_5008, 1, x_5007);
lean_ctor_set(x_4868, 1, x_5008);
if (lean_is_scalar(x_4972)) {
 x_5009 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5009 = x_4972;
}
lean_ctor_set(x_5009, 0, x_4868);
lean_ctor_set(x_5009, 1, x_4971);
return x_5009;
}
}
else
{
lean_object* x_5010; lean_object* x_5011; lean_object* x_5012; lean_object* x_5013; lean_object* x_5014; lean_object* x_5015; lean_object* x_5016; lean_object* x_5017; lean_object* x_5018; lean_object* x_5019; lean_object* x_5020; lean_object* x_5021; lean_object* x_5022; lean_object* x_5023; lean_object* x_5024; lean_object* x_5025; lean_object* x_5026; lean_object* x_5027; lean_object* x_5028; lean_object* x_5029; lean_object* x_5030; lean_object* x_5031; lean_object* x_5032; lean_object* x_5033; lean_object* x_5034; lean_object* x_5035; lean_object* x_5036; lean_object* x_5037; lean_object* x_5038; lean_object* x_5039; lean_object* x_5040; lean_object* x_5041; lean_object* x_5042; lean_object* x_5043; lean_object* x_5044; lean_object* x_5045; lean_object* x_5046; lean_object* x_5047; lean_object* x_5048; lean_object* x_5049; lean_object* x_5050; lean_object* x_5051; lean_object* x_5052; lean_object* x_5053; lean_object* x_5054; lean_object* x_5055; 
x_5010 = lean_ctor_get(x_4868, 0);
lean_inc(x_5010);
lean_dec(x_4868);
x_5011 = lean_ctor_get(x_4869, 0);
lean_inc(x_5011);
if (lean_is_exclusive(x_4869)) {
 lean_ctor_release(x_4869, 0);
 lean_ctor_release(x_4869, 1);
 x_5012 = x_4869;
} else {
 lean_dec_ref(x_4869);
 x_5012 = lean_box(0);
}
x_5013 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_4870);
lean_dec(x_5);
x_5014 = lean_ctor_get(x_5013, 1);
lean_inc(x_5014);
lean_dec(x_5013);
x_5015 = l_Lean_Elab_Term_getMainModule___rarg(x_5014);
x_5016 = lean_ctor_get(x_5015, 1);
lean_inc(x_5016);
if (lean_is_exclusive(x_5015)) {
 lean_ctor_release(x_5015, 0);
 lean_ctor_release(x_5015, 1);
 x_5017 = x_5015;
} else {
 lean_dec_ref(x_5015);
 x_5017 = lean_box(0);
}
x_5018 = l_Array_empty___closed__1;
x_5019 = lean_array_push(x_5018, x_4860);
x_5020 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5021 = lean_array_push(x_5019, x_5020);
x_5022 = l_Lean_mkTermIdFromIdent___closed__2;
x_5023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5023, 0, x_5022);
lean_ctor_set(x_5023, 1, x_5021);
x_5024 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5025 = lean_array_push(x_5024, x_5023);
x_5026 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5027 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5027, 0, x_5026);
lean_ctor_set(x_5027, 1, x_5025);
x_5028 = lean_array_push(x_5018, x_5027);
x_5029 = l_Lean_nullKind___closed__2;
x_5030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5030, 0, x_5029);
lean_ctor_set(x_5030, 1, x_5028);
x_5031 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5032 = lean_array_push(x_5031, x_5030);
x_5033 = lean_array_push(x_5032, x_5020);
x_5034 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5035 = lean_array_push(x_5033, x_5034);
x_5036 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5037 = lean_array_push(x_5035, x_5036);
lean_inc(x_14);
x_5038 = lean_array_push(x_5018, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5039 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5039 = lean_box(0);
}
if (lean_is_scalar(x_5039)) {
 x_5040 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5040 = x_5039;
}
lean_ctor_set(x_5040, 0, x_5029);
lean_ctor_set(x_5040, 1, x_5038);
x_5041 = lean_array_push(x_5018, x_5040);
x_5042 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5043 = lean_array_push(x_5041, x_5042);
x_5044 = lean_array_push(x_5043, x_5011);
x_5045 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5046 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5046, 0, x_5045);
lean_ctor_set(x_5046, 1, x_5044);
x_5047 = lean_array_push(x_5018, x_5046);
x_5048 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5048, 0, x_5029);
lean_ctor_set(x_5048, 1, x_5047);
x_5049 = lean_array_push(x_5037, x_5048);
x_5050 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5051, 0, x_5050);
lean_ctor_set(x_5051, 1, x_5049);
x_5052 = lean_box(x_4857);
if (lean_is_scalar(x_5012)) {
 x_5053 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5053 = x_5012;
}
lean_ctor_set(x_5053, 0, x_5051);
lean_ctor_set(x_5053, 1, x_5052);
x_5054 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5054, 0, x_5010);
lean_ctor_set(x_5054, 1, x_5053);
if (lean_is_scalar(x_5017)) {
 x_5055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5055 = x_5017;
}
lean_ctor_set(x_5055, 0, x_5054);
lean_ctor_set(x_5055, 1, x_5016);
return x_5055;
}
}
else
{
uint8_t x_5056; 
lean_dec(x_4860);
lean_dec(x_14);
lean_dec(x_5);
x_5056 = !lean_is_exclusive(x_4867);
if (x_5056 == 0)
{
return x_4867;
}
else
{
lean_object* x_5057; lean_object* x_5058; lean_object* x_5059; 
x_5057 = lean_ctor_get(x_4867, 0);
x_5058 = lean_ctor_get(x_4867, 1);
lean_inc(x_5058);
lean_inc(x_5057);
lean_dec(x_4867);
x_5059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5059, 0, x_5057);
lean_ctor_set(x_5059, 1, x_5058);
return x_5059;
}
}
}
else
{
lean_object* x_5060; lean_object* x_5061; lean_object* x_5062; uint8_t x_5063; 
x_5060 = lean_ctor_get(x_4858, 0);
lean_inc(x_5060);
lean_dec(x_4858);
x_5061 = lean_ctor_get(x_5060, 0);
lean_inc(x_5061);
x_5062 = lean_ctor_get(x_5060, 1);
lean_inc(x_5062);
lean_dec(x_5060);
x_5063 = l_Lean_Syntax_isNone(x_5062);
lean_dec(x_5062);
if (x_5063 == 0)
{
lean_object* x_5064; lean_object* x_5065; uint8_t x_5066; 
lean_dec(x_5061);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_5064 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_5065 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_5064, x_5, x_6);
lean_dec(x_14);
x_5066 = !lean_is_exclusive(x_5065);
if (x_5066 == 0)
{
return x_5065;
}
else
{
lean_object* x_5067; lean_object* x_5068; lean_object* x_5069; 
x_5067 = lean_ctor_get(x_5065, 0);
x_5068 = lean_ctor_get(x_5065, 1);
lean_inc(x_5068);
lean_inc(x_5067);
lean_dec(x_5065);
x_5069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5069, 0, x_5067);
lean_ctor_set(x_5069, 1, x_5068);
return x_5069;
}
}
else
{
lean_object* x_5070; lean_object* x_5071; lean_object* x_5072; lean_object* x_5073; lean_object* x_5074; 
x_5070 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_5071 = lean_unsigned_to_nat(1u);
x_5072 = lean_nat_add(x_3, x_5071);
lean_dec(x_3);
x_5073 = l_Lean_Elab_Term_mkExplicitBinder(x_5061, x_5070);
x_5074 = lean_array_push(x_4, x_5073);
x_3 = x_5072;
x_4 = x_5074;
goto _start;
}
}
}
}
else
{
uint8_t x_5076; lean_object* x_5077; 
lean_dec(x_16);
lean_dec(x_15);
x_5076 = 1;
lean_inc(x_14);
x_5077 = l_Lean_Syntax_isTermId_x3f(x_14, x_5076);
if (lean_obj_tag(x_5077) == 0)
{
lean_object* x_5078; lean_object* x_5079; lean_object* x_5080; lean_object* x_5081; lean_object* x_5082; lean_object* x_5083; lean_object* x_5084; lean_object* x_5085; lean_object* x_5086; 
x_5078 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_5079 = lean_ctor_get(x_5078, 0);
lean_inc(x_5079);
x_5080 = lean_ctor_get(x_5078, 1);
lean_inc(x_5080);
lean_dec(x_5078);
x_5081 = lean_unsigned_to_nat(1u);
x_5082 = lean_nat_add(x_3, x_5081);
lean_dec(x_3);
x_5083 = l_Lean_mkHole(x_14);
lean_inc(x_5079);
x_5084 = l_Lean_Elab_Term_mkExplicitBinder(x_5079, x_5083);
x_5085 = lean_array_push(x_4, x_5084);
lean_inc(x_5);
x_5086 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_5082, x_5085, x_5, x_5080);
if (lean_obj_tag(x_5086) == 0)
{
lean_object* x_5087; lean_object* x_5088; lean_object* x_5089; uint8_t x_5090; 
x_5087 = lean_ctor_get(x_5086, 0);
lean_inc(x_5087);
x_5088 = lean_ctor_get(x_5087, 1);
lean_inc(x_5088);
x_5089 = lean_ctor_get(x_5086, 1);
lean_inc(x_5089);
lean_dec(x_5086);
x_5090 = !lean_is_exclusive(x_5087);
if (x_5090 == 0)
{
lean_object* x_5091; uint8_t x_5092; 
x_5091 = lean_ctor_get(x_5087, 1);
lean_dec(x_5091);
x_5092 = !lean_is_exclusive(x_5088);
if (x_5092 == 0)
{
lean_object* x_5093; lean_object* x_5094; lean_object* x_5095; lean_object* x_5096; lean_object* x_5097; uint8_t x_5098; 
x_5093 = lean_ctor_get(x_5088, 0);
x_5094 = lean_ctor_get(x_5088, 1);
lean_dec(x_5094);
x_5095 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5089);
lean_dec(x_5);
x_5096 = lean_ctor_get(x_5095, 1);
lean_inc(x_5096);
lean_dec(x_5095);
x_5097 = l_Lean_Elab_Term_getMainModule___rarg(x_5096);
x_5098 = !lean_is_exclusive(x_5097);
if (x_5098 == 0)
{
lean_object* x_5099; lean_object* x_5100; lean_object* x_5101; lean_object* x_5102; lean_object* x_5103; lean_object* x_5104; lean_object* x_5105; lean_object* x_5106; lean_object* x_5107; lean_object* x_5108; lean_object* x_5109; lean_object* x_5110; lean_object* x_5111; lean_object* x_5112; lean_object* x_5113; lean_object* x_5114; lean_object* x_5115; lean_object* x_5116; lean_object* x_5117; lean_object* x_5118; lean_object* x_5119; lean_object* x_5120; uint8_t x_5121; 
x_5099 = lean_ctor_get(x_5097, 0);
lean_dec(x_5099);
x_5100 = l_Array_empty___closed__1;
x_5101 = lean_array_push(x_5100, x_5079);
x_5102 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5103 = lean_array_push(x_5101, x_5102);
x_5104 = l_Lean_mkTermIdFromIdent___closed__2;
x_5105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5105, 0, x_5104);
lean_ctor_set(x_5105, 1, x_5103);
x_5106 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5107 = lean_array_push(x_5106, x_5105);
x_5108 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5109, 0, x_5108);
lean_ctor_set(x_5109, 1, x_5107);
x_5110 = lean_array_push(x_5100, x_5109);
x_5111 = l_Lean_nullKind___closed__2;
x_5112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5112, 0, x_5111);
lean_ctor_set(x_5112, 1, x_5110);
x_5113 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5114 = lean_array_push(x_5113, x_5112);
x_5115 = lean_array_push(x_5114, x_5102);
x_5116 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5117 = lean_array_push(x_5115, x_5116);
x_5118 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5119 = lean_array_push(x_5117, x_5118);
lean_inc(x_14);
x_5120 = lean_array_push(x_5100, x_14);
x_5121 = !lean_is_exclusive(x_14);
if (x_5121 == 0)
{
lean_object* x_5122; lean_object* x_5123; lean_object* x_5124; lean_object* x_5125; lean_object* x_5126; lean_object* x_5127; lean_object* x_5128; lean_object* x_5129; lean_object* x_5130; lean_object* x_5131; lean_object* x_5132; lean_object* x_5133; lean_object* x_5134; lean_object* x_5135; 
x_5122 = lean_ctor_get(x_14, 1);
lean_dec(x_5122);
x_5123 = lean_ctor_get(x_14, 0);
lean_dec(x_5123);
lean_ctor_set(x_14, 1, x_5120);
lean_ctor_set(x_14, 0, x_5111);
x_5124 = lean_array_push(x_5100, x_14);
x_5125 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5126 = lean_array_push(x_5124, x_5125);
x_5127 = lean_array_push(x_5126, x_5093);
x_5128 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5129, 0, x_5128);
lean_ctor_set(x_5129, 1, x_5127);
x_5130 = lean_array_push(x_5100, x_5129);
x_5131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5131, 0, x_5111);
lean_ctor_set(x_5131, 1, x_5130);
x_5132 = lean_array_push(x_5119, x_5131);
x_5133 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5134, 0, x_5133);
lean_ctor_set(x_5134, 1, x_5132);
x_5135 = lean_box(x_5076);
lean_ctor_set(x_5088, 1, x_5135);
lean_ctor_set(x_5088, 0, x_5134);
lean_ctor_set(x_5097, 0, x_5087);
return x_5097;
}
else
{
lean_object* x_5136; lean_object* x_5137; lean_object* x_5138; lean_object* x_5139; lean_object* x_5140; lean_object* x_5141; lean_object* x_5142; lean_object* x_5143; lean_object* x_5144; lean_object* x_5145; lean_object* x_5146; lean_object* x_5147; lean_object* x_5148; 
lean_dec(x_14);
x_5136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5136, 0, x_5111);
lean_ctor_set(x_5136, 1, x_5120);
x_5137 = lean_array_push(x_5100, x_5136);
x_5138 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5139 = lean_array_push(x_5137, x_5138);
x_5140 = lean_array_push(x_5139, x_5093);
x_5141 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5142, 0, x_5141);
lean_ctor_set(x_5142, 1, x_5140);
x_5143 = lean_array_push(x_5100, x_5142);
x_5144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5144, 0, x_5111);
lean_ctor_set(x_5144, 1, x_5143);
x_5145 = lean_array_push(x_5119, x_5144);
x_5146 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5147, 0, x_5146);
lean_ctor_set(x_5147, 1, x_5145);
x_5148 = lean_box(x_5076);
lean_ctor_set(x_5088, 1, x_5148);
lean_ctor_set(x_5088, 0, x_5147);
lean_ctor_set(x_5097, 0, x_5087);
return x_5097;
}
}
else
{
lean_object* x_5149; lean_object* x_5150; lean_object* x_5151; lean_object* x_5152; lean_object* x_5153; lean_object* x_5154; lean_object* x_5155; lean_object* x_5156; lean_object* x_5157; lean_object* x_5158; lean_object* x_5159; lean_object* x_5160; lean_object* x_5161; lean_object* x_5162; lean_object* x_5163; lean_object* x_5164; lean_object* x_5165; lean_object* x_5166; lean_object* x_5167; lean_object* x_5168; lean_object* x_5169; lean_object* x_5170; lean_object* x_5171; lean_object* x_5172; lean_object* x_5173; lean_object* x_5174; lean_object* x_5175; lean_object* x_5176; lean_object* x_5177; lean_object* x_5178; lean_object* x_5179; lean_object* x_5180; lean_object* x_5181; lean_object* x_5182; lean_object* x_5183; lean_object* x_5184; lean_object* x_5185; 
x_5149 = lean_ctor_get(x_5097, 1);
lean_inc(x_5149);
lean_dec(x_5097);
x_5150 = l_Array_empty___closed__1;
x_5151 = lean_array_push(x_5150, x_5079);
x_5152 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5153 = lean_array_push(x_5151, x_5152);
x_5154 = l_Lean_mkTermIdFromIdent___closed__2;
x_5155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5155, 0, x_5154);
lean_ctor_set(x_5155, 1, x_5153);
x_5156 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5157 = lean_array_push(x_5156, x_5155);
x_5158 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5159, 0, x_5158);
lean_ctor_set(x_5159, 1, x_5157);
x_5160 = lean_array_push(x_5150, x_5159);
x_5161 = l_Lean_nullKind___closed__2;
x_5162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5162, 0, x_5161);
lean_ctor_set(x_5162, 1, x_5160);
x_5163 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5164 = lean_array_push(x_5163, x_5162);
x_5165 = lean_array_push(x_5164, x_5152);
x_5166 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5167 = lean_array_push(x_5165, x_5166);
x_5168 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5169 = lean_array_push(x_5167, x_5168);
lean_inc(x_14);
x_5170 = lean_array_push(x_5150, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5171 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5171 = lean_box(0);
}
if (lean_is_scalar(x_5171)) {
 x_5172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5172 = x_5171;
}
lean_ctor_set(x_5172, 0, x_5161);
lean_ctor_set(x_5172, 1, x_5170);
x_5173 = lean_array_push(x_5150, x_5172);
x_5174 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5175 = lean_array_push(x_5173, x_5174);
x_5176 = lean_array_push(x_5175, x_5093);
x_5177 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5178, 0, x_5177);
lean_ctor_set(x_5178, 1, x_5176);
x_5179 = lean_array_push(x_5150, x_5178);
x_5180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5180, 0, x_5161);
lean_ctor_set(x_5180, 1, x_5179);
x_5181 = lean_array_push(x_5169, x_5180);
x_5182 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5183, 0, x_5182);
lean_ctor_set(x_5183, 1, x_5181);
x_5184 = lean_box(x_5076);
lean_ctor_set(x_5088, 1, x_5184);
lean_ctor_set(x_5088, 0, x_5183);
x_5185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5185, 0, x_5087);
lean_ctor_set(x_5185, 1, x_5149);
return x_5185;
}
}
else
{
lean_object* x_5186; lean_object* x_5187; lean_object* x_5188; lean_object* x_5189; lean_object* x_5190; lean_object* x_5191; lean_object* x_5192; lean_object* x_5193; lean_object* x_5194; lean_object* x_5195; lean_object* x_5196; lean_object* x_5197; lean_object* x_5198; lean_object* x_5199; lean_object* x_5200; lean_object* x_5201; lean_object* x_5202; lean_object* x_5203; lean_object* x_5204; lean_object* x_5205; lean_object* x_5206; lean_object* x_5207; lean_object* x_5208; lean_object* x_5209; lean_object* x_5210; lean_object* x_5211; lean_object* x_5212; lean_object* x_5213; lean_object* x_5214; lean_object* x_5215; lean_object* x_5216; lean_object* x_5217; lean_object* x_5218; lean_object* x_5219; lean_object* x_5220; lean_object* x_5221; lean_object* x_5222; lean_object* x_5223; lean_object* x_5224; lean_object* x_5225; lean_object* x_5226; lean_object* x_5227; lean_object* x_5228; 
x_5186 = lean_ctor_get(x_5088, 0);
lean_inc(x_5186);
lean_dec(x_5088);
x_5187 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5089);
lean_dec(x_5);
x_5188 = lean_ctor_get(x_5187, 1);
lean_inc(x_5188);
lean_dec(x_5187);
x_5189 = l_Lean_Elab_Term_getMainModule___rarg(x_5188);
x_5190 = lean_ctor_get(x_5189, 1);
lean_inc(x_5190);
if (lean_is_exclusive(x_5189)) {
 lean_ctor_release(x_5189, 0);
 lean_ctor_release(x_5189, 1);
 x_5191 = x_5189;
} else {
 lean_dec_ref(x_5189);
 x_5191 = lean_box(0);
}
x_5192 = l_Array_empty___closed__1;
x_5193 = lean_array_push(x_5192, x_5079);
x_5194 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5195 = lean_array_push(x_5193, x_5194);
x_5196 = l_Lean_mkTermIdFromIdent___closed__2;
x_5197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5197, 0, x_5196);
lean_ctor_set(x_5197, 1, x_5195);
x_5198 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5199 = lean_array_push(x_5198, x_5197);
x_5200 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5201, 0, x_5200);
lean_ctor_set(x_5201, 1, x_5199);
x_5202 = lean_array_push(x_5192, x_5201);
x_5203 = l_Lean_nullKind___closed__2;
x_5204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5204, 0, x_5203);
lean_ctor_set(x_5204, 1, x_5202);
x_5205 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5206 = lean_array_push(x_5205, x_5204);
x_5207 = lean_array_push(x_5206, x_5194);
x_5208 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5209 = lean_array_push(x_5207, x_5208);
x_5210 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5211 = lean_array_push(x_5209, x_5210);
lean_inc(x_14);
x_5212 = lean_array_push(x_5192, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5213 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5213 = lean_box(0);
}
if (lean_is_scalar(x_5213)) {
 x_5214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5214 = x_5213;
}
lean_ctor_set(x_5214, 0, x_5203);
lean_ctor_set(x_5214, 1, x_5212);
x_5215 = lean_array_push(x_5192, x_5214);
x_5216 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5217 = lean_array_push(x_5215, x_5216);
x_5218 = lean_array_push(x_5217, x_5186);
x_5219 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5220, 0, x_5219);
lean_ctor_set(x_5220, 1, x_5218);
x_5221 = lean_array_push(x_5192, x_5220);
x_5222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5222, 0, x_5203);
lean_ctor_set(x_5222, 1, x_5221);
x_5223 = lean_array_push(x_5211, x_5222);
x_5224 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5225, 0, x_5224);
lean_ctor_set(x_5225, 1, x_5223);
x_5226 = lean_box(x_5076);
x_5227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5227, 0, x_5225);
lean_ctor_set(x_5227, 1, x_5226);
lean_ctor_set(x_5087, 1, x_5227);
if (lean_is_scalar(x_5191)) {
 x_5228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5228 = x_5191;
}
lean_ctor_set(x_5228, 0, x_5087);
lean_ctor_set(x_5228, 1, x_5190);
return x_5228;
}
}
else
{
lean_object* x_5229; lean_object* x_5230; lean_object* x_5231; lean_object* x_5232; lean_object* x_5233; lean_object* x_5234; lean_object* x_5235; lean_object* x_5236; lean_object* x_5237; lean_object* x_5238; lean_object* x_5239; lean_object* x_5240; lean_object* x_5241; lean_object* x_5242; lean_object* x_5243; lean_object* x_5244; lean_object* x_5245; lean_object* x_5246; lean_object* x_5247; lean_object* x_5248; lean_object* x_5249; lean_object* x_5250; lean_object* x_5251; lean_object* x_5252; lean_object* x_5253; lean_object* x_5254; lean_object* x_5255; lean_object* x_5256; lean_object* x_5257; lean_object* x_5258; lean_object* x_5259; lean_object* x_5260; lean_object* x_5261; lean_object* x_5262; lean_object* x_5263; lean_object* x_5264; lean_object* x_5265; lean_object* x_5266; lean_object* x_5267; lean_object* x_5268; lean_object* x_5269; lean_object* x_5270; lean_object* x_5271; lean_object* x_5272; lean_object* x_5273; lean_object* x_5274; 
x_5229 = lean_ctor_get(x_5087, 0);
lean_inc(x_5229);
lean_dec(x_5087);
x_5230 = lean_ctor_get(x_5088, 0);
lean_inc(x_5230);
if (lean_is_exclusive(x_5088)) {
 lean_ctor_release(x_5088, 0);
 lean_ctor_release(x_5088, 1);
 x_5231 = x_5088;
} else {
 lean_dec_ref(x_5088);
 x_5231 = lean_box(0);
}
x_5232 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5089);
lean_dec(x_5);
x_5233 = lean_ctor_get(x_5232, 1);
lean_inc(x_5233);
lean_dec(x_5232);
x_5234 = l_Lean_Elab_Term_getMainModule___rarg(x_5233);
x_5235 = lean_ctor_get(x_5234, 1);
lean_inc(x_5235);
if (lean_is_exclusive(x_5234)) {
 lean_ctor_release(x_5234, 0);
 lean_ctor_release(x_5234, 1);
 x_5236 = x_5234;
} else {
 lean_dec_ref(x_5234);
 x_5236 = lean_box(0);
}
x_5237 = l_Array_empty___closed__1;
x_5238 = lean_array_push(x_5237, x_5079);
x_5239 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5240 = lean_array_push(x_5238, x_5239);
x_5241 = l_Lean_mkTermIdFromIdent___closed__2;
x_5242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5242, 0, x_5241);
lean_ctor_set(x_5242, 1, x_5240);
x_5243 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5244 = lean_array_push(x_5243, x_5242);
x_5245 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5246, 0, x_5245);
lean_ctor_set(x_5246, 1, x_5244);
x_5247 = lean_array_push(x_5237, x_5246);
x_5248 = l_Lean_nullKind___closed__2;
x_5249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5249, 0, x_5248);
lean_ctor_set(x_5249, 1, x_5247);
x_5250 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5251 = lean_array_push(x_5250, x_5249);
x_5252 = lean_array_push(x_5251, x_5239);
x_5253 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5254 = lean_array_push(x_5252, x_5253);
x_5255 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5256 = lean_array_push(x_5254, x_5255);
lean_inc(x_14);
x_5257 = lean_array_push(x_5237, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5258 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5258 = lean_box(0);
}
if (lean_is_scalar(x_5258)) {
 x_5259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5259 = x_5258;
}
lean_ctor_set(x_5259, 0, x_5248);
lean_ctor_set(x_5259, 1, x_5257);
x_5260 = lean_array_push(x_5237, x_5259);
x_5261 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5262 = lean_array_push(x_5260, x_5261);
x_5263 = lean_array_push(x_5262, x_5230);
x_5264 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5265, 0, x_5264);
lean_ctor_set(x_5265, 1, x_5263);
x_5266 = lean_array_push(x_5237, x_5265);
x_5267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5267, 0, x_5248);
lean_ctor_set(x_5267, 1, x_5266);
x_5268 = lean_array_push(x_5256, x_5267);
x_5269 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5270, 0, x_5269);
lean_ctor_set(x_5270, 1, x_5268);
x_5271 = lean_box(x_5076);
if (lean_is_scalar(x_5231)) {
 x_5272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5272 = x_5231;
}
lean_ctor_set(x_5272, 0, x_5270);
lean_ctor_set(x_5272, 1, x_5271);
x_5273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5273, 0, x_5229);
lean_ctor_set(x_5273, 1, x_5272);
if (lean_is_scalar(x_5236)) {
 x_5274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5274 = x_5236;
}
lean_ctor_set(x_5274, 0, x_5273);
lean_ctor_set(x_5274, 1, x_5235);
return x_5274;
}
}
else
{
uint8_t x_5275; 
lean_dec(x_5079);
lean_dec(x_14);
lean_dec(x_5);
x_5275 = !lean_is_exclusive(x_5086);
if (x_5275 == 0)
{
return x_5086;
}
else
{
lean_object* x_5276; lean_object* x_5277; lean_object* x_5278; 
x_5276 = lean_ctor_get(x_5086, 0);
x_5277 = lean_ctor_get(x_5086, 1);
lean_inc(x_5277);
lean_inc(x_5276);
lean_dec(x_5086);
x_5278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5278, 0, x_5276);
lean_ctor_set(x_5278, 1, x_5277);
return x_5278;
}
}
}
else
{
lean_object* x_5279; lean_object* x_5280; lean_object* x_5281; uint8_t x_5282; 
x_5279 = lean_ctor_get(x_5077, 0);
lean_inc(x_5279);
lean_dec(x_5077);
x_5280 = lean_ctor_get(x_5279, 0);
lean_inc(x_5280);
x_5281 = lean_ctor_get(x_5279, 1);
lean_inc(x_5281);
lean_dec(x_5279);
x_5282 = l_Lean_Syntax_isNone(x_5281);
lean_dec(x_5281);
if (x_5282 == 0)
{
lean_object* x_5283; lean_object* x_5284; uint8_t x_5285; 
lean_dec(x_5280);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_5283 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_5284 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_5283, x_5, x_6);
lean_dec(x_14);
x_5285 = !lean_is_exclusive(x_5284);
if (x_5285 == 0)
{
return x_5284;
}
else
{
lean_object* x_5286; lean_object* x_5287; lean_object* x_5288; 
x_5286 = lean_ctor_get(x_5284, 0);
x_5287 = lean_ctor_get(x_5284, 1);
lean_inc(x_5287);
lean_inc(x_5286);
lean_dec(x_5284);
x_5288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5288, 0, x_5286);
lean_ctor_set(x_5288, 1, x_5287);
return x_5288;
}
}
else
{
lean_object* x_5289; lean_object* x_5290; lean_object* x_5291; lean_object* x_5292; lean_object* x_5293; 
x_5289 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_5290 = lean_unsigned_to_nat(1u);
x_5291 = lean_nat_add(x_3, x_5290);
lean_dec(x_3);
x_5292 = l_Lean_Elab_Term_mkExplicitBinder(x_5280, x_5289);
x_5293 = lean_array_push(x_4, x_5292);
x_3 = x_5291;
x_4 = x_5293;
goto _start;
}
}
}
}
else
{
uint8_t x_5295; lean_object* x_5296; 
lean_dec(x_15);
x_5295 = 1;
lean_inc(x_14);
x_5296 = l_Lean_Syntax_isTermId_x3f(x_14, x_5295);
if (lean_obj_tag(x_5296) == 0)
{
lean_object* x_5297; lean_object* x_5298; lean_object* x_5299; lean_object* x_5300; lean_object* x_5301; lean_object* x_5302; lean_object* x_5303; lean_object* x_5304; lean_object* x_5305; 
x_5297 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_5298 = lean_ctor_get(x_5297, 0);
lean_inc(x_5298);
x_5299 = lean_ctor_get(x_5297, 1);
lean_inc(x_5299);
lean_dec(x_5297);
x_5300 = lean_unsigned_to_nat(1u);
x_5301 = lean_nat_add(x_3, x_5300);
lean_dec(x_3);
x_5302 = l_Lean_mkHole(x_14);
lean_inc(x_5298);
x_5303 = l_Lean_Elab_Term_mkExplicitBinder(x_5298, x_5302);
x_5304 = lean_array_push(x_4, x_5303);
lean_inc(x_5);
x_5305 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_5301, x_5304, x_5, x_5299);
if (lean_obj_tag(x_5305) == 0)
{
lean_object* x_5306; lean_object* x_5307; lean_object* x_5308; uint8_t x_5309; 
x_5306 = lean_ctor_get(x_5305, 0);
lean_inc(x_5306);
x_5307 = lean_ctor_get(x_5306, 1);
lean_inc(x_5307);
x_5308 = lean_ctor_get(x_5305, 1);
lean_inc(x_5308);
lean_dec(x_5305);
x_5309 = !lean_is_exclusive(x_5306);
if (x_5309 == 0)
{
lean_object* x_5310; uint8_t x_5311; 
x_5310 = lean_ctor_get(x_5306, 1);
lean_dec(x_5310);
x_5311 = !lean_is_exclusive(x_5307);
if (x_5311 == 0)
{
lean_object* x_5312; lean_object* x_5313; lean_object* x_5314; lean_object* x_5315; lean_object* x_5316; uint8_t x_5317; 
x_5312 = lean_ctor_get(x_5307, 0);
x_5313 = lean_ctor_get(x_5307, 1);
lean_dec(x_5313);
x_5314 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5308);
lean_dec(x_5);
x_5315 = lean_ctor_get(x_5314, 1);
lean_inc(x_5315);
lean_dec(x_5314);
x_5316 = l_Lean_Elab_Term_getMainModule___rarg(x_5315);
x_5317 = !lean_is_exclusive(x_5316);
if (x_5317 == 0)
{
lean_object* x_5318; lean_object* x_5319; lean_object* x_5320; lean_object* x_5321; lean_object* x_5322; lean_object* x_5323; lean_object* x_5324; lean_object* x_5325; lean_object* x_5326; lean_object* x_5327; lean_object* x_5328; lean_object* x_5329; lean_object* x_5330; lean_object* x_5331; lean_object* x_5332; lean_object* x_5333; lean_object* x_5334; lean_object* x_5335; lean_object* x_5336; lean_object* x_5337; lean_object* x_5338; lean_object* x_5339; uint8_t x_5340; 
x_5318 = lean_ctor_get(x_5316, 0);
lean_dec(x_5318);
x_5319 = l_Array_empty___closed__1;
x_5320 = lean_array_push(x_5319, x_5298);
x_5321 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5322 = lean_array_push(x_5320, x_5321);
x_5323 = l_Lean_mkTermIdFromIdent___closed__2;
x_5324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5324, 0, x_5323);
lean_ctor_set(x_5324, 1, x_5322);
x_5325 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5326 = lean_array_push(x_5325, x_5324);
x_5327 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5328, 0, x_5327);
lean_ctor_set(x_5328, 1, x_5326);
x_5329 = lean_array_push(x_5319, x_5328);
x_5330 = l_Lean_nullKind___closed__2;
x_5331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5331, 0, x_5330);
lean_ctor_set(x_5331, 1, x_5329);
x_5332 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5333 = lean_array_push(x_5332, x_5331);
x_5334 = lean_array_push(x_5333, x_5321);
x_5335 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5336 = lean_array_push(x_5334, x_5335);
x_5337 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5338 = lean_array_push(x_5336, x_5337);
lean_inc(x_14);
x_5339 = lean_array_push(x_5319, x_14);
x_5340 = !lean_is_exclusive(x_14);
if (x_5340 == 0)
{
lean_object* x_5341; lean_object* x_5342; lean_object* x_5343; lean_object* x_5344; lean_object* x_5345; lean_object* x_5346; lean_object* x_5347; lean_object* x_5348; lean_object* x_5349; lean_object* x_5350; lean_object* x_5351; lean_object* x_5352; lean_object* x_5353; lean_object* x_5354; 
x_5341 = lean_ctor_get(x_14, 1);
lean_dec(x_5341);
x_5342 = lean_ctor_get(x_14, 0);
lean_dec(x_5342);
lean_ctor_set(x_14, 1, x_5339);
lean_ctor_set(x_14, 0, x_5330);
x_5343 = lean_array_push(x_5319, x_14);
x_5344 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5345 = lean_array_push(x_5343, x_5344);
x_5346 = lean_array_push(x_5345, x_5312);
x_5347 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5348, 0, x_5347);
lean_ctor_set(x_5348, 1, x_5346);
x_5349 = lean_array_push(x_5319, x_5348);
x_5350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5350, 0, x_5330);
lean_ctor_set(x_5350, 1, x_5349);
x_5351 = lean_array_push(x_5338, x_5350);
x_5352 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5353, 0, x_5352);
lean_ctor_set(x_5353, 1, x_5351);
x_5354 = lean_box(x_5295);
lean_ctor_set(x_5307, 1, x_5354);
lean_ctor_set(x_5307, 0, x_5353);
lean_ctor_set(x_5316, 0, x_5306);
return x_5316;
}
else
{
lean_object* x_5355; lean_object* x_5356; lean_object* x_5357; lean_object* x_5358; lean_object* x_5359; lean_object* x_5360; lean_object* x_5361; lean_object* x_5362; lean_object* x_5363; lean_object* x_5364; lean_object* x_5365; lean_object* x_5366; lean_object* x_5367; 
lean_dec(x_14);
x_5355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5355, 0, x_5330);
lean_ctor_set(x_5355, 1, x_5339);
x_5356 = lean_array_push(x_5319, x_5355);
x_5357 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5358 = lean_array_push(x_5356, x_5357);
x_5359 = lean_array_push(x_5358, x_5312);
x_5360 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5361, 0, x_5360);
lean_ctor_set(x_5361, 1, x_5359);
x_5362 = lean_array_push(x_5319, x_5361);
x_5363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5363, 0, x_5330);
lean_ctor_set(x_5363, 1, x_5362);
x_5364 = lean_array_push(x_5338, x_5363);
x_5365 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5366, 0, x_5365);
lean_ctor_set(x_5366, 1, x_5364);
x_5367 = lean_box(x_5295);
lean_ctor_set(x_5307, 1, x_5367);
lean_ctor_set(x_5307, 0, x_5366);
lean_ctor_set(x_5316, 0, x_5306);
return x_5316;
}
}
else
{
lean_object* x_5368; lean_object* x_5369; lean_object* x_5370; lean_object* x_5371; lean_object* x_5372; lean_object* x_5373; lean_object* x_5374; lean_object* x_5375; lean_object* x_5376; lean_object* x_5377; lean_object* x_5378; lean_object* x_5379; lean_object* x_5380; lean_object* x_5381; lean_object* x_5382; lean_object* x_5383; lean_object* x_5384; lean_object* x_5385; lean_object* x_5386; lean_object* x_5387; lean_object* x_5388; lean_object* x_5389; lean_object* x_5390; lean_object* x_5391; lean_object* x_5392; lean_object* x_5393; lean_object* x_5394; lean_object* x_5395; lean_object* x_5396; lean_object* x_5397; lean_object* x_5398; lean_object* x_5399; lean_object* x_5400; lean_object* x_5401; lean_object* x_5402; lean_object* x_5403; lean_object* x_5404; 
x_5368 = lean_ctor_get(x_5316, 1);
lean_inc(x_5368);
lean_dec(x_5316);
x_5369 = l_Array_empty___closed__1;
x_5370 = lean_array_push(x_5369, x_5298);
x_5371 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5372 = lean_array_push(x_5370, x_5371);
x_5373 = l_Lean_mkTermIdFromIdent___closed__2;
x_5374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5374, 0, x_5373);
lean_ctor_set(x_5374, 1, x_5372);
x_5375 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5376 = lean_array_push(x_5375, x_5374);
x_5377 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5378, 0, x_5377);
lean_ctor_set(x_5378, 1, x_5376);
x_5379 = lean_array_push(x_5369, x_5378);
x_5380 = l_Lean_nullKind___closed__2;
x_5381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5381, 0, x_5380);
lean_ctor_set(x_5381, 1, x_5379);
x_5382 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5383 = lean_array_push(x_5382, x_5381);
x_5384 = lean_array_push(x_5383, x_5371);
x_5385 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5386 = lean_array_push(x_5384, x_5385);
x_5387 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5388 = lean_array_push(x_5386, x_5387);
lean_inc(x_14);
x_5389 = lean_array_push(x_5369, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5390 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5390 = lean_box(0);
}
if (lean_is_scalar(x_5390)) {
 x_5391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5391 = x_5390;
}
lean_ctor_set(x_5391, 0, x_5380);
lean_ctor_set(x_5391, 1, x_5389);
x_5392 = lean_array_push(x_5369, x_5391);
x_5393 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5394 = lean_array_push(x_5392, x_5393);
x_5395 = lean_array_push(x_5394, x_5312);
x_5396 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5397, 0, x_5396);
lean_ctor_set(x_5397, 1, x_5395);
x_5398 = lean_array_push(x_5369, x_5397);
x_5399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5399, 0, x_5380);
lean_ctor_set(x_5399, 1, x_5398);
x_5400 = lean_array_push(x_5388, x_5399);
x_5401 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5402, 0, x_5401);
lean_ctor_set(x_5402, 1, x_5400);
x_5403 = lean_box(x_5295);
lean_ctor_set(x_5307, 1, x_5403);
lean_ctor_set(x_5307, 0, x_5402);
x_5404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5404, 0, x_5306);
lean_ctor_set(x_5404, 1, x_5368);
return x_5404;
}
}
else
{
lean_object* x_5405; lean_object* x_5406; lean_object* x_5407; lean_object* x_5408; lean_object* x_5409; lean_object* x_5410; lean_object* x_5411; lean_object* x_5412; lean_object* x_5413; lean_object* x_5414; lean_object* x_5415; lean_object* x_5416; lean_object* x_5417; lean_object* x_5418; lean_object* x_5419; lean_object* x_5420; lean_object* x_5421; lean_object* x_5422; lean_object* x_5423; lean_object* x_5424; lean_object* x_5425; lean_object* x_5426; lean_object* x_5427; lean_object* x_5428; lean_object* x_5429; lean_object* x_5430; lean_object* x_5431; lean_object* x_5432; lean_object* x_5433; lean_object* x_5434; lean_object* x_5435; lean_object* x_5436; lean_object* x_5437; lean_object* x_5438; lean_object* x_5439; lean_object* x_5440; lean_object* x_5441; lean_object* x_5442; lean_object* x_5443; lean_object* x_5444; lean_object* x_5445; lean_object* x_5446; lean_object* x_5447; 
x_5405 = lean_ctor_get(x_5307, 0);
lean_inc(x_5405);
lean_dec(x_5307);
x_5406 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5308);
lean_dec(x_5);
x_5407 = lean_ctor_get(x_5406, 1);
lean_inc(x_5407);
lean_dec(x_5406);
x_5408 = l_Lean_Elab_Term_getMainModule___rarg(x_5407);
x_5409 = lean_ctor_get(x_5408, 1);
lean_inc(x_5409);
if (lean_is_exclusive(x_5408)) {
 lean_ctor_release(x_5408, 0);
 lean_ctor_release(x_5408, 1);
 x_5410 = x_5408;
} else {
 lean_dec_ref(x_5408);
 x_5410 = lean_box(0);
}
x_5411 = l_Array_empty___closed__1;
x_5412 = lean_array_push(x_5411, x_5298);
x_5413 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5414 = lean_array_push(x_5412, x_5413);
x_5415 = l_Lean_mkTermIdFromIdent___closed__2;
x_5416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5416, 0, x_5415);
lean_ctor_set(x_5416, 1, x_5414);
x_5417 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5418 = lean_array_push(x_5417, x_5416);
x_5419 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5420, 0, x_5419);
lean_ctor_set(x_5420, 1, x_5418);
x_5421 = lean_array_push(x_5411, x_5420);
x_5422 = l_Lean_nullKind___closed__2;
x_5423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5423, 0, x_5422);
lean_ctor_set(x_5423, 1, x_5421);
x_5424 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5425 = lean_array_push(x_5424, x_5423);
x_5426 = lean_array_push(x_5425, x_5413);
x_5427 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5428 = lean_array_push(x_5426, x_5427);
x_5429 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5430 = lean_array_push(x_5428, x_5429);
lean_inc(x_14);
x_5431 = lean_array_push(x_5411, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5432 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5432 = lean_box(0);
}
if (lean_is_scalar(x_5432)) {
 x_5433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5433 = x_5432;
}
lean_ctor_set(x_5433, 0, x_5422);
lean_ctor_set(x_5433, 1, x_5431);
x_5434 = lean_array_push(x_5411, x_5433);
x_5435 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5436 = lean_array_push(x_5434, x_5435);
x_5437 = lean_array_push(x_5436, x_5405);
x_5438 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5439, 0, x_5438);
lean_ctor_set(x_5439, 1, x_5437);
x_5440 = lean_array_push(x_5411, x_5439);
x_5441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5441, 0, x_5422);
lean_ctor_set(x_5441, 1, x_5440);
x_5442 = lean_array_push(x_5430, x_5441);
x_5443 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5444, 0, x_5443);
lean_ctor_set(x_5444, 1, x_5442);
x_5445 = lean_box(x_5295);
x_5446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5446, 0, x_5444);
lean_ctor_set(x_5446, 1, x_5445);
lean_ctor_set(x_5306, 1, x_5446);
if (lean_is_scalar(x_5410)) {
 x_5447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5447 = x_5410;
}
lean_ctor_set(x_5447, 0, x_5306);
lean_ctor_set(x_5447, 1, x_5409);
return x_5447;
}
}
else
{
lean_object* x_5448; lean_object* x_5449; lean_object* x_5450; lean_object* x_5451; lean_object* x_5452; lean_object* x_5453; lean_object* x_5454; lean_object* x_5455; lean_object* x_5456; lean_object* x_5457; lean_object* x_5458; lean_object* x_5459; lean_object* x_5460; lean_object* x_5461; lean_object* x_5462; lean_object* x_5463; lean_object* x_5464; lean_object* x_5465; lean_object* x_5466; lean_object* x_5467; lean_object* x_5468; lean_object* x_5469; lean_object* x_5470; lean_object* x_5471; lean_object* x_5472; lean_object* x_5473; lean_object* x_5474; lean_object* x_5475; lean_object* x_5476; lean_object* x_5477; lean_object* x_5478; lean_object* x_5479; lean_object* x_5480; lean_object* x_5481; lean_object* x_5482; lean_object* x_5483; lean_object* x_5484; lean_object* x_5485; lean_object* x_5486; lean_object* x_5487; lean_object* x_5488; lean_object* x_5489; lean_object* x_5490; lean_object* x_5491; lean_object* x_5492; lean_object* x_5493; 
x_5448 = lean_ctor_get(x_5306, 0);
lean_inc(x_5448);
lean_dec(x_5306);
x_5449 = lean_ctor_get(x_5307, 0);
lean_inc(x_5449);
if (lean_is_exclusive(x_5307)) {
 lean_ctor_release(x_5307, 0);
 lean_ctor_release(x_5307, 1);
 x_5450 = x_5307;
} else {
 lean_dec_ref(x_5307);
 x_5450 = lean_box(0);
}
x_5451 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5308);
lean_dec(x_5);
x_5452 = lean_ctor_get(x_5451, 1);
lean_inc(x_5452);
lean_dec(x_5451);
x_5453 = l_Lean_Elab_Term_getMainModule___rarg(x_5452);
x_5454 = lean_ctor_get(x_5453, 1);
lean_inc(x_5454);
if (lean_is_exclusive(x_5453)) {
 lean_ctor_release(x_5453, 0);
 lean_ctor_release(x_5453, 1);
 x_5455 = x_5453;
} else {
 lean_dec_ref(x_5453);
 x_5455 = lean_box(0);
}
x_5456 = l_Array_empty___closed__1;
x_5457 = lean_array_push(x_5456, x_5298);
x_5458 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5459 = lean_array_push(x_5457, x_5458);
x_5460 = l_Lean_mkTermIdFromIdent___closed__2;
x_5461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5461, 0, x_5460);
lean_ctor_set(x_5461, 1, x_5459);
x_5462 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5463 = lean_array_push(x_5462, x_5461);
x_5464 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5465, 0, x_5464);
lean_ctor_set(x_5465, 1, x_5463);
x_5466 = lean_array_push(x_5456, x_5465);
x_5467 = l_Lean_nullKind___closed__2;
x_5468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5468, 0, x_5467);
lean_ctor_set(x_5468, 1, x_5466);
x_5469 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5470 = lean_array_push(x_5469, x_5468);
x_5471 = lean_array_push(x_5470, x_5458);
x_5472 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5473 = lean_array_push(x_5471, x_5472);
x_5474 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5475 = lean_array_push(x_5473, x_5474);
lean_inc(x_14);
x_5476 = lean_array_push(x_5456, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5477 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5477 = lean_box(0);
}
if (lean_is_scalar(x_5477)) {
 x_5478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5478 = x_5477;
}
lean_ctor_set(x_5478, 0, x_5467);
lean_ctor_set(x_5478, 1, x_5476);
x_5479 = lean_array_push(x_5456, x_5478);
x_5480 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5481 = lean_array_push(x_5479, x_5480);
x_5482 = lean_array_push(x_5481, x_5449);
x_5483 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5484, 0, x_5483);
lean_ctor_set(x_5484, 1, x_5482);
x_5485 = lean_array_push(x_5456, x_5484);
x_5486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5486, 0, x_5467);
lean_ctor_set(x_5486, 1, x_5485);
x_5487 = lean_array_push(x_5475, x_5486);
x_5488 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5489, 0, x_5488);
lean_ctor_set(x_5489, 1, x_5487);
x_5490 = lean_box(x_5295);
if (lean_is_scalar(x_5450)) {
 x_5491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5491 = x_5450;
}
lean_ctor_set(x_5491, 0, x_5489);
lean_ctor_set(x_5491, 1, x_5490);
x_5492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5492, 0, x_5448);
lean_ctor_set(x_5492, 1, x_5491);
if (lean_is_scalar(x_5455)) {
 x_5493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5493 = x_5455;
}
lean_ctor_set(x_5493, 0, x_5492);
lean_ctor_set(x_5493, 1, x_5454);
return x_5493;
}
}
else
{
uint8_t x_5494; 
lean_dec(x_5298);
lean_dec(x_14);
lean_dec(x_5);
x_5494 = !lean_is_exclusive(x_5305);
if (x_5494 == 0)
{
return x_5305;
}
else
{
lean_object* x_5495; lean_object* x_5496; lean_object* x_5497; 
x_5495 = lean_ctor_get(x_5305, 0);
x_5496 = lean_ctor_get(x_5305, 1);
lean_inc(x_5496);
lean_inc(x_5495);
lean_dec(x_5305);
x_5497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5497, 0, x_5495);
lean_ctor_set(x_5497, 1, x_5496);
return x_5497;
}
}
}
else
{
lean_object* x_5498; lean_object* x_5499; lean_object* x_5500; uint8_t x_5501; 
x_5498 = lean_ctor_get(x_5296, 0);
lean_inc(x_5498);
lean_dec(x_5296);
x_5499 = lean_ctor_get(x_5498, 0);
lean_inc(x_5499);
x_5500 = lean_ctor_get(x_5498, 1);
lean_inc(x_5500);
lean_dec(x_5498);
x_5501 = l_Lean_Syntax_isNone(x_5500);
lean_dec(x_5500);
if (x_5501 == 0)
{
lean_object* x_5502; lean_object* x_5503; uint8_t x_5504; 
lean_dec(x_5499);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_5502 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_5503 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_5502, x_5, x_6);
lean_dec(x_14);
x_5504 = !lean_is_exclusive(x_5503);
if (x_5504 == 0)
{
return x_5503;
}
else
{
lean_object* x_5505; lean_object* x_5506; lean_object* x_5507; 
x_5505 = lean_ctor_get(x_5503, 0);
x_5506 = lean_ctor_get(x_5503, 1);
lean_inc(x_5506);
lean_inc(x_5505);
lean_dec(x_5503);
x_5507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5507, 0, x_5505);
lean_ctor_set(x_5507, 1, x_5506);
return x_5507;
}
}
else
{
lean_object* x_5508; lean_object* x_5509; lean_object* x_5510; lean_object* x_5511; lean_object* x_5512; 
x_5508 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_5509 = lean_unsigned_to_nat(1u);
x_5510 = lean_nat_add(x_3, x_5509);
lean_dec(x_3);
x_5511 = l_Lean_Elab_Term_mkExplicitBinder(x_5499, x_5508);
x_5512 = lean_array_push(x_4, x_5511);
x_3 = x_5510;
x_4 = x_5512;
goto _start;
}
}
}
}
case 2:
{
uint8_t x_5514; lean_object* x_5515; 
x_5514 = 1;
lean_inc(x_14);
x_5515 = l_Lean_Syntax_isTermId_x3f(x_14, x_5514);
if (lean_obj_tag(x_5515) == 0)
{
lean_object* x_5516; lean_object* x_5517; lean_object* x_5518; lean_object* x_5519; lean_object* x_5520; lean_object* x_5521; lean_object* x_5522; lean_object* x_5523; lean_object* x_5524; 
x_5516 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_5517 = lean_ctor_get(x_5516, 0);
lean_inc(x_5517);
x_5518 = lean_ctor_get(x_5516, 1);
lean_inc(x_5518);
lean_dec(x_5516);
x_5519 = lean_unsigned_to_nat(1u);
x_5520 = lean_nat_add(x_3, x_5519);
lean_dec(x_3);
x_5521 = l_Lean_mkHole(x_14);
lean_inc(x_5517);
x_5522 = l_Lean_Elab_Term_mkExplicitBinder(x_5517, x_5521);
x_5523 = lean_array_push(x_4, x_5522);
lean_inc(x_5);
x_5524 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_5520, x_5523, x_5, x_5518);
if (lean_obj_tag(x_5524) == 0)
{
lean_object* x_5525; lean_object* x_5526; lean_object* x_5527; uint8_t x_5528; 
x_5525 = lean_ctor_get(x_5524, 0);
lean_inc(x_5525);
x_5526 = lean_ctor_get(x_5525, 1);
lean_inc(x_5526);
x_5527 = lean_ctor_get(x_5524, 1);
lean_inc(x_5527);
lean_dec(x_5524);
x_5528 = !lean_is_exclusive(x_5525);
if (x_5528 == 0)
{
lean_object* x_5529; uint8_t x_5530; 
x_5529 = lean_ctor_get(x_5525, 1);
lean_dec(x_5529);
x_5530 = !lean_is_exclusive(x_5526);
if (x_5530 == 0)
{
lean_object* x_5531; lean_object* x_5532; lean_object* x_5533; lean_object* x_5534; lean_object* x_5535; uint8_t x_5536; 
x_5531 = lean_ctor_get(x_5526, 0);
x_5532 = lean_ctor_get(x_5526, 1);
lean_dec(x_5532);
x_5533 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5527);
lean_dec(x_5);
x_5534 = lean_ctor_get(x_5533, 1);
lean_inc(x_5534);
lean_dec(x_5533);
x_5535 = l_Lean_Elab_Term_getMainModule___rarg(x_5534);
x_5536 = !lean_is_exclusive(x_5535);
if (x_5536 == 0)
{
lean_object* x_5537; lean_object* x_5538; lean_object* x_5539; lean_object* x_5540; lean_object* x_5541; lean_object* x_5542; lean_object* x_5543; lean_object* x_5544; lean_object* x_5545; lean_object* x_5546; lean_object* x_5547; lean_object* x_5548; lean_object* x_5549; lean_object* x_5550; lean_object* x_5551; lean_object* x_5552; lean_object* x_5553; lean_object* x_5554; lean_object* x_5555; lean_object* x_5556; lean_object* x_5557; lean_object* x_5558; uint8_t x_5559; 
x_5537 = lean_ctor_get(x_5535, 0);
lean_dec(x_5537);
x_5538 = l_Array_empty___closed__1;
x_5539 = lean_array_push(x_5538, x_5517);
x_5540 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5541 = lean_array_push(x_5539, x_5540);
x_5542 = l_Lean_mkTermIdFromIdent___closed__2;
x_5543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5543, 0, x_5542);
lean_ctor_set(x_5543, 1, x_5541);
x_5544 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5545 = lean_array_push(x_5544, x_5543);
x_5546 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5547, 0, x_5546);
lean_ctor_set(x_5547, 1, x_5545);
x_5548 = lean_array_push(x_5538, x_5547);
x_5549 = l_Lean_nullKind___closed__2;
x_5550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5550, 0, x_5549);
lean_ctor_set(x_5550, 1, x_5548);
x_5551 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5552 = lean_array_push(x_5551, x_5550);
x_5553 = lean_array_push(x_5552, x_5540);
x_5554 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5555 = lean_array_push(x_5553, x_5554);
x_5556 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5557 = lean_array_push(x_5555, x_5556);
lean_inc(x_14);
x_5558 = lean_array_push(x_5538, x_14);
x_5559 = !lean_is_exclusive(x_14);
if (x_5559 == 0)
{
lean_object* x_5560; lean_object* x_5561; lean_object* x_5562; lean_object* x_5563; lean_object* x_5564; lean_object* x_5565; lean_object* x_5566; lean_object* x_5567; lean_object* x_5568; lean_object* x_5569; lean_object* x_5570; lean_object* x_5571; lean_object* x_5572; lean_object* x_5573; 
x_5560 = lean_ctor_get(x_14, 1);
lean_dec(x_5560);
x_5561 = lean_ctor_get(x_14, 0);
lean_dec(x_5561);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_5558);
lean_ctor_set(x_14, 0, x_5549);
x_5562 = lean_array_push(x_5538, x_14);
x_5563 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5564 = lean_array_push(x_5562, x_5563);
x_5565 = lean_array_push(x_5564, x_5531);
x_5566 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5567, 0, x_5566);
lean_ctor_set(x_5567, 1, x_5565);
x_5568 = lean_array_push(x_5538, x_5567);
x_5569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5569, 0, x_5549);
lean_ctor_set(x_5569, 1, x_5568);
x_5570 = lean_array_push(x_5557, x_5569);
x_5571 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5572, 0, x_5571);
lean_ctor_set(x_5572, 1, x_5570);
x_5573 = lean_box(x_5514);
lean_ctor_set(x_5526, 1, x_5573);
lean_ctor_set(x_5526, 0, x_5572);
lean_ctor_set(x_5535, 0, x_5525);
return x_5535;
}
else
{
lean_object* x_5574; lean_object* x_5575; lean_object* x_5576; lean_object* x_5577; lean_object* x_5578; lean_object* x_5579; lean_object* x_5580; lean_object* x_5581; lean_object* x_5582; lean_object* x_5583; lean_object* x_5584; lean_object* x_5585; lean_object* x_5586; 
lean_dec(x_14);
x_5574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5574, 0, x_5549);
lean_ctor_set(x_5574, 1, x_5558);
x_5575 = lean_array_push(x_5538, x_5574);
x_5576 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5577 = lean_array_push(x_5575, x_5576);
x_5578 = lean_array_push(x_5577, x_5531);
x_5579 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5580, 0, x_5579);
lean_ctor_set(x_5580, 1, x_5578);
x_5581 = lean_array_push(x_5538, x_5580);
x_5582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5582, 0, x_5549);
lean_ctor_set(x_5582, 1, x_5581);
x_5583 = lean_array_push(x_5557, x_5582);
x_5584 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5585, 0, x_5584);
lean_ctor_set(x_5585, 1, x_5583);
x_5586 = lean_box(x_5514);
lean_ctor_set(x_5526, 1, x_5586);
lean_ctor_set(x_5526, 0, x_5585);
lean_ctor_set(x_5535, 0, x_5525);
return x_5535;
}
}
else
{
lean_object* x_5587; lean_object* x_5588; lean_object* x_5589; lean_object* x_5590; lean_object* x_5591; lean_object* x_5592; lean_object* x_5593; lean_object* x_5594; lean_object* x_5595; lean_object* x_5596; lean_object* x_5597; lean_object* x_5598; lean_object* x_5599; lean_object* x_5600; lean_object* x_5601; lean_object* x_5602; lean_object* x_5603; lean_object* x_5604; lean_object* x_5605; lean_object* x_5606; lean_object* x_5607; lean_object* x_5608; lean_object* x_5609; lean_object* x_5610; lean_object* x_5611; lean_object* x_5612; lean_object* x_5613; lean_object* x_5614; lean_object* x_5615; lean_object* x_5616; lean_object* x_5617; lean_object* x_5618; lean_object* x_5619; lean_object* x_5620; lean_object* x_5621; lean_object* x_5622; lean_object* x_5623; 
x_5587 = lean_ctor_get(x_5535, 1);
lean_inc(x_5587);
lean_dec(x_5535);
x_5588 = l_Array_empty___closed__1;
x_5589 = lean_array_push(x_5588, x_5517);
x_5590 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5591 = lean_array_push(x_5589, x_5590);
x_5592 = l_Lean_mkTermIdFromIdent___closed__2;
x_5593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5593, 0, x_5592);
lean_ctor_set(x_5593, 1, x_5591);
x_5594 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5595 = lean_array_push(x_5594, x_5593);
x_5596 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5597, 0, x_5596);
lean_ctor_set(x_5597, 1, x_5595);
x_5598 = lean_array_push(x_5588, x_5597);
x_5599 = l_Lean_nullKind___closed__2;
x_5600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5600, 0, x_5599);
lean_ctor_set(x_5600, 1, x_5598);
x_5601 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5602 = lean_array_push(x_5601, x_5600);
x_5603 = lean_array_push(x_5602, x_5590);
x_5604 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5605 = lean_array_push(x_5603, x_5604);
x_5606 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5607 = lean_array_push(x_5605, x_5606);
lean_inc(x_14);
x_5608 = lean_array_push(x_5588, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5609 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5609 = lean_box(0);
}
if (lean_is_scalar(x_5609)) {
 x_5610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5610 = x_5609;
 lean_ctor_set_tag(x_5610, 1);
}
lean_ctor_set(x_5610, 0, x_5599);
lean_ctor_set(x_5610, 1, x_5608);
x_5611 = lean_array_push(x_5588, x_5610);
x_5612 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5613 = lean_array_push(x_5611, x_5612);
x_5614 = lean_array_push(x_5613, x_5531);
x_5615 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5616, 0, x_5615);
lean_ctor_set(x_5616, 1, x_5614);
x_5617 = lean_array_push(x_5588, x_5616);
x_5618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5618, 0, x_5599);
lean_ctor_set(x_5618, 1, x_5617);
x_5619 = lean_array_push(x_5607, x_5618);
x_5620 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5621, 0, x_5620);
lean_ctor_set(x_5621, 1, x_5619);
x_5622 = lean_box(x_5514);
lean_ctor_set(x_5526, 1, x_5622);
lean_ctor_set(x_5526, 0, x_5621);
x_5623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5623, 0, x_5525);
lean_ctor_set(x_5623, 1, x_5587);
return x_5623;
}
}
else
{
lean_object* x_5624; lean_object* x_5625; lean_object* x_5626; lean_object* x_5627; lean_object* x_5628; lean_object* x_5629; lean_object* x_5630; lean_object* x_5631; lean_object* x_5632; lean_object* x_5633; lean_object* x_5634; lean_object* x_5635; lean_object* x_5636; lean_object* x_5637; lean_object* x_5638; lean_object* x_5639; lean_object* x_5640; lean_object* x_5641; lean_object* x_5642; lean_object* x_5643; lean_object* x_5644; lean_object* x_5645; lean_object* x_5646; lean_object* x_5647; lean_object* x_5648; lean_object* x_5649; lean_object* x_5650; lean_object* x_5651; lean_object* x_5652; lean_object* x_5653; lean_object* x_5654; lean_object* x_5655; lean_object* x_5656; lean_object* x_5657; lean_object* x_5658; lean_object* x_5659; lean_object* x_5660; lean_object* x_5661; lean_object* x_5662; lean_object* x_5663; lean_object* x_5664; lean_object* x_5665; lean_object* x_5666; 
x_5624 = lean_ctor_get(x_5526, 0);
lean_inc(x_5624);
lean_dec(x_5526);
x_5625 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5527);
lean_dec(x_5);
x_5626 = lean_ctor_get(x_5625, 1);
lean_inc(x_5626);
lean_dec(x_5625);
x_5627 = l_Lean_Elab_Term_getMainModule___rarg(x_5626);
x_5628 = lean_ctor_get(x_5627, 1);
lean_inc(x_5628);
if (lean_is_exclusive(x_5627)) {
 lean_ctor_release(x_5627, 0);
 lean_ctor_release(x_5627, 1);
 x_5629 = x_5627;
} else {
 lean_dec_ref(x_5627);
 x_5629 = lean_box(0);
}
x_5630 = l_Array_empty___closed__1;
x_5631 = lean_array_push(x_5630, x_5517);
x_5632 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5633 = lean_array_push(x_5631, x_5632);
x_5634 = l_Lean_mkTermIdFromIdent___closed__2;
x_5635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5635, 0, x_5634);
lean_ctor_set(x_5635, 1, x_5633);
x_5636 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5637 = lean_array_push(x_5636, x_5635);
x_5638 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5639, 0, x_5638);
lean_ctor_set(x_5639, 1, x_5637);
x_5640 = lean_array_push(x_5630, x_5639);
x_5641 = l_Lean_nullKind___closed__2;
x_5642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5642, 0, x_5641);
lean_ctor_set(x_5642, 1, x_5640);
x_5643 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5644 = lean_array_push(x_5643, x_5642);
x_5645 = lean_array_push(x_5644, x_5632);
x_5646 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5647 = lean_array_push(x_5645, x_5646);
x_5648 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5649 = lean_array_push(x_5647, x_5648);
lean_inc(x_14);
x_5650 = lean_array_push(x_5630, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5651 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5651 = lean_box(0);
}
if (lean_is_scalar(x_5651)) {
 x_5652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5652 = x_5651;
 lean_ctor_set_tag(x_5652, 1);
}
lean_ctor_set(x_5652, 0, x_5641);
lean_ctor_set(x_5652, 1, x_5650);
x_5653 = lean_array_push(x_5630, x_5652);
x_5654 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5655 = lean_array_push(x_5653, x_5654);
x_5656 = lean_array_push(x_5655, x_5624);
x_5657 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5658, 0, x_5657);
lean_ctor_set(x_5658, 1, x_5656);
x_5659 = lean_array_push(x_5630, x_5658);
x_5660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5660, 0, x_5641);
lean_ctor_set(x_5660, 1, x_5659);
x_5661 = lean_array_push(x_5649, x_5660);
x_5662 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5663, 0, x_5662);
lean_ctor_set(x_5663, 1, x_5661);
x_5664 = lean_box(x_5514);
x_5665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5665, 0, x_5663);
lean_ctor_set(x_5665, 1, x_5664);
lean_ctor_set(x_5525, 1, x_5665);
if (lean_is_scalar(x_5629)) {
 x_5666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5666 = x_5629;
}
lean_ctor_set(x_5666, 0, x_5525);
lean_ctor_set(x_5666, 1, x_5628);
return x_5666;
}
}
else
{
lean_object* x_5667; lean_object* x_5668; lean_object* x_5669; lean_object* x_5670; lean_object* x_5671; lean_object* x_5672; lean_object* x_5673; lean_object* x_5674; lean_object* x_5675; lean_object* x_5676; lean_object* x_5677; lean_object* x_5678; lean_object* x_5679; lean_object* x_5680; lean_object* x_5681; lean_object* x_5682; lean_object* x_5683; lean_object* x_5684; lean_object* x_5685; lean_object* x_5686; lean_object* x_5687; lean_object* x_5688; lean_object* x_5689; lean_object* x_5690; lean_object* x_5691; lean_object* x_5692; lean_object* x_5693; lean_object* x_5694; lean_object* x_5695; lean_object* x_5696; lean_object* x_5697; lean_object* x_5698; lean_object* x_5699; lean_object* x_5700; lean_object* x_5701; lean_object* x_5702; lean_object* x_5703; lean_object* x_5704; lean_object* x_5705; lean_object* x_5706; lean_object* x_5707; lean_object* x_5708; lean_object* x_5709; lean_object* x_5710; lean_object* x_5711; lean_object* x_5712; 
x_5667 = lean_ctor_get(x_5525, 0);
lean_inc(x_5667);
lean_dec(x_5525);
x_5668 = lean_ctor_get(x_5526, 0);
lean_inc(x_5668);
if (lean_is_exclusive(x_5526)) {
 lean_ctor_release(x_5526, 0);
 lean_ctor_release(x_5526, 1);
 x_5669 = x_5526;
} else {
 lean_dec_ref(x_5526);
 x_5669 = lean_box(0);
}
x_5670 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5527);
lean_dec(x_5);
x_5671 = lean_ctor_get(x_5670, 1);
lean_inc(x_5671);
lean_dec(x_5670);
x_5672 = l_Lean_Elab_Term_getMainModule___rarg(x_5671);
x_5673 = lean_ctor_get(x_5672, 1);
lean_inc(x_5673);
if (lean_is_exclusive(x_5672)) {
 lean_ctor_release(x_5672, 0);
 lean_ctor_release(x_5672, 1);
 x_5674 = x_5672;
} else {
 lean_dec_ref(x_5672);
 x_5674 = lean_box(0);
}
x_5675 = l_Array_empty___closed__1;
x_5676 = lean_array_push(x_5675, x_5517);
x_5677 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5678 = lean_array_push(x_5676, x_5677);
x_5679 = l_Lean_mkTermIdFromIdent___closed__2;
x_5680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5680, 0, x_5679);
lean_ctor_set(x_5680, 1, x_5678);
x_5681 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5682 = lean_array_push(x_5681, x_5680);
x_5683 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5684, 0, x_5683);
lean_ctor_set(x_5684, 1, x_5682);
x_5685 = lean_array_push(x_5675, x_5684);
x_5686 = l_Lean_nullKind___closed__2;
x_5687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5687, 0, x_5686);
lean_ctor_set(x_5687, 1, x_5685);
x_5688 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5689 = lean_array_push(x_5688, x_5687);
x_5690 = lean_array_push(x_5689, x_5677);
x_5691 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5692 = lean_array_push(x_5690, x_5691);
x_5693 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5694 = lean_array_push(x_5692, x_5693);
lean_inc(x_14);
x_5695 = lean_array_push(x_5675, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_5696 = x_14;
} else {
 lean_dec_ref(x_14);
 x_5696 = lean_box(0);
}
if (lean_is_scalar(x_5696)) {
 x_5697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_5697 = x_5696;
 lean_ctor_set_tag(x_5697, 1);
}
lean_ctor_set(x_5697, 0, x_5686);
lean_ctor_set(x_5697, 1, x_5695);
x_5698 = lean_array_push(x_5675, x_5697);
x_5699 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5700 = lean_array_push(x_5698, x_5699);
x_5701 = lean_array_push(x_5700, x_5668);
x_5702 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5703, 0, x_5702);
lean_ctor_set(x_5703, 1, x_5701);
x_5704 = lean_array_push(x_5675, x_5703);
x_5705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5705, 0, x_5686);
lean_ctor_set(x_5705, 1, x_5704);
x_5706 = lean_array_push(x_5694, x_5705);
x_5707 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5708, 0, x_5707);
lean_ctor_set(x_5708, 1, x_5706);
x_5709 = lean_box(x_5514);
if (lean_is_scalar(x_5669)) {
 x_5710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5710 = x_5669;
}
lean_ctor_set(x_5710, 0, x_5708);
lean_ctor_set(x_5710, 1, x_5709);
x_5711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5711, 0, x_5667);
lean_ctor_set(x_5711, 1, x_5710);
if (lean_is_scalar(x_5674)) {
 x_5712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5712 = x_5674;
}
lean_ctor_set(x_5712, 0, x_5711);
lean_ctor_set(x_5712, 1, x_5673);
return x_5712;
}
}
else
{
uint8_t x_5713; 
lean_dec(x_5517);
lean_dec(x_14);
lean_dec(x_5);
x_5713 = !lean_is_exclusive(x_5524);
if (x_5713 == 0)
{
return x_5524;
}
else
{
lean_object* x_5714; lean_object* x_5715; lean_object* x_5716; 
x_5714 = lean_ctor_get(x_5524, 0);
x_5715 = lean_ctor_get(x_5524, 1);
lean_inc(x_5715);
lean_inc(x_5714);
lean_dec(x_5524);
x_5716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5716, 0, x_5714);
lean_ctor_set(x_5716, 1, x_5715);
return x_5716;
}
}
}
else
{
lean_object* x_5717; lean_object* x_5718; lean_object* x_5719; uint8_t x_5720; 
x_5717 = lean_ctor_get(x_5515, 0);
lean_inc(x_5717);
lean_dec(x_5515);
x_5718 = lean_ctor_get(x_5717, 0);
lean_inc(x_5718);
x_5719 = lean_ctor_get(x_5717, 1);
lean_inc(x_5719);
lean_dec(x_5717);
x_5720 = l_Lean_Syntax_isNone(x_5719);
lean_dec(x_5719);
if (x_5720 == 0)
{
lean_object* x_5721; lean_object* x_5722; uint8_t x_5723; 
lean_dec(x_5718);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_5721 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_5722 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_5721, x_5, x_6);
lean_dec(x_14);
x_5723 = !lean_is_exclusive(x_5722);
if (x_5723 == 0)
{
return x_5722;
}
else
{
lean_object* x_5724; lean_object* x_5725; lean_object* x_5726; 
x_5724 = lean_ctor_get(x_5722, 0);
x_5725 = lean_ctor_get(x_5722, 1);
lean_inc(x_5725);
lean_inc(x_5724);
lean_dec(x_5722);
x_5726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5726, 0, x_5724);
lean_ctor_set(x_5726, 1, x_5725);
return x_5726;
}
}
else
{
lean_object* x_5727; lean_object* x_5728; lean_object* x_5729; lean_object* x_5730; lean_object* x_5731; 
x_5727 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_5728 = lean_unsigned_to_nat(1u);
x_5729 = lean_nat_add(x_3, x_5728);
lean_dec(x_3);
x_5730 = l_Lean_Elab_Term_mkExplicitBinder(x_5718, x_5727);
x_5731 = lean_array_push(x_4, x_5730);
x_3 = x_5729;
x_4 = x_5731;
goto _start;
}
}
}
default: 
{
uint8_t x_5733; lean_object* x_5734; 
x_5733 = 1;
lean_inc(x_14);
x_5734 = l_Lean_Syntax_isTermId_x3f(x_14, x_5733);
if (lean_obj_tag(x_5734) == 0)
{
lean_object* x_5735; lean_object* x_5736; lean_object* x_5737; lean_object* x_5738; lean_object* x_5739; lean_object* x_5740; lean_object* x_5741; lean_object* x_5742; lean_object* x_5743; 
x_5735 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_14, x_5, x_6);
x_5736 = lean_ctor_get(x_5735, 0);
lean_inc(x_5736);
x_5737 = lean_ctor_get(x_5735, 1);
lean_inc(x_5737);
lean_dec(x_5735);
x_5738 = lean_unsigned_to_nat(1u);
x_5739 = lean_nat_add(x_3, x_5738);
lean_dec(x_3);
x_5740 = l_Lean_mkHole(x_14);
lean_inc(x_5736);
x_5741 = l_Lean_Elab_Term_mkExplicitBinder(x_5736, x_5740);
x_5742 = lean_array_push(x_4, x_5741);
lean_inc(x_5);
x_5743 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_5739, x_5742, x_5, x_5737);
if (lean_obj_tag(x_5743) == 0)
{
lean_object* x_5744; lean_object* x_5745; lean_object* x_5746; uint8_t x_5747; 
x_5744 = lean_ctor_get(x_5743, 0);
lean_inc(x_5744);
x_5745 = lean_ctor_get(x_5744, 1);
lean_inc(x_5745);
x_5746 = lean_ctor_get(x_5743, 1);
lean_inc(x_5746);
lean_dec(x_5743);
x_5747 = !lean_is_exclusive(x_5744);
if (x_5747 == 0)
{
lean_object* x_5748; uint8_t x_5749; 
x_5748 = lean_ctor_get(x_5744, 1);
lean_dec(x_5748);
x_5749 = !lean_is_exclusive(x_5745);
if (x_5749 == 0)
{
lean_object* x_5750; lean_object* x_5751; lean_object* x_5752; lean_object* x_5753; lean_object* x_5754; uint8_t x_5755; 
x_5750 = lean_ctor_get(x_5745, 0);
x_5751 = lean_ctor_get(x_5745, 1);
lean_dec(x_5751);
x_5752 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5746);
lean_dec(x_5);
x_5753 = lean_ctor_get(x_5752, 1);
lean_inc(x_5753);
lean_dec(x_5752);
x_5754 = l_Lean_Elab_Term_getMainModule___rarg(x_5753);
x_5755 = !lean_is_exclusive(x_5754);
if (x_5755 == 0)
{
lean_object* x_5756; lean_object* x_5757; lean_object* x_5758; lean_object* x_5759; lean_object* x_5760; lean_object* x_5761; lean_object* x_5762; lean_object* x_5763; lean_object* x_5764; lean_object* x_5765; lean_object* x_5766; lean_object* x_5767; lean_object* x_5768; lean_object* x_5769; lean_object* x_5770; lean_object* x_5771; lean_object* x_5772; lean_object* x_5773; lean_object* x_5774; lean_object* x_5775; lean_object* x_5776; lean_object* x_5777; lean_object* x_5778; lean_object* x_5779; lean_object* x_5780; lean_object* x_5781; lean_object* x_5782; lean_object* x_5783; lean_object* x_5784; lean_object* x_5785; lean_object* x_5786; lean_object* x_5787; lean_object* x_5788; lean_object* x_5789; lean_object* x_5790; 
x_5756 = lean_ctor_get(x_5754, 0);
lean_dec(x_5756);
x_5757 = l_Array_empty___closed__1;
x_5758 = lean_array_push(x_5757, x_5736);
x_5759 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5760 = lean_array_push(x_5758, x_5759);
x_5761 = l_Lean_mkTermIdFromIdent___closed__2;
x_5762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5762, 0, x_5761);
lean_ctor_set(x_5762, 1, x_5760);
x_5763 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5764 = lean_array_push(x_5763, x_5762);
x_5765 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5766, 0, x_5765);
lean_ctor_set(x_5766, 1, x_5764);
x_5767 = lean_array_push(x_5757, x_5766);
x_5768 = l_Lean_nullKind___closed__2;
x_5769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5769, 0, x_5768);
lean_ctor_set(x_5769, 1, x_5767);
x_5770 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5771 = lean_array_push(x_5770, x_5769);
x_5772 = lean_array_push(x_5771, x_5759);
x_5773 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5774 = lean_array_push(x_5772, x_5773);
x_5775 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5776 = lean_array_push(x_5774, x_5775);
x_5777 = lean_array_push(x_5757, x_14);
x_5778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5778, 0, x_5768);
lean_ctor_set(x_5778, 1, x_5777);
x_5779 = lean_array_push(x_5757, x_5778);
x_5780 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5781 = lean_array_push(x_5779, x_5780);
x_5782 = lean_array_push(x_5781, x_5750);
x_5783 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5784, 0, x_5783);
lean_ctor_set(x_5784, 1, x_5782);
x_5785 = lean_array_push(x_5757, x_5784);
x_5786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5786, 0, x_5768);
lean_ctor_set(x_5786, 1, x_5785);
x_5787 = lean_array_push(x_5776, x_5786);
x_5788 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5789, 0, x_5788);
lean_ctor_set(x_5789, 1, x_5787);
x_5790 = lean_box(x_5733);
lean_ctor_set(x_5745, 1, x_5790);
lean_ctor_set(x_5745, 0, x_5789);
lean_ctor_set(x_5754, 0, x_5744);
return x_5754;
}
else
{
lean_object* x_5791; lean_object* x_5792; lean_object* x_5793; lean_object* x_5794; lean_object* x_5795; lean_object* x_5796; lean_object* x_5797; lean_object* x_5798; lean_object* x_5799; lean_object* x_5800; lean_object* x_5801; lean_object* x_5802; lean_object* x_5803; lean_object* x_5804; lean_object* x_5805; lean_object* x_5806; lean_object* x_5807; lean_object* x_5808; lean_object* x_5809; lean_object* x_5810; lean_object* x_5811; lean_object* x_5812; lean_object* x_5813; lean_object* x_5814; lean_object* x_5815; lean_object* x_5816; lean_object* x_5817; lean_object* x_5818; lean_object* x_5819; lean_object* x_5820; lean_object* x_5821; lean_object* x_5822; lean_object* x_5823; lean_object* x_5824; lean_object* x_5825; lean_object* x_5826; 
x_5791 = lean_ctor_get(x_5754, 1);
lean_inc(x_5791);
lean_dec(x_5754);
x_5792 = l_Array_empty___closed__1;
x_5793 = lean_array_push(x_5792, x_5736);
x_5794 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5795 = lean_array_push(x_5793, x_5794);
x_5796 = l_Lean_mkTermIdFromIdent___closed__2;
x_5797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5797, 0, x_5796);
lean_ctor_set(x_5797, 1, x_5795);
x_5798 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5799 = lean_array_push(x_5798, x_5797);
x_5800 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5801, 0, x_5800);
lean_ctor_set(x_5801, 1, x_5799);
x_5802 = lean_array_push(x_5792, x_5801);
x_5803 = l_Lean_nullKind___closed__2;
x_5804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5804, 0, x_5803);
lean_ctor_set(x_5804, 1, x_5802);
x_5805 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5806 = lean_array_push(x_5805, x_5804);
x_5807 = lean_array_push(x_5806, x_5794);
x_5808 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5809 = lean_array_push(x_5807, x_5808);
x_5810 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5811 = lean_array_push(x_5809, x_5810);
x_5812 = lean_array_push(x_5792, x_14);
x_5813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5813, 0, x_5803);
lean_ctor_set(x_5813, 1, x_5812);
x_5814 = lean_array_push(x_5792, x_5813);
x_5815 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5816 = lean_array_push(x_5814, x_5815);
x_5817 = lean_array_push(x_5816, x_5750);
x_5818 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5819, 0, x_5818);
lean_ctor_set(x_5819, 1, x_5817);
x_5820 = lean_array_push(x_5792, x_5819);
x_5821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5821, 0, x_5803);
lean_ctor_set(x_5821, 1, x_5820);
x_5822 = lean_array_push(x_5811, x_5821);
x_5823 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5824, 0, x_5823);
lean_ctor_set(x_5824, 1, x_5822);
x_5825 = lean_box(x_5733);
lean_ctor_set(x_5745, 1, x_5825);
lean_ctor_set(x_5745, 0, x_5824);
x_5826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5826, 0, x_5744);
lean_ctor_set(x_5826, 1, x_5791);
return x_5826;
}
}
else
{
lean_object* x_5827; lean_object* x_5828; lean_object* x_5829; lean_object* x_5830; lean_object* x_5831; lean_object* x_5832; lean_object* x_5833; lean_object* x_5834; lean_object* x_5835; lean_object* x_5836; lean_object* x_5837; lean_object* x_5838; lean_object* x_5839; lean_object* x_5840; lean_object* x_5841; lean_object* x_5842; lean_object* x_5843; lean_object* x_5844; lean_object* x_5845; lean_object* x_5846; lean_object* x_5847; lean_object* x_5848; lean_object* x_5849; lean_object* x_5850; lean_object* x_5851; lean_object* x_5852; lean_object* x_5853; lean_object* x_5854; lean_object* x_5855; lean_object* x_5856; lean_object* x_5857; lean_object* x_5858; lean_object* x_5859; lean_object* x_5860; lean_object* x_5861; lean_object* x_5862; lean_object* x_5863; lean_object* x_5864; lean_object* x_5865; lean_object* x_5866; lean_object* x_5867; lean_object* x_5868; 
x_5827 = lean_ctor_get(x_5745, 0);
lean_inc(x_5827);
lean_dec(x_5745);
x_5828 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5746);
lean_dec(x_5);
x_5829 = lean_ctor_get(x_5828, 1);
lean_inc(x_5829);
lean_dec(x_5828);
x_5830 = l_Lean_Elab_Term_getMainModule___rarg(x_5829);
x_5831 = lean_ctor_get(x_5830, 1);
lean_inc(x_5831);
if (lean_is_exclusive(x_5830)) {
 lean_ctor_release(x_5830, 0);
 lean_ctor_release(x_5830, 1);
 x_5832 = x_5830;
} else {
 lean_dec_ref(x_5830);
 x_5832 = lean_box(0);
}
x_5833 = l_Array_empty___closed__1;
x_5834 = lean_array_push(x_5833, x_5736);
x_5835 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5836 = lean_array_push(x_5834, x_5835);
x_5837 = l_Lean_mkTermIdFromIdent___closed__2;
x_5838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5838, 0, x_5837);
lean_ctor_set(x_5838, 1, x_5836);
x_5839 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5840 = lean_array_push(x_5839, x_5838);
x_5841 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5842, 0, x_5841);
lean_ctor_set(x_5842, 1, x_5840);
x_5843 = lean_array_push(x_5833, x_5842);
x_5844 = l_Lean_nullKind___closed__2;
x_5845 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5845, 0, x_5844);
lean_ctor_set(x_5845, 1, x_5843);
x_5846 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5847 = lean_array_push(x_5846, x_5845);
x_5848 = lean_array_push(x_5847, x_5835);
x_5849 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5850 = lean_array_push(x_5848, x_5849);
x_5851 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5852 = lean_array_push(x_5850, x_5851);
x_5853 = lean_array_push(x_5833, x_14);
x_5854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5854, 0, x_5844);
lean_ctor_set(x_5854, 1, x_5853);
x_5855 = lean_array_push(x_5833, x_5854);
x_5856 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5857 = lean_array_push(x_5855, x_5856);
x_5858 = lean_array_push(x_5857, x_5827);
x_5859 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5860, 0, x_5859);
lean_ctor_set(x_5860, 1, x_5858);
x_5861 = lean_array_push(x_5833, x_5860);
x_5862 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5862, 0, x_5844);
lean_ctor_set(x_5862, 1, x_5861);
x_5863 = lean_array_push(x_5852, x_5862);
x_5864 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5865, 0, x_5864);
lean_ctor_set(x_5865, 1, x_5863);
x_5866 = lean_box(x_5733);
x_5867 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5867, 0, x_5865);
lean_ctor_set(x_5867, 1, x_5866);
lean_ctor_set(x_5744, 1, x_5867);
if (lean_is_scalar(x_5832)) {
 x_5868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5868 = x_5832;
}
lean_ctor_set(x_5868, 0, x_5744);
lean_ctor_set(x_5868, 1, x_5831);
return x_5868;
}
}
else
{
lean_object* x_5869; lean_object* x_5870; lean_object* x_5871; lean_object* x_5872; lean_object* x_5873; lean_object* x_5874; lean_object* x_5875; lean_object* x_5876; lean_object* x_5877; lean_object* x_5878; lean_object* x_5879; lean_object* x_5880; lean_object* x_5881; lean_object* x_5882; lean_object* x_5883; lean_object* x_5884; lean_object* x_5885; lean_object* x_5886; lean_object* x_5887; lean_object* x_5888; lean_object* x_5889; lean_object* x_5890; lean_object* x_5891; lean_object* x_5892; lean_object* x_5893; lean_object* x_5894; lean_object* x_5895; lean_object* x_5896; lean_object* x_5897; lean_object* x_5898; lean_object* x_5899; lean_object* x_5900; lean_object* x_5901; lean_object* x_5902; lean_object* x_5903; lean_object* x_5904; lean_object* x_5905; lean_object* x_5906; lean_object* x_5907; lean_object* x_5908; lean_object* x_5909; lean_object* x_5910; lean_object* x_5911; lean_object* x_5912; lean_object* x_5913; 
x_5869 = lean_ctor_get(x_5744, 0);
lean_inc(x_5869);
lean_dec(x_5744);
x_5870 = lean_ctor_get(x_5745, 0);
lean_inc(x_5870);
if (lean_is_exclusive(x_5745)) {
 lean_ctor_release(x_5745, 0);
 lean_ctor_release(x_5745, 1);
 x_5871 = x_5745;
} else {
 lean_dec_ref(x_5745);
 x_5871 = lean_box(0);
}
x_5872 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_5746);
lean_dec(x_5);
x_5873 = lean_ctor_get(x_5872, 1);
lean_inc(x_5873);
lean_dec(x_5872);
x_5874 = l_Lean_Elab_Term_getMainModule___rarg(x_5873);
x_5875 = lean_ctor_get(x_5874, 1);
lean_inc(x_5875);
if (lean_is_exclusive(x_5874)) {
 lean_ctor_release(x_5874, 0);
 lean_ctor_release(x_5874, 1);
 x_5876 = x_5874;
} else {
 lean_dec_ref(x_5874);
 x_5876 = lean_box(0);
}
x_5877 = l_Array_empty___closed__1;
x_5878 = lean_array_push(x_5877, x_5736);
x_5879 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_5880 = lean_array_push(x_5878, x_5879);
x_5881 = l_Lean_mkTermIdFromIdent___closed__2;
x_5882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5882, 0, x_5881);
lean_ctor_set(x_5882, 1, x_5880);
x_5883 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_5884 = lean_array_push(x_5883, x_5882);
x_5885 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_5886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5886, 0, x_5885);
lean_ctor_set(x_5886, 1, x_5884);
x_5887 = lean_array_push(x_5877, x_5886);
x_5888 = l_Lean_nullKind___closed__2;
x_5889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5889, 0, x_5888);
lean_ctor_set(x_5889, 1, x_5887);
x_5890 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_5891 = lean_array_push(x_5890, x_5889);
x_5892 = lean_array_push(x_5891, x_5879);
x_5893 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_5894 = lean_array_push(x_5892, x_5893);
x_5895 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_5896 = lean_array_push(x_5894, x_5895);
x_5897 = lean_array_push(x_5877, x_14);
x_5898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5898, 0, x_5888);
lean_ctor_set(x_5898, 1, x_5897);
x_5899 = lean_array_push(x_5877, x_5898);
x_5900 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_5901 = lean_array_push(x_5899, x_5900);
x_5902 = lean_array_push(x_5901, x_5870);
x_5903 = l_Lean_Parser_Term_matchAlt___closed__2;
x_5904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5904, 0, x_5903);
lean_ctor_set(x_5904, 1, x_5902);
x_5905 = lean_array_push(x_5877, x_5904);
x_5906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5906, 0, x_5888);
lean_ctor_set(x_5906, 1, x_5905);
x_5907 = lean_array_push(x_5896, x_5906);
x_5908 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_5909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5909, 0, x_5908);
lean_ctor_set(x_5909, 1, x_5907);
x_5910 = lean_box(x_5733);
if (lean_is_scalar(x_5871)) {
 x_5911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5911 = x_5871;
}
lean_ctor_set(x_5911, 0, x_5909);
lean_ctor_set(x_5911, 1, x_5910);
x_5912 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5912, 0, x_5869);
lean_ctor_set(x_5912, 1, x_5911);
if (lean_is_scalar(x_5876)) {
 x_5913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_5913 = x_5876;
}
lean_ctor_set(x_5913, 0, x_5912);
lean_ctor_set(x_5913, 1, x_5875);
return x_5913;
}
}
else
{
uint8_t x_5914; 
lean_dec(x_5736);
lean_dec(x_14);
lean_dec(x_5);
x_5914 = !lean_is_exclusive(x_5743);
if (x_5914 == 0)
{
return x_5743;
}
else
{
lean_object* x_5915; lean_object* x_5916; lean_object* x_5917; 
x_5915 = lean_ctor_get(x_5743, 0);
x_5916 = lean_ctor_get(x_5743, 1);
lean_inc(x_5916);
lean_inc(x_5915);
lean_dec(x_5743);
x_5917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5917, 0, x_5915);
lean_ctor_set(x_5917, 1, x_5916);
return x_5917;
}
}
}
else
{
lean_object* x_5918; lean_object* x_5919; lean_object* x_5920; uint8_t x_5921; 
x_5918 = lean_ctor_get(x_5734, 0);
lean_inc(x_5918);
lean_dec(x_5734);
x_5919 = lean_ctor_get(x_5918, 0);
lean_inc(x_5919);
x_5920 = lean_ctor_get(x_5918, 1);
lean_inc(x_5920);
lean_dec(x_5918);
x_5921 = l_Lean_Syntax_isNone(x_5920);
lean_dec(x_5920);
if (x_5921 == 0)
{
lean_object* x_5922; lean_object* x_5923; uint8_t x_5924; 
lean_dec(x_5919);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_5922 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
x_5923 = l_Lean_Elab_Term_throwErrorAt___rarg(x_14, x_5922, x_5, x_6);
lean_dec(x_14);
x_5924 = !lean_is_exclusive(x_5923);
if (x_5924 == 0)
{
return x_5923;
}
else
{
lean_object* x_5925; lean_object* x_5926; lean_object* x_5927; 
x_5925 = lean_ctor_get(x_5923, 0);
x_5926 = lean_ctor_get(x_5923, 1);
lean_inc(x_5926);
lean_inc(x_5925);
lean_dec(x_5923);
x_5927 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5927, 0, x_5925);
lean_ctor_set(x_5927, 1, x_5926);
return x_5927;
}
}
else
{
lean_object* x_5928; lean_object* x_5929; lean_object* x_5930; lean_object* x_5931; lean_object* x_5932; 
x_5928 = l_Lean_mkHole(x_14);
lean_dec(x_14);
x_5929 = lean_unsigned_to_nat(1u);
x_5930 = lean_nat_add(x_3, x_5929);
lean_dec(x_3);
x_5931 = l_Lean_Elab_Term_mkExplicitBinder(x_5919, x_5928);
x_5932 = lean_array_push(x_4, x_5931);
x_3 = x_5930;
x_4 = x_5932;
goto _start;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Binders_11__expandFunBindersAux(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main(x_1, x_2, x_5, x_6, x_3, x_4);
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
lean_object* _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("autoParam is not allowed at 'fun/λ' binders");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optParam is not allowed at 'fun/λ' binders");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_instantiateMVars(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_isOptParam(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isAutoParam(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_box(0);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3;
x_12 = l_Lean_Elab_Term_throwError___rarg(x_11, x_2, x_7);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_4);
lean_dec(x_6);
x_13 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6;
x_14 = l_Lean_Elab_Term_throwError___rarg(x_13, x_2, x_7);
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
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = l_Lean_Expr_isOptParam(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isAutoParam(x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3;
x_26 = l_Lean_Elab_Term_throwError___rarg(x_25, x_2, x_20);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
x_27 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6;
x_28 = l_Lean_Elab_Term_throwError___rarg(x_27, x_2, x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_13__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_4);
x_14 = l_Lean_Elab_Term_whnfForall(x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_11);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 2);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_4);
lean_inc(x_2);
x_25 = l_Lean_Elab_Term_isDefEq(x_2, x_23, x_4, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(x_2, x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_expr_instantiate1(x_24, x_1);
lean_dec(x_24);
lean_ctor_set(x_6, 0, x_30);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_9);
lean_ctor_set(x_31, 2, x_10);
lean_ctor_set(x_31, 3, x_6);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_expr_instantiate1(x_24, x_1);
lean_dec(x_24);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set(x_34, 2, x_10);
lean_ctor_set(x_34, 3, x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_24);
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
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
else
{
lean_object* x_44; 
lean_dec(x_15);
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_44 = lean_box(0);
x_18 = x_44;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_20 = lean_alloc_ctor(0, 4, 0);
} else {
 x_20 = x_11;
}
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_19);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_6);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_6, 0);
lean_inc(x_49);
lean_dec(x_6);
lean_inc(x_4);
x_50 = l_Lean_Elab_Term_whnfForall(x_49, x_4, x_5);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_obj_tag(x_51) == 7)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_11);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 2);
lean_inc(x_60);
lean_dec(x_51);
lean_inc(x_4);
lean_inc(x_2);
x_61 = l_Lean_Elab_Term_isDefEq(x_2, x_59, x_4, x_52);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(x_2, x_4, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
x_66 = lean_expr_instantiate1(x_60, x_1);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_8);
lean_ctor_set(x_68, 1, x_9);
lean_ctor_set(x_68, 2, x_10);
lean_ctor_set(x_68, 3, x_67);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_60);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_76 = x_61;
} else {
 lean_dec_ref(x_61);
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
else
{
lean_object* x_78; 
lean_dec(x_51);
lean_dec(x_4);
lean_dec(x_2);
x_78 = lean_box(0);
x_54 = x_78;
goto block_58;
}
block_58:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
x_55 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_56 = lean_alloc_ctor(0, 4, 0);
} else {
 x_56 = x_11;
}
lean_ctor_set(x_56, 0, x_8);
lean_ctor_set(x_56, 1, x_9);
lean_ctor_set(x_56, 2, x_10);
lean_ctor_set(x_56, 3, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_79 = lean_ctor_get(x_50, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_50, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_81 = x_50;
} else {
 lean_dec_ref(x_50);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_13__propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Binders_13__propagateExpectedType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
x_23 = lean_ctor_get(x_4, 6);
x_24 = lean_ctor_get(x_4, 7);
x_25 = lean_ctor_get(x_4, 8);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_29 = lean_ctor_get(x_4, 9);
x_30 = l_Lean_Elab_replaceRef(x_10, x_29);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_17, 1);
lean_dec(x_33);
lean_inc(x_15);
lean_inc(x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 1, x_14);
lean_inc(x_30);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_ctor_set(x_4, 9, x_30);
lean_inc(x_4);
x_34 = l_Lean_Elab_Term_elabType(x_10, x_4, x_5);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_4);
lean_inc(x_35);
x_37 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(x_35, x_4, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_40);
x_42 = l_Lean_mkFVar(x_40);
lean_inc(x_42);
x_43 = lean_array_push(x_13, x_42);
lean_inc(x_14);
lean_ctor_set(x_3, 0, x_43);
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
x_45 = l_Lean_Syntax_getId(x_44);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
lean_dec(x_9);
lean_inc(x_35);
x_47 = lean_local_ctx_mk_local_decl(x_14, x_40, x_45, x_35, x_46);
x_48 = l_Lean_Elab_replaceRef(x_44, x_30);
lean_dec(x_30);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_18);
lean_ctor_set(x_49, 2, x_19);
lean_ctor_set(x_49, 3, x_20);
lean_ctor_set(x_49, 4, x_21);
lean_ctor_set(x_49, 5, x_22);
lean_ctor_set(x_49, 6, x_23);
lean_ctor_set(x_49, 7, x_24);
lean_ctor_set(x_49, 8, x_25);
lean_ctor_set(x_49, 9, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*10, x_26);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 1, x_27);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 2, x_28);
lean_inc(x_35);
x_50 = l___private_Lean_Elab_Binders_13__propagateExpectedType(x_42, x_35, x_3, x_49, x_41);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 2);
x_56 = lean_ctor_get(x_51, 3);
x_57 = lean_ctor_get(x_51, 1);
lean_dec(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_47);
lean_inc(x_54);
lean_ctor_set(x_51, 1, x_47);
lean_inc(x_4);
x_58 = l_Lean_Elab_Term_isClass(x_35, x_4, x_52);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_47);
lean_dec(x_42);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_2, x_61);
lean_dec(x_2);
x_2 = x_62;
x_3 = x_51;
x_5 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_51);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_64);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_42);
x_69 = lean_array_push(x_55, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_2, x_70);
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_47);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_56);
x_2 = x_71;
x_3 = x_72;
x_5 = x_67;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_dec(x_51);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_58);
if (x_74 == 0)
{
return x_58;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_58, 0);
x_76 = lean_ctor_get(x_58, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_58);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_51, 0);
x_79 = lean_ctor_get(x_51, 2);
x_80 = lean_ctor_get(x_51, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_51);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_47);
lean_inc(x_78);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_47);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_80);
lean_inc(x_4);
x_82 = l_Lean_Elab_Term_isClass(x_35, x_4, x_52);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_47);
lean_dec(x_42);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_2, x_85);
lean_dec(x_2);
x_2 = x_86;
x_3 = x_81;
x_5 = x_84;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_81);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_88);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_42);
x_93 = lean_array_push(x_79, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_2, x_94);
lean_dec(x_2);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_78);
lean_ctor_set(x_96, 1, x_47);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_80);
x_2 = x_95;
x_3 = x_96;
x_5 = x_91;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_2);
x_98 = lean_ctor_get(x_82, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_100 = x_82;
} else {
 lean_dec_ref(x_82);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_50);
if (x_102 == 0)
{
return x_50;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_50, 0);
x_104 = lean_ctor_get(x_50, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_50);
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
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_37);
if (x_106 == 0)
{
return x_37;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_37, 0);
x_108 = lean_ctor_get(x_37, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_37);
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
lean_dec(x_4);
lean_dec(x_17);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_34);
if (x_110 == 0)
{
return x_34;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_34, 0);
x_112 = lean_ctor_get(x_34, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_34);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_17, 0);
x_115 = lean_ctor_get(x_17, 3);
x_116 = lean_ctor_get(x_17, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_14);
lean_ctor_set(x_117, 2, x_15);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 4, x_116);
lean_inc(x_30);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_117);
lean_ctor_set(x_4, 9, x_30);
lean_ctor_set(x_4, 0, x_117);
lean_inc(x_4);
x_118 = l_Lean_Elab_Term_elabType(x_10, x_4, x_5);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_4);
lean_inc(x_119);
x_121 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(x_119, x_4, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_124);
x_126 = l_Lean_mkFVar(x_124);
lean_inc(x_126);
x_127 = lean_array_push(x_13, x_126);
lean_inc(x_14);
lean_ctor_set(x_3, 0, x_127);
x_128 = lean_ctor_get(x_9, 0);
lean_inc(x_128);
x_129 = l_Lean_Syntax_getId(x_128);
x_130 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
lean_dec(x_9);
lean_inc(x_119);
x_131 = lean_local_ctx_mk_local_decl(x_14, x_124, x_129, x_119, x_130);
x_132 = l_Lean_Elab_replaceRef(x_128, x_30);
lean_dec(x_30);
lean_dec(x_128);
x_133 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_133, 0, x_117);
lean_ctor_set(x_133, 1, x_18);
lean_ctor_set(x_133, 2, x_19);
lean_ctor_set(x_133, 3, x_20);
lean_ctor_set(x_133, 4, x_21);
lean_ctor_set(x_133, 5, x_22);
lean_ctor_set(x_133, 6, x_23);
lean_ctor_set(x_133, 7, x_24);
lean_ctor_set(x_133, 8, x_25);
lean_ctor_set(x_133, 9, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*10, x_26);
lean_ctor_set_uint8(x_133, sizeof(void*)*10 + 1, x_27);
lean_ctor_set_uint8(x_133, sizeof(void*)*10 + 2, x_28);
lean_inc(x_119);
x_134 = l___private_Lean_Elab_Binders_13__propagateExpectedType(x_126, x_119, x_3, x_133, x_125);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 3);
lean_inc(x_139);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 x_140 = x_135;
} else {
 lean_dec_ref(x_135);
 x_140 = lean_box(0);
}
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_131);
lean_inc(x_137);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 4, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_131);
lean_ctor_set(x_141, 2, x_138);
lean_ctor_set(x_141, 3, x_139);
lean_inc(x_4);
x_142 = l_Lean_Elab_Term_isClass(x_119, x_4, x_136);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_131);
lean_dec(x_126);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_2, x_145);
lean_dec(x_2);
x_2 = x_146;
x_3 = x_141;
x_5 = x_144;
goto _start;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_141);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_dec(x_142);
x_149 = lean_ctor_get(x_143, 0);
lean_inc(x_149);
lean_dec(x_143);
x_150 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_148);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_126);
x_153 = lean_array_push(x_138, x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_add(x_2, x_154);
lean_dec(x_2);
x_156 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_156, 0, x_137);
lean_ctor_set(x_156, 1, x_131);
lean_ctor_set(x_156, 2, x_153);
lean_ctor_set(x_156, 3, x_139);
x_2 = x_155;
x_3 = x_156;
x_5 = x_151;
goto _start;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_4);
lean_dec(x_2);
x_158 = lean_ctor_get(x_142, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_142, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_160 = x_142;
} else {
 lean_dec_ref(x_142);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_2);
x_162 = lean_ctor_get(x_134, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_134, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_164 = x_134;
} else {
 lean_dec_ref(x_134);
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
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_117);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_166 = lean_ctor_get(x_121, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_121, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_168 = x_121;
} else {
 lean_dec_ref(x_121);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_4);
lean_dec(x_117);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_170 = lean_ctor_get(x_118, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_118, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_172 = x_118;
} else {
 lean_dec_ref(x_118);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_174 = lean_ctor_get(x_3, 0);
x_175 = lean_ctor_get(x_3, 1);
x_176 = lean_ctor_get(x_3, 2);
x_177 = lean_ctor_get(x_3, 3);
x_178 = lean_ctor_get(x_4, 0);
x_179 = lean_ctor_get(x_4, 1);
x_180 = lean_ctor_get(x_4, 2);
x_181 = lean_ctor_get(x_4, 3);
x_182 = lean_ctor_get(x_4, 4);
x_183 = lean_ctor_get(x_4, 5);
x_184 = lean_ctor_get(x_4, 6);
x_185 = lean_ctor_get(x_4, 7);
x_186 = lean_ctor_get(x_4, 8);
x_187 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_188 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_189 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_190 = lean_ctor_get(x_4, 9);
lean_inc(x_190);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_4);
x_191 = l_Lean_Elab_replaceRef(x_10, x_190);
lean_dec(x_190);
x_192 = lean_ctor_get(x_178, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_178, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_178, 4);
lean_inc(x_194);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 x_195 = x_178;
} else {
 lean_dec_ref(x_178);
 x_195 = lean_box(0);
}
lean_inc(x_176);
lean_inc(x_175);
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_175);
lean_ctor_set(x_196, 2, x_176);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 4, x_194);
lean_inc(x_191);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_196);
x_197 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_179);
lean_ctor_set(x_197, 2, x_180);
lean_ctor_set(x_197, 3, x_181);
lean_ctor_set(x_197, 4, x_182);
lean_ctor_set(x_197, 5, x_183);
lean_ctor_set(x_197, 6, x_184);
lean_ctor_set(x_197, 7, x_185);
lean_ctor_set(x_197, 8, x_186);
lean_ctor_set(x_197, 9, x_191);
lean_ctor_set_uint8(x_197, sizeof(void*)*10, x_187);
lean_ctor_set_uint8(x_197, sizeof(void*)*10 + 1, x_188);
lean_ctor_set_uint8(x_197, sizeof(void*)*10 + 2, x_189);
lean_inc(x_197);
x_198 = l_Lean_Elab_Term_elabType(x_10, x_197, x_5);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_197);
lean_inc(x_199);
x_201 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(x_199, x_197, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_202);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_204);
x_206 = l_Lean_mkFVar(x_204);
lean_inc(x_206);
x_207 = lean_array_push(x_174, x_206);
lean_inc(x_175);
lean_ctor_set(x_3, 0, x_207);
x_208 = lean_ctor_get(x_9, 0);
lean_inc(x_208);
x_209 = l_Lean_Syntax_getId(x_208);
x_210 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
lean_dec(x_9);
lean_inc(x_199);
x_211 = lean_local_ctx_mk_local_decl(x_175, x_204, x_209, x_199, x_210);
x_212 = l_Lean_Elab_replaceRef(x_208, x_191);
lean_dec(x_191);
lean_dec(x_208);
x_213 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_213, 0, x_196);
lean_ctor_set(x_213, 1, x_179);
lean_ctor_set(x_213, 2, x_180);
lean_ctor_set(x_213, 3, x_181);
lean_ctor_set(x_213, 4, x_182);
lean_ctor_set(x_213, 5, x_183);
lean_ctor_set(x_213, 6, x_184);
lean_ctor_set(x_213, 7, x_185);
lean_ctor_set(x_213, 8, x_186);
lean_ctor_set(x_213, 9, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*10, x_187);
lean_ctor_set_uint8(x_213, sizeof(void*)*10 + 1, x_188);
lean_ctor_set_uint8(x_213, sizeof(void*)*10 + 2, x_189);
lean_inc(x_199);
x_214 = l___private_Lean_Elab_Binders_13__propagateExpectedType(x_206, x_199, x_3, x_213, x_205);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_215, 3);
lean_inc(x_219);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 x_220 = x_215;
} else {
 lean_dec_ref(x_215);
 x_220 = lean_box(0);
}
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_211);
lean_inc(x_217);
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 4, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_217);
lean_ctor_set(x_221, 1, x_211);
lean_ctor_set(x_221, 2, x_218);
lean_ctor_set(x_221, 3, x_219);
lean_inc(x_197);
x_222 = l_Lean_Elab_Term_isClass(x_199, x_197, x_216);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_211);
lean_dec(x_206);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_nat_add(x_2, x_225);
lean_dec(x_2);
x_2 = x_226;
x_3 = x_221;
x_4 = x_197;
x_5 = x_224;
goto _start;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_221);
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
lean_dec(x_222);
x_229 = lean_ctor_get(x_223, 0);
lean_inc(x_229);
lean_dec(x_223);
x_230 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_228);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_206);
x_233 = lean_array_push(x_218, x_232);
x_234 = lean_unsigned_to_nat(1u);
x_235 = lean_nat_add(x_2, x_234);
lean_dec(x_2);
x_236 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_236, 0, x_217);
lean_ctor_set(x_236, 1, x_211);
lean_ctor_set(x_236, 2, x_233);
lean_ctor_set(x_236, 3, x_219);
x_2 = x_235;
x_3 = x_236;
x_4 = x_197;
x_5 = x_231;
goto _start;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_197);
lean_dec(x_2);
x_238 = lean_ctor_get(x_222, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_222, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_240 = x_222;
} else {
 lean_dec_ref(x_222);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_211);
lean_dec(x_206);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_2);
x_242 = lean_ctor_get(x_214, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_214, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_244 = x_214;
} else {
 lean_dec_ref(x_214);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_191);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_free_object(x_3);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_9);
lean_dec(x_2);
x_246 = lean_ctor_get(x_201, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_201, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_248 = x_201;
} else {
 lean_dec_ref(x_201);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_191);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_free_object(x_3);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_9);
lean_dec(x_2);
x_250 = lean_ctor_get(x_198, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_198, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_252 = x_198;
} else {
 lean_dec_ref(x_198);
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
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_254 = lean_ctor_get(x_3, 0);
x_255 = lean_ctor_get(x_3, 1);
x_256 = lean_ctor_get(x_3, 2);
x_257 = lean_ctor_get(x_3, 3);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_3);
x_258 = lean_ctor_get(x_4, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_4, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_4, 2);
lean_inc(x_260);
x_261 = lean_ctor_get(x_4, 3);
lean_inc(x_261);
x_262 = lean_ctor_get(x_4, 4);
lean_inc(x_262);
x_263 = lean_ctor_get(x_4, 5);
lean_inc(x_263);
x_264 = lean_ctor_get(x_4, 6);
lean_inc(x_264);
x_265 = lean_ctor_get(x_4, 7);
lean_inc(x_265);
x_266 = lean_ctor_get(x_4, 8);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_268 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_269 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_270 = lean_ctor_get(x_4, 9);
lean_inc(x_270);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_271 = x_4;
} else {
 lean_dec_ref(x_4);
 x_271 = lean_box(0);
}
x_272 = l_Lean_Elab_replaceRef(x_10, x_270);
lean_dec(x_270);
x_273 = lean_ctor_get(x_258, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_258, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_258, 4);
lean_inc(x_275);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 lean_ctor_release(x_258, 4);
 x_276 = x_258;
} else {
 lean_dec_ref(x_258);
 x_276 = lean_box(0);
}
lean_inc(x_256);
lean_inc(x_255);
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 5, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_273);
lean_ctor_set(x_277, 1, x_255);
lean_ctor_set(x_277, 2, x_256);
lean_ctor_set(x_277, 3, x_274);
lean_ctor_set(x_277, 4, x_275);
lean_inc(x_272);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_277);
if (lean_is_scalar(x_271)) {
 x_278 = lean_alloc_ctor(0, 10, 3);
} else {
 x_278 = x_271;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_259);
lean_ctor_set(x_278, 2, x_260);
lean_ctor_set(x_278, 3, x_261);
lean_ctor_set(x_278, 4, x_262);
lean_ctor_set(x_278, 5, x_263);
lean_ctor_set(x_278, 6, x_264);
lean_ctor_set(x_278, 7, x_265);
lean_ctor_set(x_278, 8, x_266);
lean_ctor_set(x_278, 9, x_272);
lean_ctor_set_uint8(x_278, sizeof(void*)*10, x_267);
lean_ctor_set_uint8(x_278, sizeof(void*)*10 + 1, x_268);
lean_ctor_set_uint8(x_278, sizeof(void*)*10 + 2, x_269);
lean_inc(x_278);
x_279 = l_Lean_Elab_Term_elabType(x_10, x_278, x_5);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_278);
lean_inc(x_280);
x_282 = l___private_Lean_Elab_Binders_12__checkNoOptAutoParam(x_280, x_278, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_285);
x_287 = l_Lean_mkFVar(x_285);
lean_inc(x_287);
x_288 = lean_array_push(x_254, x_287);
lean_inc(x_255);
x_289 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_255);
lean_ctor_set(x_289, 2, x_256);
lean_ctor_set(x_289, 3, x_257);
x_290 = lean_ctor_get(x_9, 0);
lean_inc(x_290);
x_291 = l_Lean_Syntax_getId(x_290);
x_292 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
lean_dec(x_9);
lean_inc(x_280);
x_293 = lean_local_ctx_mk_local_decl(x_255, x_285, x_291, x_280, x_292);
x_294 = l_Lean_Elab_replaceRef(x_290, x_272);
lean_dec(x_272);
lean_dec(x_290);
x_295 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_295, 0, x_277);
lean_ctor_set(x_295, 1, x_259);
lean_ctor_set(x_295, 2, x_260);
lean_ctor_set(x_295, 3, x_261);
lean_ctor_set(x_295, 4, x_262);
lean_ctor_set(x_295, 5, x_263);
lean_ctor_set(x_295, 6, x_264);
lean_ctor_set(x_295, 7, x_265);
lean_ctor_set(x_295, 8, x_266);
lean_ctor_set(x_295, 9, x_294);
lean_ctor_set_uint8(x_295, sizeof(void*)*10, x_267);
lean_ctor_set_uint8(x_295, sizeof(void*)*10 + 1, x_268);
lean_ctor_set_uint8(x_295, sizeof(void*)*10 + 2, x_269);
lean_inc(x_280);
x_296 = l___private_Lean_Elab_Binders_13__propagateExpectedType(x_287, x_280, x_289, x_295, x_286);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 3);
lean_inc(x_301);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 lean_ctor_release(x_297, 2);
 lean_ctor_release(x_297, 3);
 x_302 = x_297;
} else {
 lean_dec_ref(x_297);
 x_302 = lean_box(0);
}
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_293);
lean_inc(x_299);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 4, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_293);
lean_ctor_set(x_303, 2, x_300);
lean_ctor_set(x_303, 3, x_301);
lean_inc(x_278);
x_304 = l_Lean_Elab_Term_isClass(x_280, x_278, x_298);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_287);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_unsigned_to_nat(1u);
x_308 = lean_nat_add(x_2, x_307);
lean_dec(x_2);
x_2 = x_308;
x_3 = x_303;
x_4 = x_278;
x_5 = x_306;
goto _start;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_303);
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
lean_dec(x_304);
x_311 = lean_ctor_get(x_305, 0);
lean_inc(x_311);
lean_dec(x_305);
x_312 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_310);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_287);
x_315 = lean_array_push(x_300, x_314);
x_316 = lean_unsigned_to_nat(1u);
x_317 = lean_nat_add(x_2, x_316);
lean_dec(x_2);
x_318 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_318, 0, x_299);
lean_ctor_set(x_318, 1, x_293);
lean_ctor_set(x_318, 2, x_315);
lean_ctor_set(x_318, 3, x_301);
x_2 = x_317;
x_3 = x_318;
x_4 = x_278;
x_5 = x_313;
goto _start;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_287);
lean_dec(x_278);
lean_dec(x_2);
x_320 = lean_ctor_get(x_304, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_304, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_322 = x_304;
} else {
 lean_dec_ref(x_304);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_293);
lean_dec(x_287);
lean_dec(x_280);
lean_dec(x_278);
lean_dec(x_2);
x_324 = lean_ctor_get(x_296, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_296, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_326 = x_296;
} else {
 lean_dec_ref(x_296);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_280);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_272);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_9);
lean_dec(x_2);
x_328 = lean_ctor_get(x_282, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_282, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_330 = x_282;
} else {
 lean_dec_ref(x_282);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_272);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_9);
lean_dec(x_2);
x_332 = lean_ctor_get(x_279, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_279, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_334 = x_279;
} else {
 lean_dec_ref(x_279);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Binders_14__elabFunBinderViews___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Binders_14__elabFunBinderViews___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_14__elabFunBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Binders_14__elabFunBinderViews(x_1, x_2, x_3, x_4, x_5);
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
x_10 = l___private_Lean_Elab_Binders_6__matchBinder(x_9, x_4, x_5);
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
x_14 = l___private_Lean_Elab_Binders_14__elabFunBinderViews___main(x_11, x_13, x_3, x_4, x_12);
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
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Elab_Term_getLCtx(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getLocalInsts(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_empty___closed__1;
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_2);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_16 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux___main(x_1, x_15, x_14, x_4, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_20 = lean_array_get_size(x_11);
lean_dec(x_11);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 3);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_20, x_25);
lean_dec(x_25);
lean_dec(x_20);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_4, 0);
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
x_32 = lean_apply_4(x_3, x_21, x_24, x_4, x_18);
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
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_apply_4(x_3, x_21, x_24, x_4, x_18);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 2);
x_41 = lean_ctor_get(x_4, 3);
x_42 = lean_ctor_get(x_4, 4);
x_43 = lean_ctor_get(x_4, 5);
x_44 = lean_ctor_get(x_4, 6);
x_45 = lean_ctor_get(x_4, 7);
x_46 = lean_ctor_get(x_4, 8);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_50 = lean_ctor_get(x_4, 9);
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
lean_dec(x_4);
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
lean_ctor_set(x_56, 9, x_50);
lean_ctor_set_uint8(x_56, sizeof(void*)*10, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 1, x_48);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 2, x_49);
x_57 = lean_apply_4(x_3, x_21, x_24, x_56, x_18);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
lean_dec(x_59);
x_162 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_18);
x_163 = lean_ctor_get(x_4, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = !lean_is_exclusive(x_4);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_4, 0);
lean_dec(x_166);
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_163, 2);
lean_dec(x_168);
x_169 = lean_ctor_get(x_163, 1);
lean_dec(x_169);
lean_ctor_set(x_163, 2, x_23);
lean_ctor_set(x_163, 1, x_22);
x_170 = lean_apply_4(x_3, x_21, x_24, x_4, x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_171);
x_61 = x_173;
x_62 = x_172;
goto block_161;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
lean_dec(x_170);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_174);
x_61 = x_176;
x_62 = x_175;
goto block_161;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_163, 0);
x_178 = lean_ctor_get(x_163, 3);
x_179 = lean_ctor_get(x_163, 4);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_163);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_22);
lean_ctor_set(x_180, 2, x_23);
lean_ctor_set(x_180, 3, x_178);
lean_ctor_set(x_180, 4, x_179);
lean_ctor_set(x_4, 0, x_180);
x_181 = lean_apply_4(x_3, x_21, x_24, x_4, x_164);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_182);
x_61 = x_184;
x_62 = x_183;
goto block_161;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_185);
x_61 = x_187;
x_62 = x_186;
goto block_161;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_188 = lean_ctor_get(x_4, 1);
x_189 = lean_ctor_get(x_4, 2);
x_190 = lean_ctor_get(x_4, 3);
x_191 = lean_ctor_get(x_4, 4);
x_192 = lean_ctor_get(x_4, 5);
x_193 = lean_ctor_get(x_4, 6);
x_194 = lean_ctor_get(x_4, 7);
x_195 = lean_ctor_get(x_4, 8);
x_196 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_197 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_198 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_199 = lean_ctor_get(x_4, 9);
lean_inc(x_199);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_4);
x_200 = lean_ctor_get(x_163, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_163, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_163, 4);
lean_inc(x_202);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 x_203 = x_163;
} else {
 lean_dec_ref(x_163);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_200);
lean_ctor_set(x_204, 1, x_22);
lean_ctor_set(x_204, 2, x_23);
lean_ctor_set(x_204, 3, x_201);
lean_ctor_set(x_204, 4, x_202);
x_205 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_188);
lean_ctor_set(x_205, 2, x_189);
lean_ctor_set(x_205, 3, x_190);
lean_ctor_set(x_205, 4, x_191);
lean_ctor_set(x_205, 5, x_192);
lean_ctor_set(x_205, 6, x_193);
lean_ctor_set(x_205, 7, x_194);
lean_ctor_set(x_205, 8, x_195);
lean_ctor_set(x_205, 9, x_199);
lean_ctor_set_uint8(x_205, sizeof(void*)*10, x_196);
lean_ctor_set_uint8(x_205, sizeof(void*)*10 + 1, x_197);
lean_ctor_set_uint8(x_205, sizeof(void*)*10 + 2, x_198);
x_206 = lean_apply_4(x_3, x_21, x_24, x_205, x_164);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_207);
x_61 = x_209;
x_62 = x_208;
goto block_161;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_dec(x_206);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_210);
x_61 = x_212;
x_62 = x_211;
goto block_161;
}
}
block_161:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_63, 2);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_64);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_64, 2);
lean_dec(x_71);
lean_ctor_set(x_64, 2, x_60);
if (lean_is_scalar(x_19)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_19;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_62);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_64, 0);
x_74 = lean_ctor_get(x_64, 1);
x_75 = lean_ctor_get(x_64, 3);
x_76 = lean_ctor_get(x_64, 4);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_64);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_60);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_63, 2, x_77);
if (lean_is_scalar(x_19)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_19;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_62);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_63, 0);
x_80 = lean_ctor_get(x_63, 1);
x_81 = lean_ctor_get(x_63, 3);
x_82 = lean_ctor_get(x_63, 4);
x_83 = lean_ctor_get(x_63, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_63);
x_84 = lean_ctor_get(x_64, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_64, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_64, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_64, 4);
lean_inc(x_87);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 x_88 = x_64;
} else {
 lean_dec_ref(x_64);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 5, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_60);
lean_ctor_set(x_89, 3, x_86);
lean_ctor_set(x_89, 4, x_87);
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_80);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_81);
lean_ctor_set(x_90, 4, x_82);
lean_ctor_set(x_90, 5, x_83);
lean_ctor_set(x_62, 0, x_90);
if (lean_is_scalar(x_19)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_19;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_65);
lean_ctor_set(x_91, 1, x_62);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_92 = lean_ctor_get(x_62, 1);
x_93 = lean_ctor_get(x_62, 2);
x_94 = lean_ctor_get(x_62, 3);
x_95 = lean_ctor_get(x_62, 4);
x_96 = lean_ctor_get(x_62, 5);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_62);
x_97 = lean_ctor_get(x_63, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_63, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_63, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_63, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_63, 5);
lean_inc(x_101);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 x_102 = x_63;
} else {
 lean_dec_ref(x_63);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_64, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_64, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_64, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_64, 4);
lean_inc(x_106);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 x_107 = x_64;
} else {
 lean_dec_ref(x_64);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_60);
lean_ctor_set(x_108, 3, x_105);
lean_ctor_set(x_108, 4, x_106);
if (lean_is_scalar(x_102)) {
 x_109 = lean_alloc_ctor(0, 6, 0);
} else {
 x_109 = x_102;
}
lean_ctor_set(x_109, 0, x_97);
lean_ctor_set(x_109, 1, x_98);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_99);
lean_ctor_set(x_109, 4, x_100);
lean_ctor_set(x_109, 5, x_101);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_92);
lean_ctor_set(x_110, 2, x_93);
lean_ctor_set(x_110, 3, x_94);
lean_ctor_set(x_110, 4, x_95);
lean_ctor_set(x_110, 5, x_96);
if (lean_is_scalar(x_19)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_19;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_65);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_62, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_61, 0);
lean_inc(x_114);
lean_dec(x_61);
x_115 = !lean_is_exclusive(x_62);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_62, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_112);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_112, 2);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_113);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_113, 2);
lean_dec(x_120);
lean_ctor_set(x_113, 2, x_60);
if (lean_is_scalar(x_19)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_19;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_62);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_113, 0);
x_123 = lean_ctor_get(x_113, 1);
x_124 = lean_ctor_get(x_113, 3);
x_125 = lean_ctor_get(x_113, 4);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_113);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_60);
lean_ctor_set(x_126, 3, x_124);
lean_ctor_set(x_126, 4, x_125);
lean_ctor_set(x_112, 2, x_126);
if (lean_is_scalar(x_19)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_19;
}
lean_ctor_set(x_127, 0, x_114);
lean_ctor_set(x_127, 1, x_62);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_112, 0);
x_129 = lean_ctor_get(x_112, 1);
x_130 = lean_ctor_get(x_112, 3);
x_131 = lean_ctor_get(x_112, 4);
x_132 = lean_ctor_get(x_112, 5);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_112);
x_133 = lean_ctor_get(x_113, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_113, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_113, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_113, 4);
lean_inc(x_136);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_137 = x_113;
} else {
 lean_dec_ref(x_113);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 5, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_133);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_138, 2, x_60);
lean_ctor_set(x_138, 3, x_135);
lean_ctor_set(x_138, 4, x_136);
x_139 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_129);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_130);
lean_ctor_set(x_139, 4, x_131);
lean_ctor_set(x_139, 5, x_132);
lean_ctor_set(x_62, 0, x_139);
if (lean_is_scalar(x_19)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_19;
}
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_62);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_141 = lean_ctor_get(x_62, 1);
x_142 = lean_ctor_get(x_62, 2);
x_143 = lean_ctor_get(x_62, 3);
x_144 = lean_ctor_get(x_62, 4);
x_145 = lean_ctor_get(x_62, 5);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_62);
x_146 = lean_ctor_get(x_112, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_112, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_112, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_112, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_112, 5);
lean_inc(x_150);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 x_151 = x_112;
} else {
 lean_dec_ref(x_112);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_113, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_113, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_113, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_113, 4);
lean_inc(x_155);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_156 = x_113;
} else {
 lean_dec_ref(x_113);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_153);
lean_ctor_set(x_157, 2, x_60);
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
x_159 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_141);
lean_ctor_set(x_159, 2, x_142);
lean_ctor_set(x_159, 3, x_143);
lean_ctor_set(x_159, 4, x_144);
lean_ctor_set(x_159, 5, x_145);
if (lean_is_scalar(x_19)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_19;
}
lean_ctor_set(x_160, 0, x_114);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_16);
if (x_213 == 0)
{
return x_16;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_16, 0);
x_215 = lean_ctor_get(x_16, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_16);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = l_Array_empty___closed__1;
x_218 = lean_apply_4(x_3, x_217, x_2, x_4, x_5);
return x_218;
}
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFunBinders___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_elabFunBinders___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabFun___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
lean_inc(x_4);
x_7 = l_Lean_Elab_Term_elabTerm(x_1, x_3, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_mkLambda(x_2, x_8, x_4, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_expandFunBinders(x_7, x_9, x_3, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun___lambda__1), 5, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Term_elabFunBinders___rarg(x_16, x_2, x_18, x_3, x_15);
lean_dec(x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_20);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_getMainModule___rarg(x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_empty___closed__1;
x_29 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_21, x_21, x_27, x_28);
lean_dec(x_21);
x_30 = l_Lean_nullKind___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_array_push(x_35, x_22);
x_37 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_3, 7);
lean_inc(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_3, 7, x_42);
x_43 = 1;
x_44 = l_Lean_Elab_Term_elabTerm(x_38, x_2, x_43, x_3, x_26);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = lean_ctor_get(x_3, 4);
x_50 = lean_ctor_get(x_3, 5);
x_51 = lean_ctor_get(x_3, 6);
x_52 = lean_ctor_get(x_3, 7);
x_53 = lean_ctor_get(x_3, 8);
x_54 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_57 = lean_ctor_get(x_3, 9);
lean_inc(x_57);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
lean_inc(x_38);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_38);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
x_60 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_48);
lean_ctor_set(x_60, 4, x_49);
lean_ctor_set(x_60, 5, x_50);
lean_ctor_set(x_60, 6, x_51);
lean_ctor_set(x_60, 7, x_59);
lean_ctor_set(x_60, 8, x_53);
lean_ctor_set(x_60, 9, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*10, x_54);
lean_ctor_set_uint8(x_60, sizeof(void*)*10 + 1, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*10 + 2, x_56);
x_61 = 1;
x_62 = l_Lean_Elab_Term_elabTerm(x_38, x_2, x_61, x_60, x_26);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
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
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_elabType(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_9, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_mkForall(x_3, x_7, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_mkLambda(x_3, x_11, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
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
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
return x_6;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
lean_inc(x_4);
x_7 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_instantiateMVars(x_8, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkOptionalNode___closed__2;
x_14 = lean_array_push(x_13, x_3);
x_15 = l_Lean_Elab_Term_mkLambda(x_14, x_11, x_4, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
lean_inc(x_4);
x_7 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_instantiateMVars(x_8, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_mkLet(x_3, x_11, x_4, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
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
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__1), 5, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_inc(x_8);
x_11 = l_Lean_Elab_Term_elabBinders___rarg(x_2, x_10, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
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
x_34 = l_Lean_Elab_Term_getOptions(x_8, x_13);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_38 = l_Lean_checkTraceOption(x_35, x_37);
lean_dec(x_35);
if (x_38 == 0)
{
x_16 = x_36;
goto block_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_1);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_1);
x_40 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_14);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_14);
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_15);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_15);
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Term_logTrace(x_37, x_47, x_8, x_36);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_16 = x_49;
goto block_33;
}
block_33:
{
if (x_7 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__2), 5, 2);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
x_18 = 0;
x_19 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_18, x_14, x_17, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_mkApp(x_21, x_15);
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
x_25 = l_Lean_mkApp(x_23, x_15);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_15);
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
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__3), 5, 2);
lean_closure_set(x_31, 0, x_5);
lean_closure_set(x_31, 1, x_6);
x_32 = l_Lean_Elab_Term_withLetDecl___rarg(x_1, x_14, x_15, x_31, x_8, x_16);
return x_32;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
return x_11;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_11, 0);
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_11);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Binders_15__expandLetIdLhs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getRelaxedId(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Term_expandOptType(x_1, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Binders_15__expandLetIdLhs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Binders_15__expandLetIdLhs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_16__getMatchAltNumPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Array_empty___closed__1;
x_8 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_6, x_5, x_2, x_7);
lean_dec(x_5);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Binders_16__getMatchAltNumPatterns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Binders_16__getMatchAltNumPatterns(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__9;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_13);
lean_ctor_set(x_5, 1, x_6);
x_15 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_16 = l_Lean_addMacroScope(x_13, x_15, x_6);
x_17 = lean_box(0);
x_18 = l_Lean_SourceInfo_inhabited___closed__1;
x_19 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2;
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
x_21 = l_Array_empty___closed__1;
x_22 = lean_array_push(x_21, x_20);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_24 = lean_array_push(x_22, x_23);
x_25 = l_Lean_mkTermIdFromIdent___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_isEmpty___rarg(x_4);
x_28 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3;
lean_inc(x_26);
x_29 = lean_array_push(x_28, x_26);
x_30 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
if (x_27 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = l_Lean_mkAtomFrom(x_1, x_32);
x_34 = lean_array_push(x_4, x_33);
x_35 = lean_array_push(x_34, x_31);
x_36 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_2, x_10, x_35, x_5, x_11);
lean_dec(x_10);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_array_push(x_21, x_26);
x_40 = l_Lean_nullKind___closed__2;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_array_push(x_45, x_38);
x_47 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_36, 0, x_48);
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_array_push(x_21, x_26);
x_52 = l_Lean_nullKind___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_57 = lean_array_push(x_55, x_56);
x_58 = lean_array_push(x_57, x_49);
x_59 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_array_push(x_4, x_31);
x_63 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_2, x_10, x_62, x_5, x_11);
lean_dec(x_10);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_array_push(x_21, x_26);
x_67 = l_Lean_nullKind___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_70 = lean_array_push(x_69, x_68);
x_71 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_72 = lean_array_push(x_70, x_71);
x_73 = lean_array_push(x_72, x_65);
x_74 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_63, 0, x_75);
return x_63;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_63, 0);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_63);
x_78 = lean_array_push(x_21, x_26);
x_79 = l_Lean_nullKind___closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_82 = lean_array_push(x_81, x_80);
x_83 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_84 = lean_array_push(x_82, x_83);
x_85 = lean_array_push(x_84, x_76);
x_86 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 2);
x_91 = lean_ctor_get(x_5, 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_89);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_6);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_91);
x_93 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_94 = l_Lean_addMacroScope(x_89, x_93, x_6);
x_95 = lean_box(0);
x_96 = l_Lean_SourceInfo_inhabited___closed__1;
x_97 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2;
x_98 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_95);
x_99 = l_Array_empty___closed__1;
x_100 = lean_array_push(x_99, x_98);
x_101 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_102 = lean_array_push(x_100, x_101);
x_103 = l_Lean_mkTermIdFromIdent___closed__2;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Array_isEmpty___rarg(x_4);
x_106 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3;
lean_inc(x_104);
x_107 = lean_array_push(x_106, x_104);
x_108 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
if (x_105 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_110 = l_List_reprAux___main___rarg___closed__1;
x_111 = l_Lean_mkAtomFrom(x_1, x_110);
x_112 = lean_array_push(x_4, x_111);
x_113 = lean_array_push(x_112, x_109);
x_114 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_2, x_10, x_113, x_92, x_11);
lean_dec(x_10);
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
x_118 = lean_array_push(x_99, x_104);
x_119 = l_Lean_nullKind___closed__2;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_122 = lean_array_push(x_121, x_120);
x_123 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_124 = lean_array_push(x_122, x_123);
x_125 = lean_array_push(x_124, x_115);
x_126 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
if (lean_is_scalar(x_117)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_117;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_116);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_129 = lean_array_push(x_4, x_109);
x_130 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_2, x_10, x_129, x_92, x_11);
lean_dec(x_10);
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
x_134 = lean_array_push(x_99, x_104);
x_135 = l_Lean_nullKind___closed__2;
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_138 = lean_array_push(x_137, x_136);
x_139 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_140 = lean_array_push(x_138, x_139);
x_141 = lean_array_push(x_140, x_131);
x_142 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
if (lean_is_scalar(x_133)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_133;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_132);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_5);
x_145 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_146 = l_Lean_mkAtomFrom(x_1, x_145);
x_147 = l_Lean_nullKind;
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_4);
x_149 = l_Lean_Parser_Term_structInst___elambda__1___closed__7;
x_150 = l_Lean_mkAtomFrom(x_1, x_149);
x_151 = l_Lean_Meta_mkEqNDRec___closed__6;
x_152 = lean_array_push(x_151, x_146);
x_153 = lean_array_push(x_152, x_148);
x_154 = l_Lean_mkOptionalNode___closed__1;
x_155 = lean_array_push(x_153, x_154);
x_156 = lean_array_push(x_155, x_150);
x_157 = lean_array_push(x_156, x_154);
x_158 = lean_array_push(x_157, x_2);
x_159 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_6);
return x_161;
}
}
}
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_56; uint8_t x_57; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_getKind(x_9);
x_56 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_57 = lean_name_eq(x_12, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Parser_Term_letPatDecl___elambda__1___closed__2;
x_59 = lean_name_eq(x_12, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_11);
x_60 = l_Lean_Parser_Term_letEqnsDecl___elambda__1___closed__2;
x_61 = lean_name_eq(x_12, x_60);
lean_dec(x_12);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_5);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_unsigned_to_nat(4u);
x_64 = l_Lean_Syntax_getArg(x_9, x_63);
x_65 = l___private_Lean_Elab_Binders_16__getMatchAltNumPatterns(x_64);
x_66 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getEnv___rarg(x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_70, 5);
x_74 = lean_ctor_get(x_4, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 4);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_environment_main_module(x_71);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_76);
x_79 = l_Array_empty___closed__1;
x_80 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_64, x_65, x_79, x_78, x_73);
lean_dec(x_65);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_ctor_set(x_70, 5, x_82);
x_13 = x_81;
x_14 = x_70;
goto block_55;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_83 = lean_ctor_get(x_70, 0);
x_84 = lean_ctor_get(x_70, 1);
x_85 = lean_ctor_get(x_70, 2);
x_86 = lean_ctor_get(x_70, 3);
x_87 = lean_ctor_get(x_70, 4);
x_88 = lean_ctor_get(x_70, 5);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_70);
x_89 = lean_ctor_get(x_4, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 4);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_environment_main_module(x_71);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_67);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
x_94 = l_Array_empty___closed__1;
x_95 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main(x_1, x_64, x_65, x_94, x_93, x_88);
lean_dec(x_65);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_84);
lean_ctor_set(x_98, 2, x_85);
lean_ctor_set(x_98, 3, x_86);
lean_ctor_set(x_98, 4, x_87);
lean_ctor_set(x_98, 5, x_97);
x_13 = x_96;
x_14 = x_98;
goto block_55;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_12);
lean_dec(x_7);
x_99 = l_Lean_Syntax_getArg(x_9, x_8);
x_100 = lean_unsigned_to_nat(2u);
x_101 = l_Lean_Syntax_getArg(x_9, x_100);
x_102 = l_Lean_Elab_Term_expandOptType(x_1, x_101);
lean_dec(x_101);
x_103 = lean_unsigned_to_nat(4u);
x_104 = l_Lean_Syntax_getArg(x_9, x_103);
lean_dec(x_9);
x_105 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Elab_Term_getMainModule___rarg(x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_112 = l_Lean_addMacroScope(x_109, x_111, x_106);
x_113 = lean_box(0);
x_114 = l_Lean_SourceInfo_inhabited___closed__1;
x_115 = l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2;
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set(x_116, 3, x_113);
x_117 = l_Array_empty___closed__1;
x_118 = lean_array_push(x_117, x_116);
x_119 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_120 = lean_array_push(x_118, x_119);
x_121 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_122 = lean_array_push(x_121, x_102);
x_123 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_array_push(x_117, x_124);
x_126 = l_Lean_nullKind___closed__2;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
lean_inc(x_120);
x_128 = lean_array_push(x_120, x_127);
x_129 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_130 = lean_array_push(x_128, x_129);
x_131 = lean_array_push(x_130, x_104);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_56);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_117, x_132);
x_134 = l_Lean_Parser_Term_letDecl___closed__2;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_137 = lean_array_push(x_136, x_135);
x_138 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_139 = lean_array_push(x_137, x_138);
x_140 = l_Lean_mkTermIdFromIdent___closed__2;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_120);
x_142 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_143 = lean_array_push(x_142, x_141);
x_144 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_array_push(x_117, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_126);
lean_ctor_set(x_147, 1, x_146);
x_148 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_149 = lean_array_push(x_148, x_147);
x_150 = lean_array_push(x_149, x_119);
x_151 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_152 = lean_array_push(x_150, x_151);
x_153 = lean_array_push(x_152, x_119);
x_154 = lean_array_push(x_117, x_99);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_126);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_push(x_117, x_155);
x_157 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_158 = lean_array_push(x_156, x_157);
x_159 = lean_array_push(x_158, x_11);
x_160 = l_Lean_Parser_Term_matchAlt___closed__2;
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_array_push(x_117, x_161);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_126);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_array_push(x_153, x_163);
x_165 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_array_push(x_139, x_166);
x_168 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
if (x_3 == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_4, 7);
x_172 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
x_173 = l_Lean_Syntax_updateKind(x_169, x_172);
lean_inc(x_173);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_1);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
lean_ctor_set(x_4, 7, x_175);
x_176 = 1;
x_177 = l_Lean_Elab_Term_elabTerm(x_173, x_2, x_176, x_4, x_110);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_178 = lean_ctor_get(x_4, 0);
x_179 = lean_ctor_get(x_4, 1);
x_180 = lean_ctor_get(x_4, 2);
x_181 = lean_ctor_get(x_4, 3);
x_182 = lean_ctor_get(x_4, 4);
x_183 = lean_ctor_get(x_4, 5);
x_184 = lean_ctor_get(x_4, 6);
x_185 = lean_ctor_get(x_4, 7);
x_186 = lean_ctor_get(x_4, 8);
x_187 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_188 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_189 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_190 = lean_ctor_get(x_4, 9);
lean_inc(x_190);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_4);
x_191 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
x_192 = l_Lean_Syntax_updateKind(x_169, x_191);
lean_inc(x_192);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_1);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_185);
x_195 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_195, 0, x_178);
lean_ctor_set(x_195, 1, x_179);
lean_ctor_set(x_195, 2, x_180);
lean_ctor_set(x_195, 3, x_181);
lean_ctor_set(x_195, 4, x_182);
lean_ctor_set(x_195, 5, x_183);
lean_ctor_set(x_195, 6, x_184);
lean_ctor_set(x_195, 7, x_194);
lean_ctor_set(x_195, 8, x_186);
lean_ctor_set(x_195, 9, x_190);
lean_ctor_set_uint8(x_195, sizeof(void*)*10, x_187);
lean_ctor_set_uint8(x_195, sizeof(void*)*10 + 1, x_188);
lean_ctor_set_uint8(x_195, sizeof(void*)*10 + 2, x_189);
x_196 = 1;
x_197 = l_Lean_Elab_Term_elabTerm(x_192, x_2, x_196, x_195, x_110);
return x_197;
}
}
else
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_4);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_4, 7);
lean_inc(x_169);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_169);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_4, 7, x_201);
x_202 = 1;
x_203 = l_Lean_Elab_Term_elabTerm(x_169, x_2, x_202, x_4, x_110);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; 
x_204 = lean_ctor_get(x_4, 0);
x_205 = lean_ctor_get(x_4, 1);
x_206 = lean_ctor_get(x_4, 2);
x_207 = lean_ctor_get(x_4, 3);
x_208 = lean_ctor_get(x_4, 4);
x_209 = lean_ctor_get(x_4, 5);
x_210 = lean_ctor_get(x_4, 6);
x_211 = lean_ctor_get(x_4, 7);
x_212 = lean_ctor_get(x_4, 8);
x_213 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_214 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_215 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_216 = lean_ctor_get(x_4, 9);
lean_inc(x_216);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_4);
lean_inc(x_169);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_1);
lean_ctor_set(x_217, 1, x_169);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_211);
x_219 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_219, 0, x_204);
lean_ctor_set(x_219, 1, x_205);
lean_ctor_set(x_219, 2, x_206);
lean_ctor_set(x_219, 3, x_207);
lean_ctor_set(x_219, 4, x_208);
lean_ctor_set(x_219, 5, x_209);
lean_ctor_set(x_219, 6, x_210);
lean_ctor_set(x_219, 7, x_218);
lean_ctor_set(x_219, 8, x_212);
lean_ctor_set(x_219, 9, x_216);
lean_ctor_set_uint8(x_219, sizeof(void*)*10, x_213);
lean_ctor_set_uint8(x_219, sizeof(void*)*10 + 1, x_214);
lean_ctor_set_uint8(x_219, sizeof(void*)*10 + 2, x_215);
x_220 = 1;
x_221 = l_Lean_Elab_Term_elabTerm(x_169, x_2, x_220, x_219, x_110);
return x_221;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_222 = l___private_Lean_Elab_Binders_15__expandLetIdLhs(x_9);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = lean_unsigned_to_nat(4u);
x_228 = l_Lean_Syntax_getArg(x_9, x_227);
lean_dec(x_9);
x_229 = l_Lean_Elab_Term_elabLetDeclAux(x_224, x_225, x_226, x_228, x_11, x_2, x_3, x_4, x_5);
lean_dec(x_225);
return x_229;
}
block_55:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_15 = l_Lean_Syntax_getArg(x_9, x_8);
x_16 = l_Lean_Syntax_getArg(x_9, x_6);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_9, x_17);
lean_dec(x_9);
x_19 = l_Lean_formatEntry___closed__1;
x_20 = l_Lean_mkAtomFrom(x_1, x_19);
x_21 = l_Lean_Elab_Term_mkExplicitBinder___closed__5;
x_22 = lean_array_push(x_21, x_15);
x_23 = lean_array_push(x_22, x_16);
x_24 = lean_array_push(x_23, x_18);
x_25 = lean_array_push(x_24, x_20);
x_26 = lean_array_push(x_25, x_13);
x_27 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Syntax_setArg(x_7, x_8, x_28);
lean_inc(x_1);
x_30 = l_Lean_Syntax_setArg(x_1, x_6, x_29);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_4, 7);
lean_inc(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_4, 7, x_34);
x_35 = 1;
x_36 = l_Lean_Elab_Term_elabTerm(x_30, x_2, x_35, x_4, x_14);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
x_39 = lean_ctor_get(x_4, 2);
x_40 = lean_ctor_get(x_4, 3);
x_41 = lean_ctor_get(x_4, 4);
x_42 = lean_ctor_get(x_4, 5);
x_43 = lean_ctor_get(x_4, 6);
x_44 = lean_ctor_get(x_4, 7);
x_45 = lean_ctor_get(x_4, 8);
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_49 = lean_ctor_get(x_4, 9);
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
lean_dec(x_4);
lean_inc(x_30);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
x_52 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_52, 2, x_39);
lean_ctor_set(x_52, 3, x_40);
lean_ctor_set(x_52, 4, x_41);
lean_ctor_set(x_52, 5, x_42);
lean_ctor_set(x_52, 6, x_43);
lean_ctor_set(x_52, 7, x_51);
lean_ctor_set(x_52, 8, x_45);
lean_ctor_set(x_52, 9, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*10, x_46);
lean_ctor_set_uint8(x_52, sizeof(void*)*10 + 1, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*10 + 2, x_48);
x_53 = 1;
x_54 = l_Lean_Elab_Term_elabTerm(x_30, x_2, x_53, x_52, x_14);
return x_54;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDecl), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabLetBangDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetBangDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetBangDecl), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetBangDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_let_x21___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetBangDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Binders_18__regTraceClasses(lean_object* x_1) {
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Binders(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
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
l_Lean_Elab_Term_quoteAutoTactic___main___closed__4 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__4);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__5 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__5);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__6 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__6);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__7 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__7);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__8 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__8);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__9 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__9);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__10 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__10);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__11 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__11);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__12 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__12);
l_Lean_Elab_Term_quoteAutoTactic___main___closed__13 = _init_l_Lean_Elab_Term_quoteAutoTactic___main___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___main___closed__13);
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
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__1 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__1);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__2);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__3 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__3);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__4);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__5 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__5);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__6);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__7 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__7);
l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8 = _init_l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_4__expandBinderModifier___closed__8);
l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Binders_5__getBinderIds___spec__1___closed__3);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabForall(lean_io_mk_world());
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
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__7 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__7);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__9 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__9);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__10 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__10);
l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11 = _init_l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11);
l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__1 = _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__1);
l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__2 = _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__2);
l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3 = _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__3);
l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__4 = _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__4);
l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__5 = _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__5);
l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6 = _init_l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_12__checkNoOptAutoParam___closed__6);
l___regBuiltin_Lean_Elab_Term_elabFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabFun___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabLetDeclAux___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__3);
l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__1 = _init_l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__1);
l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2 = _init_l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__2);
l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3 = _init_l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_17__expandLetEqnsDeclVal___main___closed__3);
l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetBangDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetBangDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetBangDecl___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabLetBangDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Binders_18__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
