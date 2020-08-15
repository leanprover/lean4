// Lean compiler output
// Module: Lean.Elab.Tactic.Induction
// Imports: Init Lean.Meta.RecursorInfo Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Cases Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Generalize
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
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__5;
lean_object* l_Lean_Elab_Tactic_evalCases(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__5;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__2;
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_trace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7;
lean_object* l_Lean_Elab_Tactic_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
lean_object* l_Lean_Elab_Tactic_restore(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(lean_object*);
lean_object* l_Lean_Elab_Tactic_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withRef___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(lean_object*);
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__3;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_15__isTermRHS___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7;
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_cases___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2;
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_save(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
lean_object* l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2;
lean_object* l_Lean_Elab_Tactic_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4;
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__8;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__4;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1;
lean_object* l_Lean_Meta_getParamNames(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8;
lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8;
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4;
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Syntax_getIdAt(x_5, x_4);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generalize");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_local_ctx_find_from_user_name(x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
x_7 = l_Lean_Elab_Tactic_throwError___rarg(x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_LocalDecl_toExpr(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getLCtx___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_7 = lean_local_ctx_get_unused_name(x_3, x_6);
x_8 = lean_box(0);
x_9 = 0;
lean_inc(x_4);
x_10 = l_Lean_Elab_Tactic_elabTerm(x_1, x_8, x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_7);
x_13 = l_Lean_Elab_Tactic_evalGeneralizeAux(x_2, x_11, x_7, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1), 4, 1);
lean_closure_set(x_15, 0, x_7);
x_16 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_17, x_4, x_14);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTerm___boxed), 5, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
x_9 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_8, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2), 5, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
x_11 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_12, x_3, x_4);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lean_Meta_intro1(x_1, x_4, x_2, x_3);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_mkFVar(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_7, 1, x_13);
lean_ctor_set(x_7, 0, x_11);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_mkFVar(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
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
x_25 = l_Lean_mkFVar(x_22);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
return x_5;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
x_4 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_5; 
lean_dec(x_4);
lean_inc(x_2);
x_5 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_generalize___boxed), 5, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_15, 0, x_9);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_8, x_16, x_2, x_7);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = l_Lean_Elab_Tactic_getFVarIds(x_7, x_3, x_4);
return x_8;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 9);
x_11 = l_Lean_Elab_replaceRef(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 9, x_11);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_trace), 4, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed), 4, 1);
lean_closure_set(x_15, 0, x_5);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_16, x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
x_23 = lean_ctor_get(x_8, 5);
x_24 = lean_ctor_get(x_8, 6);
x_25 = lean_ctor_get(x_8, 7);
x_26 = lean_ctor_get(x_8, 8);
x_27 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_30 = lean_ctor_get(x_8, 9);
lean_inc(x_30);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_31 = l_Lean_Elab_replaceRef(x_1, x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_21);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_23);
lean_ctor_set(x_32, 6, x_24);
lean_ctor_set(x_32, 7, x_25);
lean_ctor_set(x_32, 8, x_26);
lean_ctor_set(x_32, 9, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*10, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 1, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 2, x_29);
lean_ctor_set(x_2, 0, x_32);
lean_inc(x_5);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_33, 0, x_5);
x_34 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_trace), 4, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_33);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed), 4, 1);
lean_closure_set(x_36, 0, x_5);
x_37 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_37, x_2, x_3);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
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
x_47 = lean_ctor_get(x_39, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_39, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 8);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_39, sizeof(void*)*10);
x_51 = lean_ctor_get_uint8(x_39, sizeof(void*)*10 + 1);
x_52 = lean_ctor_get_uint8(x_39, sizeof(void*)*10 + 2);
x_53 = lean_ctor_get(x_39, 9);
lean_inc(x_53);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 lean_ctor_release(x_39, 7);
 lean_ctor_release(x_39, 8);
 lean_ctor_release(x_39, 9);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Elab_replaceRef(x_1, x_53);
lean_dec(x_53);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 10, 3);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_42);
lean_ctor_set(x_56, 2, x_43);
lean_ctor_set(x_56, 3, x_44);
lean_ctor_set(x_56, 4, x_45);
lean_ctor_set(x_56, 5, x_46);
lean_ctor_set(x_56, 6, x_47);
lean_ctor_set(x_56, 7, x_48);
lean_ctor_set(x_56, 8, x_49);
lean_ctor_set(x_56, 9, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*10, x_50);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 1, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 2, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_40);
lean_inc(x_5);
x_58 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_58, 0, x_5);
x_59 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_60 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_trace), 4, 2);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_58);
x_61 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed), 4, 1);
lean_closure_set(x_61, 0, x_5);
x_62 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_62, 0, x_60);
lean_closure_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_62, x_57, x_3);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
lean_dec(x_2);
x_64 = l_Array_empty___closed__1;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
return x_65;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise depends on variable being generalized");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Expr_fvarId_x21(x_1);
x_10 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_array_get_size(x_7);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_free_object(x_3);
lean_dec(x_8);
lean_dec(x_7);
x_15 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_16 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_2, x_16, x_17, x_4, x_5);
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = l_Lean_Expr_fvarId_x21(x_1);
x_26 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_27 = lean_array_get_size(x_23);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_23);
x_32 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_33 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_2, x_33, x_34, x_4, x_5);
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
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = 0;
x_14 = lean_box(x_13);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_revert___boxed), 5, 3);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_14);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed), 5, 2);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_11);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_11, x_20, x_3, x_10);
lean_dec(x_11);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
x_5 = l_Lean_Name_eraseMacroScopes(x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = x_4;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(x_6, x_5);
x_8 = x_7;
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_10__getAltRHS(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_1, x_2, x_5);
x_7 = l_Lean_Name_isSuffixOf___main(x_1, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkAlt");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor name '");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_10);
lean_inc(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_13, 9);
x_17 = l_Lean_Elab_replaceRef(x_10, x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 9, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
x_19 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_12);
x_21 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_20, x_18, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_mkThunk___closed__1;
x_24 = lean_name_eq(x_11, x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = 0;
x_26 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_11, x_25, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_10, x_27);
lean_dec(x_10);
x_29 = l_Lean_Name_toString___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_11);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_4);
x_37 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_28, x_36, x_4, x_22);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
lean_dec(x_3);
x_3 = x_40;
x_5 = x_38;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
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
lean_dec(x_11);
lean_dec(x_10);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_3, x_46);
lean_dec(x_3);
x_3 = x_47;
x_5 = x_22;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_11);
lean_dec(x_10);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_3, x_49);
lean_dec(x_3);
x_3 = x_50;
x_5 = x_22;
goto _start;
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
x_58 = lean_ctor_get(x_13, 2);
x_59 = lean_ctor_get(x_13, 3);
x_60 = lean_ctor_get(x_13, 4);
x_61 = lean_ctor_get(x_13, 5);
x_62 = lean_ctor_get(x_13, 6);
x_63 = lean_ctor_get(x_13, 7);
x_64 = lean_ctor_get(x_13, 8);
x_65 = lean_ctor_get_uint8(x_13, sizeof(void*)*10);
x_66 = lean_ctor_get_uint8(x_13, sizeof(void*)*10 + 1);
x_67 = lean_ctor_get_uint8(x_13, sizeof(void*)*10 + 2);
x_68 = lean_ctor_get(x_13, 9);
lean_inc(x_68);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_69 = l_Lean_Elab_replaceRef(x_10, x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_57);
lean_ctor_set(x_70, 2, x_58);
lean_ctor_set(x_70, 3, x_59);
lean_ctor_set(x_70, 4, x_60);
lean_ctor_set(x_70, 5, x_61);
lean_ctor_set(x_70, 6, x_62);
lean_ctor_set(x_70, 7, x_63);
lean_ctor_set(x_70, 8, x_64);
lean_ctor_set(x_70, 9, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*10, x_65);
lean_ctor_set_uint8(x_70, sizeof(void*)*10 + 1, x_66);
lean_ctor_set_uint8(x_70, sizeof(void*)*10 + 2, x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_14);
x_72 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, x_12);
x_74 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_73, x_71, x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_mkThunk___closed__1;
x_77 = lean_name_eq(x_11, x_76);
if (x_77 == 0)
{
uint8_t x_78; uint8_t x_79; 
x_78 = 0;
x_79 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_11, x_78, x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_unsigned_to_nat(0u);
x_81 = l_Lean_Syntax_getArg(x_10, x_80);
lean_dec(x_10);
x_82 = l_Lean_Name_toString___closed__1;
x_83 = l_Lean_Name_toStringWithSep___main(x_82, x_11);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_4);
x_90 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_81, x_89, x_4, x_75);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_3, x_92);
lean_dec(x_3);
x_3 = x_93;
x_5 = x_91;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_11);
lean_dec(x_10);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_3, x_99);
lean_dec(x_3);
x_3 = x_100;
x_5 = x_75;
goto _start;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_11);
lean_dec(x_10);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_add(x_3, x_102);
lean_dec(x_3);
x_3 = x_103;
x_5 = x_75;
goto _start;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_74, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_74, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_107 = x_74;
} else {
 lean_dec_ref(x_74);
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
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_2, x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is not an inductive type ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_whnf(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_18 = l_Lean_Expr_getAppFn___main(x_7);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_environment_find(x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_free_object(x_5);
x_22 = lean_box(0);
x_9 = x_22;
goto block_17;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
else
{
lean_object* x_25; 
lean_dec(x_23);
lean_free_object(x_5);
x_25 = lean_box(0);
x_9 = x_25;
goto block_17;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_18);
lean_free_object(x_5);
x_26 = lean_box(0);
x_9 = x_26;
goto block_17;
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = l_Lean_indentExpr(x_10);
x_12 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_1, x_13, x_15, x_3, x_8);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_38; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_38 = l_Lean_Expr_getAppFn___main(x_27);
if (lean_obj_tag(x_38) == 4)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
x_41 = lean_environment_find(x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_29 = x_42;
goto block_37;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
if (lean_obj_tag(x_43) == 5)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_28);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_43);
x_46 = lean_box(0);
x_29 = x_46;
goto block_37;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_38);
x_47 = lean_box(0);
x_29 = x_47;
goto block_37;
}
block_37:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = l_Lean_indentExpr(x_30);
x_32 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_35 = lean_box(0);
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_34, x_1, x_33, x_35, x_3, x_28);
lean_dec(x_3);
return x_36;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
return x_5;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_5);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_inferType), 3, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1), 4, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_7, x_11, x_2, x_6);
lean_dec(x_7);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Tactic_whnfCore(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Expr_getAppFn___main(x_6);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_8);
lean_inc(x_3);
x_9 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 4);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_nat_dec_eq(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
if (x_94 == 0)
{
x_19 = x_17;
goto block_89;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_96 = l_Lean_Elab_Tactic_throwError___rarg(x_95, x_3, x_17);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_19 = x_97;
goto block_89;
}
else
{
uint8_t x_98; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_96);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_89:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_3, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
lean_ctor_set(x_21, 3, x_29);
x_2 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 2);
x_34 = lean_ctor_get(x_21, 3);
x_35 = lean_ctor_get(x_21, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_34, x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_20, 0, x_38);
x_2 = x_18;
x_4 = x_19;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_40 = lean_ctor_get(x_20, 1);
x_41 = lean_ctor_get(x_20, 2);
x_42 = lean_ctor_get(x_20, 3);
x_43 = lean_ctor_get(x_20, 4);
x_44 = lean_ctor_get(x_20, 5);
x_45 = lean_ctor_get(x_20, 6);
x_46 = lean_ctor_get(x_20, 7);
x_47 = lean_ctor_get(x_20, 8);
x_48 = lean_ctor_get_uint8(x_20, sizeof(void*)*10);
x_49 = lean_ctor_get_uint8(x_20, sizeof(void*)*10 + 1);
x_50 = lean_ctor_get_uint8(x_20, sizeof(void*)*10 + 2);
x_51 = lean_ctor_get(x_20, 9);
lean_inc(x_51);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_52 = lean_ctor_get(x_21, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_21, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_21, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 x_57 = x_21;
} else {
 lean_dec_ref(x_21);
 x_57 = lean_box(0);
}
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_55, x_58);
lean_dec(x_55);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_56);
x_61 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_40);
lean_ctor_set(x_61, 2, x_41);
lean_ctor_set(x_61, 3, x_42);
lean_ctor_set(x_61, 4, x_43);
lean_ctor_set(x_61, 5, x_44);
lean_ctor_set(x_61, 6, x_45);
lean_ctor_set(x_61, 7, x_46);
lean_ctor_set(x_61, 8, x_47);
lean_ctor_set(x_61, 9, x_51);
lean_ctor_set_uint8(x_61, sizeof(void*)*10, x_48);
lean_ctor_set_uint8(x_61, sizeof(void*)*10 + 1, x_49);
lean_ctor_set_uint8(x_61, sizeof(void*)*10 + 2, x_50);
lean_ctor_set(x_3, 0, x_61);
x_2 = x_18;
x_4 = x_19;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
lean_dec(x_3);
x_64 = lean_ctor_get(x_20, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_20, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_20, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_20, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_20, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_20, 6);
lean_inc(x_69);
x_70 = lean_ctor_get(x_20, 7);
lean_inc(x_70);
x_71 = lean_ctor_get(x_20, 8);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_20, sizeof(void*)*10);
x_73 = lean_ctor_get_uint8(x_20, sizeof(void*)*10 + 1);
x_74 = lean_ctor_get_uint8(x_20, sizeof(void*)*10 + 2);
x_75 = lean_ctor_get(x_20, 9);
lean_inc(x_75);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 lean_ctor_release(x_20, 6);
 lean_ctor_release(x_20, 7);
 lean_ctor_release(x_20, 8);
 lean_ctor_release(x_20, 9);
 x_76 = x_20;
} else {
 lean_dec_ref(x_20);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_21, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_21, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_21, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_21, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_21, 4);
lean_inc(x_81);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 x_82 = x_21;
} else {
 lean_dec_ref(x_21);
 x_82 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_80, x_83);
lean_dec(x_80);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_81);
if (lean_is_scalar(x_76)) {
 x_86 = lean_alloc_ctor(0, 10, 3);
} else {
 x_86 = x_76;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_64);
lean_ctor_set(x_86, 2, x_65);
lean_ctor_set(x_86, 3, x_66);
lean_ctor_set(x_86, 4, x_67);
lean_ctor_set(x_86, 5, x_68);
lean_ctor_set(x_86, 6, x_69);
lean_ctor_set(x_86, 7, x_70);
lean_ctor_set(x_86, 8, x_71);
lean_ctor_set(x_86, 9, x_75);
lean_ctor_set_uint8(x_86, sizeof(void*)*10, x_72);
lean_ctor_set_uint8(x_86, sizeof(void*)*10 + 1, x_73);
lean_ctor_set_uint8(x_86, sizeof(void*)*10 + 2, x_74);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_63);
x_2 = x_18;
x_3 = x_87;
x_4 = x_19;
goto _start;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_9);
if (x_102 == 0)
{
return x_9;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_9, 0);
x_104 = lean_ctor_get(x_9, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_9);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
case 1:
{
lean_object* x_106; 
lean_dec(x_8);
lean_inc(x_3);
x_106 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_dec(x_106);
x_115 = lean_ctor_get(x_107, 0);
lean_inc(x_115);
lean_dec(x_107);
x_187 = lean_ctor_get(x_3, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_ctor_get(x_188, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 4);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_nat_dec_eq(x_189, x_190);
lean_dec(x_190);
lean_dec(x_189);
if (x_191 == 0)
{
x_116 = x_114;
goto block_186;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_193 = l_Lean_Elab_Tactic_throwError___rarg(x_192, x_3, x_114);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_116 = x_194;
goto block_186;
}
else
{
uint8_t x_195; 
lean_dec(x_115);
lean_dec(x_3);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
return x_193;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_193, 0);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_193);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
block_186:
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_3, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = !lean_is_exclusive(x_3);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_3, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_117);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_117, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_118);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_118, 3);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_124, x_125);
lean_dec(x_124);
lean_ctor_set(x_118, 3, x_126);
x_2 = x_115;
x_4 = x_116;
goto _start;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_128 = lean_ctor_get(x_118, 0);
x_129 = lean_ctor_get(x_118, 1);
x_130 = lean_ctor_get(x_118, 2);
x_131 = lean_ctor_get(x_118, 3);
x_132 = lean_ctor_get(x_118, 4);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_118);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_add(x_131, x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_128);
lean_ctor_set(x_135, 1, x_129);
lean_ctor_set(x_135, 2, x_130);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_132);
lean_ctor_set(x_117, 0, x_135);
x_2 = x_115;
x_4 = x_116;
goto _start;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_137 = lean_ctor_get(x_117, 1);
x_138 = lean_ctor_get(x_117, 2);
x_139 = lean_ctor_get(x_117, 3);
x_140 = lean_ctor_get(x_117, 4);
x_141 = lean_ctor_get(x_117, 5);
x_142 = lean_ctor_get(x_117, 6);
x_143 = lean_ctor_get(x_117, 7);
x_144 = lean_ctor_get(x_117, 8);
x_145 = lean_ctor_get_uint8(x_117, sizeof(void*)*10);
x_146 = lean_ctor_get_uint8(x_117, sizeof(void*)*10 + 1);
x_147 = lean_ctor_get_uint8(x_117, sizeof(void*)*10 + 2);
x_148 = lean_ctor_get(x_117, 9);
lean_inc(x_148);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_117);
x_149 = lean_ctor_get(x_118, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_118, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_118, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_118, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_118, 4);
lean_inc(x_153);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_154 = x_118;
} else {
 lean_dec_ref(x_118);
 x_154 = lean_box(0);
}
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_add(x_152, x_155);
lean_dec(x_152);
if (lean_is_scalar(x_154)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_154;
}
lean_ctor_set(x_157, 0, x_149);
lean_ctor_set(x_157, 1, x_150);
lean_ctor_set(x_157, 2, x_151);
lean_ctor_set(x_157, 3, x_156);
lean_ctor_set(x_157, 4, x_153);
x_158 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_137);
lean_ctor_set(x_158, 2, x_138);
lean_ctor_set(x_158, 3, x_139);
lean_ctor_set(x_158, 4, x_140);
lean_ctor_set(x_158, 5, x_141);
lean_ctor_set(x_158, 6, x_142);
lean_ctor_set(x_158, 7, x_143);
lean_ctor_set(x_158, 8, x_144);
lean_ctor_set(x_158, 9, x_148);
lean_ctor_set_uint8(x_158, sizeof(void*)*10, x_145);
lean_ctor_set_uint8(x_158, sizeof(void*)*10 + 1, x_146);
lean_ctor_set_uint8(x_158, sizeof(void*)*10 + 2, x_147);
lean_ctor_set(x_3, 0, x_158);
x_2 = x_115;
x_4 = x_116;
goto _start;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_160 = lean_ctor_get(x_3, 1);
lean_inc(x_160);
lean_dec(x_3);
x_161 = lean_ctor_get(x_117, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_117, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_117, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_117, 4);
lean_inc(x_164);
x_165 = lean_ctor_get(x_117, 5);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 6);
lean_inc(x_166);
x_167 = lean_ctor_get(x_117, 7);
lean_inc(x_167);
x_168 = lean_ctor_get(x_117, 8);
lean_inc(x_168);
x_169 = lean_ctor_get_uint8(x_117, sizeof(void*)*10);
x_170 = lean_ctor_get_uint8(x_117, sizeof(void*)*10 + 1);
x_171 = lean_ctor_get_uint8(x_117, sizeof(void*)*10 + 2);
x_172 = lean_ctor_get(x_117, 9);
lean_inc(x_172);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 lean_ctor_release(x_117, 6);
 lean_ctor_release(x_117, 7);
 lean_ctor_release(x_117, 8);
 lean_ctor_release(x_117, 9);
 x_173 = x_117;
} else {
 lean_dec_ref(x_117);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_118, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_118, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_118, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_118, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_118, 4);
lean_inc(x_178);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_179 = x_118;
} else {
 lean_dec_ref(x_118);
 x_179 = lean_box(0);
}
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_nat_add(x_177, x_180);
lean_dec(x_177);
if (lean_is_scalar(x_179)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_179;
}
lean_ctor_set(x_182, 0, x_174);
lean_ctor_set(x_182, 1, x_175);
lean_ctor_set(x_182, 2, x_176);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set(x_182, 4, x_178);
if (lean_is_scalar(x_173)) {
 x_183 = lean_alloc_ctor(0, 10, 3);
} else {
 x_183 = x_173;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_161);
lean_ctor_set(x_183, 2, x_162);
lean_ctor_set(x_183, 3, x_163);
lean_ctor_set(x_183, 4, x_164);
lean_ctor_set(x_183, 5, x_165);
lean_ctor_set(x_183, 6, x_166);
lean_ctor_set(x_183, 7, x_167);
lean_ctor_set(x_183, 8, x_168);
lean_ctor_set(x_183, 9, x_172);
lean_ctor_set_uint8(x_183, sizeof(void*)*10, x_169);
lean_ctor_set_uint8(x_183, sizeof(void*)*10 + 1, x_170);
lean_ctor_set_uint8(x_183, sizeof(void*)*10 + 2, x_171);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_160);
x_2 = x_115;
x_3 = x_184;
x_4 = x_116;
goto _start;
}
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_3);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_106);
if (x_199 == 0)
{
return x_106;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_106, 0);
x_201 = lean_ctor_get(x_106, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_106);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
case 2:
{
lean_object* x_203; 
lean_dec(x_8);
lean_inc(x_3);
x_203 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
lean_dec(x_3);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_203, 0);
lean_dec(x_206);
x_207 = lean_box(0);
lean_ctor_set(x_203, 0, x_207);
return x_203;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_dec(x_203);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_211 = lean_ctor_get(x_203, 1);
lean_inc(x_211);
lean_dec(x_203);
x_212 = lean_ctor_get(x_204, 0);
lean_inc(x_212);
lean_dec(x_204);
x_284 = lean_ctor_get(x_3, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_ctor_get(x_285, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 4);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_nat_dec_eq(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
if (x_288 == 0)
{
x_213 = x_211;
goto block_283;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_290 = l_Lean_Elab_Tactic_throwError___rarg(x_289, x_3, x_211);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_213 = x_291;
goto block_283;
}
else
{
uint8_t x_292; 
lean_dec(x_212);
lean_dec(x_3);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_290);
if (x_292 == 0)
{
return x_290;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_290, 0);
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_290);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
block_283:
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_3, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = !lean_is_exclusive(x_3);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; 
x_217 = lean_ctor_get(x_3, 0);
lean_dec(x_217);
x_218 = !lean_is_exclusive(x_214);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_214, 0);
lean_dec(x_219);
x_220 = !lean_is_exclusive(x_215);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_215, 3);
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_221);
lean_ctor_set(x_215, 3, x_223);
x_2 = x_212;
x_4 = x_213;
goto _start;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_215, 0);
x_226 = lean_ctor_get(x_215, 1);
x_227 = lean_ctor_get(x_215, 2);
x_228 = lean_ctor_get(x_215, 3);
x_229 = lean_ctor_get(x_215, 4);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_215);
x_230 = lean_unsigned_to_nat(1u);
x_231 = lean_nat_add(x_228, x_230);
lean_dec(x_228);
x_232 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_231);
lean_ctor_set(x_232, 4, x_229);
lean_ctor_set(x_214, 0, x_232);
x_2 = x_212;
x_4 = x_213;
goto _start;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_234 = lean_ctor_get(x_214, 1);
x_235 = lean_ctor_get(x_214, 2);
x_236 = lean_ctor_get(x_214, 3);
x_237 = lean_ctor_get(x_214, 4);
x_238 = lean_ctor_get(x_214, 5);
x_239 = lean_ctor_get(x_214, 6);
x_240 = lean_ctor_get(x_214, 7);
x_241 = lean_ctor_get(x_214, 8);
x_242 = lean_ctor_get_uint8(x_214, sizeof(void*)*10);
x_243 = lean_ctor_get_uint8(x_214, sizeof(void*)*10 + 1);
x_244 = lean_ctor_get_uint8(x_214, sizeof(void*)*10 + 2);
x_245 = lean_ctor_get(x_214, 9);
lean_inc(x_245);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_214);
x_246 = lean_ctor_get(x_215, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_215, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_215, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_215, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_215, 4);
lean_inc(x_250);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 lean_ctor_release(x_215, 4);
 x_251 = x_215;
} else {
 lean_dec_ref(x_215);
 x_251 = lean_box(0);
}
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_add(x_249, x_252);
lean_dec(x_249);
if (lean_is_scalar(x_251)) {
 x_254 = lean_alloc_ctor(0, 5, 0);
} else {
 x_254 = x_251;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_247);
lean_ctor_set(x_254, 2, x_248);
lean_ctor_set(x_254, 3, x_253);
lean_ctor_set(x_254, 4, x_250);
x_255 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_234);
lean_ctor_set(x_255, 2, x_235);
lean_ctor_set(x_255, 3, x_236);
lean_ctor_set(x_255, 4, x_237);
lean_ctor_set(x_255, 5, x_238);
lean_ctor_set(x_255, 6, x_239);
lean_ctor_set(x_255, 7, x_240);
lean_ctor_set(x_255, 8, x_241);
lean_ctor_set(x_255, 9, x_245);
lean_ctor_set_uint8(x_255, sizeof(void*)*10, x_242);
lean_ctor_set_uint8(x_255, sizeof(void*)*10 + 1, x_243);
lean_ctor_set_uint8(x_255, sizeof(void*)*10 + 2, x_244);
lean_ctor_set(x_3, 0, x_255);
x_2 = x_212;
x_4 = x_213;
goto _start;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_257 = lean_ctor_get(x_3, 1);
lean_inc(x_257);
lean_dec(x_3);
x_258 = lean_ctor_get(x_214, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_214, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_214, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_214, 4);
lean_inc(x_261);
x_262 = lean_ctor_get(x_214, 5);
lean_inc(x_262);
x_263 = lean_ctor_get(x_214, 6);
lean_inc(x_263);
x_264 = lean_ctor_get(x_214, 7);
lean_inc(x_264);
x_265 = lean_ctor_get(x_214, 8);
lean_inc(x_265);
x_266 = lean_ctor_get_uint8(x_214, sizeof(void*)*10);
x_267 = lean_ctor_get_uint8(x_214, sizeof(void*)*10 + 1);
x_268 = lean_ctor_get_uint8(x_214, sizeof(void*)*10 + 2);
x_269 = lean_ctor_get(x_214, 9);
lean_inc(x_269);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 lean_ctor_release(x_214, 5);
 lean_ctor_release(x_214, 6);
 lean_ctor_release(x_214, 7);
 lean_ctor_release(x_214, 8);
 lean_ctor_release(x_214, 9);
 x_270 = x_214;
} else {
 lean_dec_ref(x_214);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_215, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_215, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_215, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_215, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_215, 4);
lean_inc(x_275);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 lean_ctor_release(x_215, 3);
 lean_ctor_release(x_215, 4);
 x_276 = x_215;
} else {
 lean_dec_ref(x_215);
 x_276 = lean_box(0);
}
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_nat_add(x_274, x_277);
lean_dec(x_274);
if (lean_is_scalar(x_276)) {
 x_279 = lean_alloc_ctor(0, 5, 0);
} else {
 x_279 = x_276;
}
lean_ctor_set(x_279, 0, x_271);
lean_ctor_set(x_279, 1, x_272);
lean_ctor_set(x_279, 2, x_273);
lean_ctor_set(x_279, 3, x_278);
lean_ctor_set(x_279, 4, x_275);
if (lean_is_scalar(x_270)) {
 x_280 = lean_alloc_ctor(0, 10, 3);
} else {
 x_280 = x_270;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_258);
lean_ctor_set(x_280, 2, x_259);
lean_ctor_set(x_280, 3, x_260);
lean_ctor_set(x_280, 4, x_261);
lean_ctor_set(x_280, 5, x_262);
lean_ctor_set(x_280, 6, x_263);
lean_ctor_set(x_280, 7, x_264);
lean_ctor_set(x_280, 8, x_265);
lean_ctor_set(x_280, 9, x_269);
lean_ctor_set_uint8(x_280, sizeof(void*)*10, x_266);
lean_ctor_set_uint8(x_280, sizeof(void*)*10 + 1, x_267);
lean_ctor_set_uint8(x_280, sizeof(void*)*10 + 2, x_268);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_257);
x_2 = x_212;
x_3 = x_281;
x_4 = x_213;
goto _start;
}
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_3);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_203);
if (x_296 == 0)
{
return x_203;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_203, 0);
x_298 = lean_ctor_get(x_203, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_203);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
case 3:
{
lean_object* x_300; 
lean_dec(x_8);
lean_inc(x_3);
x_300 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
lean_dec(x_3);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_300);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_300, 0);
lean_dec(x_303);
x_304 = lean_box(0);
lean_ctor_set(x_300, 0, x_304);
return x_300;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
lean_dec(x_300);
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_308 = lean_ctor_get(x_300, 1);
lean_inc(x_308);
lean_dec(x_300);
x_309 = lean_ctor_get(x_301, 0);
lean_inc(x_309);
lean_dec(x_301);
x_381 = lean_ctor_get(x_3, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec(x_381);
x_383 = lean_ctor_get(x_382, 3);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 4);
lean_inc(x_384);
lean_dec(x_382);
x_385 = lean_nat_dec_eq(x_383, x_384);
lean_dec(x_384);
lean_dec(x_383);
if (x_385 == 0)
{
x_310 = x_308;
goto block_380;
}
else
{
lean_object* x_386; lean_object* x_387; 
x_386 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_387 = l_Lean_Elab_Tactic_throwError___rarg(x_386, x_3, x_308);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_310 = x_388;
goto block_380;
}
else
{
uint8_t x_389; 
lean_dec(x_309);
lean_dec(x_3);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_387);
if (x_389 == 0)
{
return x_387;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_387, 0);
x_391 = lean_ctor_get(x_387, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_387);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
block_380:
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_ctor_get(x_3, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = !lean_is_exclusive(x_3);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_3, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_311);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_311, 0);
lean_dec(x_316);
x_317 = !lean_is_exclusive(x_312);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_312, 3);
x_319 = lean_unsigned_to_nat(1u);
x_320 = lean_nat_add(x_318, x_319);
lean_dec(x_318);
lean_ctor_set(x_312, 3, x_320);
x_2 = x_309;
x_4 = x_310;
goto _start;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_322 = lean_ctor_get(x_312, 0);
x_323 = lean_ctor_get(x_312, 1);
x_324 = lean_ctor_get(x_312, 2);
x_325 = lean_ctor_get(x_312, 3);
x_326 = lean_ctor_get(x_312, 4);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_312);
x_327 = lean_unsigned_to_nat(1u);
x_328 = lean_nat_add(x_325, x_327);
lean_dec(x_325);
x_329 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_323);
lean_ctor_set(x_329, 2, x_324);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set(x_329, 4, x_326);
lean_ctor_set(x_311, 0, x_329);
x_2 = x_309;
x_4 = x_310;
goto _start;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_331 = lean_ctor_get(x_311, 1);
x_332 = lean_ctor_get(x_311, 2);
x_333 = lean_ctor_get(x_311, 3);
x_334 = lean_ctor_get(x_311, 4);
x_335 = lean_ctor_get(x_311, 5);
x_336 = lean_ctor_get(x_311, 6);
x_337 = lean_ctor_get(x_311, 7);
x_338 = lean_ctor_get(x_311, 8);
x_339 = lean_ctor_get_uint8(x_311, sizeof(void*)*10);
x_340 = lean_ctor_get_uint8(x_311, sizeof(void*)*10 + 1);
x_341 = lean_ctor_get_uint8(x_311, sizeof(void*)*10 + 2);
x_342 = lean_ctor_get(x_311, 9);
lean_inc(x_342);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_311);
x_343 = lean_ctor_get(x_312, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_312, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_312, 2);
lean_inc(x_345);
x_346 = lean_ctor_get(x_312, 3);
lean_inc(x_346);
x_347 = lean_ctor_get(x_312, 4);
lean_inc(x_347);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 x_348 = x_312;
} else {
 lean_dec_ref(x_312);
 x_348 = lean_box(0);
}
x_349 = lean_unsigned_to_nat(1u);
x_350 = lean_nat_add(x_346, x_349);
lean_dec(x_346);
if (lean_is_scalar(x_348)) {
 x_351 = lean_alloc_ctor(0, 5, 0);
} else {
 x_351 = x_348;
}
lean_ctor_set(x_351, 0, x_343);
lean_ctor_set(x_351, 1, x_344);
lean_ctor_set(x_351, 2, x_345);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set(x_351, 4, x_347);
x_352 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_331);
lean_ctor_set(x_352, 2, x_332);
lean_ctor_set(x_352, 3, x_333);
lean_ctor_set(x_352, 4, x_334);
lean_ctor_set(x_352, 5, x_335);
lean_ctor_set(x_352, 6, x_336);
lean_ctor_set(x_352, 7, x_337);
lean_ctor_set(x_352, 8, x_338);
lean_ctor_set(x_352, 9, x_342);
lean_ctor_set_uint8(x_352, sizeof(void*)*10, x_339);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 1, x_340);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 2, x_341);
lean_ctor_set(x_3, 0, x_352);
x_2 = x_309;
x_4 = x_310;
goto _start;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_354 = lean_ctor_get(x_3, 1);
lean_inc(x_354);
lean_dec(x_3);
x_355 = lean_ctor_get(x_311, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_311, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_311, 3);
lean_inc(x_357);
x_358 = lean_ctor_get(x_311, 4);
lean_inc(x_358);
x_359 = lean_ctor_get(x_311, 5);
lean_inc(x_359);
x_360 = lean_ctor_get(x_311, 6);
lean_inc(x_360);
x_361 = lean_ctor_get(x_311, 7);
lean_inc(x_361);
x_362 = lean_ctor_get(x_311, 8);
lean_inc(x_362);
x_363 = lean_ctor_get_uint8(x_311, sizeof(void*)*10);
x_364 = lean_ctor_get_uint8(x_311, sizeof(void*)*10 + 1);
x_365 = lean_ctor_get_uint8(x_311, sizeof(void*)*10 + 2);
x_366 = lean_ctor_get(x_311, 9);
lean_inc(x_366);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 lean_ctor_release(x_311, 2);
 lean_ctor_release(x_311, 3);
 lean_ctor_release(x_311, 4);
 lean_ctor_release(x_311, 5);
 lean_ctor_release(x_311, 6);
 lean_ctor_release(x_311, 7);
 lean_ctor_release(x_311, 8);
 lean_ctor_release(x_311, 9);
 x_367 = x_311;
} else {
 lean_dec_ref(x_311);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_312, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_312, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_312, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_312, 3);
lean_inc(x_371);
x_372 = lean_ctor_get(x_312, 4);
lean_inc(x_372);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 x_373 = x_312;
} else {
 lean_dec_ref(x_312);
 x_373 = lean_box(0);
}
x_374 = lean_unsigned_to_nat(1u);
x_375 = lean_nat_add(x_371, x_374);
lean_dec(x_371);
if (lean_is_scalar(x_373)) {
 x_376 = lean_alloc_ctor(0, 5, 0);
} else {
 x_376 = x_373;
}
lean_ctor_set(x_376, 0, x_368);
lean_ctor_set(x_376, 1, x_369);
lean_ctor_set(x_376, 2, x_370);
lean_ctor_set(x_376, 3, x_375);
lean_ctor_set(x_376, 4, x_372);
if (lean_is_scalar(x_367)) {
 x_377 = lean_alloc_ctor(0, 10, 3);
} else {
 x_377 = x_367;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_355);
lean_ctor_set(x_377, 2, x_356);
lean_ctor_set(x_377, 3, x_357);
lean_ctor_set(x_377, 4, x_358);
lean_ctor_set(x_377, 5, x_359);
lean_ctor_set(x_377, 6, x_360);
lean_ctor_set(x_377, 7, x_361);
lean_ctor_set(x_377, 8, x_362);
lean_ctor_set(x_377, 9, x_366);
lean_ctor_set_uint8(x_377, sizeof(void*)*10, x_363);
lean_ctor_set_uint8(x_377, sizeof(void*)*10 + 1, x_364);
lean_ctor_set_uint8(x_377, sizeof(void*)*10 + 2, x_365);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_354);
x_2 = x_309;
x_3 = x_378;
x_4 = x_310;
goto _start;
}
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_3);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_300);
if (x_393 == 0)
{
return x_300;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_300, 0);
x_395 = lean_ctor_get(x_300, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_300);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
case 4:
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_8, 0);
lean_inc(x_397);
lean_dec(x_8);
lean_inc(x_1);
x_398 = l_Lean_Name_append___main(x_397, x_1);
lean_dec(x_397);
x_399 = l_Lean_Elab_Tactic_getEnv___rarg(x_7);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
lean_inc(x_398);
x_402 = lean_environment_find(x_400, x_398);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
lean_dec(x_398);
lean_inc(x_3);
x_403 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_401);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
uint8_t x_405; 
lean_dec(x_3);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_403);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_403, 0);
lean_dec(x_406);
x_407 = lean_box(0);
lean_ctor_set(x_403, 0, x_407);
return x_403;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_403, 1);
lean_inc(x_408);
lean_dec(x_403);
x_409 = lean_box(0);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_411 = lean_ctor_get(x_403, 1);
lean_inc(x_411);
lean_dec(x_403);
x_412 = lean_ctor_get(x_404, 0);
lean_inc(x_412);
lean_dec(x_404);
x_484 = lean_ctor_get(x_3, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
lean_dec(x_484);
x_486 = lean_ctor_get(x_485, 3);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 4);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_nat_dec_eq(x_486, x_487);
lean_dec(x_487);
lean_dec(x_486);
if (x_488 == 0)
{
x_413 = x_411;
goto block_483;
}
else
{
lean_object* x_489; lean_object* x_490; 
x_489 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_490 = l_Lean_Elab_Tactic_throwError___rarg(x_489, x_3, x_411);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; 
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
lean_dec(x_490);
x_413 = x_491;
goto block_483;
}
else
{
uint8_t x_492; 
lean_dec(x_412);
lean_dec(x_3);
lean_dec(x_1);
x_492 = !lean_is_exclusive(x_490);
if (x_492 == 0)
{
return x_490;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_490, 0);
x_494 = lean_ctor_get(x_490, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_490);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
block_483:
{
lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_414 = lean_ctor_get(x_3, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = !lean_is_exclusive(x_3);
if (x_416 == 0)
{
lean_object* x_417; uint8_t x_418; 
x_417 = lean_ctor_get(x_3, 0);
lean_dec(x_417);
x_418 = !lean_is_exclusive(x_414);
if (x_418 == 0)
{
lean_object* x_419; uint8_t x_420; 
x_419 = lean_ctor_get(x_414, 0);
lean_dec(x_419);
x_420 = !lean_is_exclusive(x_415);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_415, 3);
x_422 = lean_unsigned_to_nat(1u);
x_423 = lean_nat_add(x_421, x_422);
lean_dec(x_421);
lean_ctor_set(x_415, 3, x_423);
x_2 = x_412;
x_4 = x_413;
goto _start;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_425 = lean_ctor_get(x_415, 0);
x_426 = lean_ctor_get(x_415, 1);
x_427 = lean_ctor_get(x_415, 2);
x_428 = lean_ctor_get(x_415, 3);
x_429 = lean_ctor_get(x_415, 4);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_415);
x_430 = lean_unsigned_to_nat(1u);
x_431 = lean_nat_add(x_428, x_430);
lean_dec(x_428);
x_432 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_432, 0, x_425);
lean_ctor_set(x_432, 1, x_426);
lean_ctor_set(x_432, 2, x_427);
lean_ctor_set(x_432, 3, x_431);
lean_ctor_set(x_432, 4, x_429);
lean_ctor_set(x_414, 0, x_432);
x_2 = x_412;
x_4 = x_413;
goto _start;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_434 = lean_ctor_get(x_414, 1);
x_435 = lean_ctor_get(x_414, 2);
x_436 = lean_ctor_get(x_414, 3);
x_437 = lean_ctor_get(x_414, 4);
x_438 = lean_ctor_get(x_414, 5);
x_439 = lean_ctor_get(x_414, 6);
x_440 = lean_ctor_get(x_414, 7);
x_441 = lean_ctor_get(x_414, 8);
x_442 = lean_ctor_get_uint8(x_414, sizeof(void*)*10);
x_443 = lean_ctor_get_uint8(x_414, sizeof(void*)*10 + 1);
x_444 = lean_ctor_get_uint8(x_414, sizeof(void*)*10 + 2);
x_445 = lean_ctor_get(x_414, 9);
lean_inc(x_445);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_414);
x_446 = lean_ctor_get(x_415, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_415, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_415, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_415, 3);
lean_inc(x_449);
x_450 = lean_ctor_get(x_415, 4);
lean_inc(x_450);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 lean_ctor_release(x_415, 4);
 x_451 = x_415;
} else {
 lean_dec_ref(x_415);
 x_451 = lean_box(0);
}
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_nat_add(x_449, x_452);
lean_dec(x_449);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 5, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_446);
lean_ctor_set(x_454, 1, x_447);
lean_ctor_set(x_454, 2, x_448);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set(x_454, 4, x_450);
x_455 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_434);
lean_ctor_set(x_455, 2, x_435);
lean_ctor_set(x_455, 3, x_436);
lean_ctor_set(x_455, 4, x_437);
lean_ctor_set(x_455, 5, x_438);
lean_ctor_set(x_455, 6, x_439);
lean_ctor_set(x_455, 7, x_440);
lean_ctor_set(x_455, 8, x_441);
lean_ctor_set(x_455, 9, x_445);
lean_ctor_set_uint8(x_455, sizeof(void*)*10, x_442);
lean_ctor_set_uint8(x_455, sizeof(void*)*10 + 1, x_443);
lean_ctor_set_uint8(x_455, sizeof(void*)*10 + 2, x_444);
lean_ctor_set(x_3, 0, x_455);
x_2 = x_412;
x_4 = x_413;
goto _start;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_457 = lean_ctor_get(x_3, 1);
lean_inc(x_457);
lean_dec(x_3);
x_458 = lean_ctor_get(x_414, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_414, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_414, 3);
lean_inc(x_460);
x_461 = lean_ctor_get(x_414, 4);
lean_inc(x_461);
x_462 = lean_ctor_get(x_414, 5);
lean_inc(x_462);
x_463 = lean_ctor_get(x_414, 6);
lean_inc(x_463);
x_464 = lean_ctor_get(x_414, 7);
lean_inc(x_464);
x_465 = lean_ctor_get(x_414, 8);
lean_inc(x_465);
x_466 = lean_ctor_get_uint8(x_414, sizeof(void*)*10);
x_467 = lean_ctor_get_uint8(x_414, sizeof(void*)*10 + 1);
x_468 = lean_ctor_get_uint8(x_414, sizeof(void*)*10 + 2);
x_469 = lean_ctor_get(x_414, 9);
lean_inc(x_469);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 lean_ctor_release(x_414, 4);
 lean_ctor_release(x_414, 5);
 lean_ctor_release(x_414, 6);
 lean_ctor_release(x_414, 7);
 lean_ctor_release(x_414, 8);
 lean_ctor_release(x_414, 9);
 x_470 = x_414;
} else {
 lean_dec_ref(x_414);
 x_470 = lean_box(0);
}
x_471 = lean_ctor_get(x_415, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_415, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_415, 2);
lean_inc(x_473);
x_474 = lean_ctor_get(x_415, 3);
lean_inc(x_474);
x_475 = lean_ctor_get(x_415, 4);
lean_inc(x_475);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 lean_ctor_release(x_415, 4);
 x_476 = x_415;
} else {
 lean_dec_ref(x_415);
 x_476 = lean_box(0);
}
x_477 = lean_unsigned_to_nat(1u);
x_478 = lean_nat_add(x_474, x_477);
lean_dec(x_474);
if (lean_is_scalar(x_476)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_476;
}
lean_ctor_set(x_479, 0, x_471);
lean_ctor_set(x_479, 1, x_472);
lean_ctor_set(x_479, 2, x_473);
lean_ctor_set(x_479, 3, x_478);
lean_ctor_set(x_479, 4, x_475);
if (lean_is_scalar(x_470)) {
 x_480 = lean_alloc_ctor(0, 10, 3);
} else {
 x_480 = x_470;
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_458);
lean_ctor_set(x_480, 2, x_459);
lean_ctor_set(x_480, 3, x_460);
lean_ctor_set(x_480, 4, x_461);
lean_ctor_set(x_480, 5, x_462);
lean_ctor_set(x_480, 6, x_463);
lean_ctor_set(x_480, 7, x_464);
lean_ctor_set(x_480, 8, x_465);
lean_ctor_set(x_480, 9, x_469);
lean_ctor_set_uint8(x_480, sizeof(void*)*10, x_466);
lean_ctor_set_uint8(x_480, sizeof(void*)*10 + 1, x_467);
lean_ctor_set_uint8(x_480, sizeof(void*)*10 + 2, x_468);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_457);
x_2 = x_412;
x_3 = x_481;
x_4 = x_413;
goto _start;
}
}
}
}
else
{
uint8_t x_496; 
lean_dec(x_3);
lean_dec(x_1);
x_496 = !lean_is_exclusive(x_403);
if (x_496 == 0)
{
return x_403;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_403, 0);
x_498 = lean_ctor_get(x_403, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_403);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_601; 
lean_dec(x_402);
x_500 = l_Lean_Elab_Tactic_save(x_401);
lean_inc(x_3);
x_601 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_401);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_602, 0);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_box(0);
x_606 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_606, 0, x_398);
lean_closure_set(x_606, 1, x_605);
x_607 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_608 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_608, 0, x_606);
lean_closure_set(x_608, 1, x_607);
x_609 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_609, 0, x_608);
lean_inc(x_3);
x_610 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_604, x_609, x_3, x_603);
lean_dec(x_604);
if (lean_obj_tag(x_610) == 0)
{
lean_dec(x_500);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_610;
}
else
{
lean_object* x_611; 
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
lean_dec(x_610);
x_501 = x_611;
goto block_600;
}
}
else
{
lean_object* x_612; 
lean_dec(x_398);
x_612 = lean_ctor_get(x_601, 1);
lean_inc(x_612);
lean_dec(x_601);
x_501 = x_612;
goto block_600;
}
block_600:
{
lean_object* x_502; lean_object* x_503; 
x_502 = l_Lean_Elab_Tactic_restore(x_501, x_500);
lean_dec(x_500);
lean_inc(x_3);
x_503 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_502);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
if (lean_obj_tag(x_504) == 0)
{
uint8_t x_505; 
lean_dec(x_3);
lean_dec(x_1);
x_505 = !lean_is_exclusive(x_503);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_ctor_get(x_503, 0);
lean_dec(x_506);
x_507 = lean_box(0);
lean_ctor_set(x_503, 0, x_507);
return x_503;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_503, 1);
lean_inc(x_508);
lean_dec(x_503);
x_509 = lean_box(0);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
x_511 = lean_ctor_get(x_503, 1);
lean_inc(x_511);
lean_dec(x_503);
x_512 = lean_ctor_get(x_504, 0);
lean_inc(x_512);
lean_dec(x_504);
x_584 = lean_ctor_get(x_3, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
lean_dec(x_584);
x_586 = lean_ctor_get(x_585, 3);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 4);
lean_inc(x_587);
lean_dec(x_585);
x_588 = lean_nat_dec_eq(x_586, x_587);
lean_dec(x_587);
lean_dec(x_586);
if (x_588 == 0)
{
x_513 = x_511;
goto block_583;
}
else
{
lean_object* x_589; lean_object* x_590; 
x_589 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_590 = l_Lean_Elab_Tactic_throwError___rarg(x_589, x_3, x_511);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; 
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
lean_dec(x_590);
x_513 = x_591;
goto block_583;
}
else
{
uint8_t x_592; 
lean_dec(x_512);
lean_dec(x_3);
lean_dec(x_1);
x_592 = !lean_is_exclusive(x_590);
if (x_592 == 0)
{
return x_590;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_590, 0);
x_594 = lean_ctor_get(x_590, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_590);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
return x_595;
}
}
}
block_583:
{
lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_514 = lean_ctor_get(x_3, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = !lean_is_exclusive(x_3);
if (x_516 == 0)
{
lean_object* x_517; uint8_t x_518; 
x_517 = lean_ctor_get(x_3, 0);
lean_dec(x_517);
x_518 = !lean_is_exclusive(x_514);
if (x_518 == 0)
{
lean_object* x_519; uint8_t x_520; 
x_519 = lean_ctor_get(x_514, 0);
lean_dec(x_519);
x_520 = !lean_is_exclusive(x_515);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_515, 3);
x_522 = lean_unsigned_to_nat(1u);
x_523 = lean_nat_add(x_521, x_522);
lean_dec(x_521);
lean_ctor_set(x_515, 3, x_523);
x_2 = x_512;
x_4 = x_513;
goto _start;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_525 = lean_ctor_get(x_515, 0);
x_526 = lean_ctor_get(x_515, 1);
x_527 = lean_ctor_get(x_515, 2);
x_528 = lean_ctor_get(x_515, 3);
x_529 = lean_ctor_get(x_515, 4);
lean_inc(x_529);
lean_inc(x_528);
lean_inc(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_515);
x_530 = lean_unsigned_to_nat(1u);
x_531 = lean_nat_add(x_528, x_530);
lean_dec(x_528);
x_532 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_532, 0, x_525);
lean_ctor_set(x_532, 1, x_526);
lean_ctor_set(x_532, 2, x_527);
lean_ctor_set(x_532, 3, x_531);
lean_ctor_set(x_532, 4, x_529);
lean_ctor_set(x_514, 0, x_532);
x_2 = x_512;
x_4 = x_513;
goto _start;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; uint8_t x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_534 = lean_ctor_get(x_514, 1);
x_535 = lean_ctor_get(x_514, 2);
x_536 = lean_ctor_get(x_514, 3);
x_537 = lean_ctor_get(x_514, 4);
x_538 = lean_ctor_get(x_514, 5);
x_539 = lean_ctor_get(x_514, 6);
x_540 = lean_ctor_get(x_514, 7);
x_541 = lean_ctor_get(x_514, 8);
x_542 = lean_ctor_get_uint8(x_514, sizeof(void*)*10);
x_543 = lean_ctor_get_uint8(x_514, sizeof(void*)*10 + 1);
x_544 = lean_ctor_get_uint8(x_514, sizeof(void*)*10 + 2);
x_545 = lean_ctor_get(x_514, 9);
lean_inc(x_545);
lean_inc(x_541);
lean_inc(x_540);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_514);
x_546 = lean_ctor_get(x_515, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_515, 1);
lean_inc(x_547);
x_548 = lean_ctor_get(x_515, 2);
lean_inc(x_548);
x_549 = lean_ctor_get(x_515, 3);
lean_inc(x_549);
x_550 = lean_ctor_get(x_515, 4);
lean_inc(x_550);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 lean_ctor_release(x_515, 2);
 lean_ctor_release(x_515, 3);
 lean_ctor_release(x_515, 4);
 x_551 = x_515;
} else {
 lean_dec_ref(x_515);
 x_551 = lean_box(0);
}
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_nat_add(x_549, x_552);
lean_dec(x_549);
if (lean_is_scalar(x_551)) {
 x_554 = lean_alloc_ctor(0, 5, 0);
} else {
 x_554 = x_551;
}
lean_ctor_set(x_554, 0, x_546);
lean_ctor_set(x_554, 1, x_547);
lean_ctor_set(x_554, 2, x_548);
lean_ctor_set(x_554, 3, x_553);
lean_ctor_set(x_554, 4, x_550);
x_555 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_534);
lean_ctor_set(x_555, 2, x_535);
lean_ctor_set(x_555, 3, x_536);
lean_ctor_set(x_555, 4, x_537);
lean_ctor_set(x_555, 5, x_538);
lean_ctor_set(x_555, 6, x_539);
lean_ctor_set(x_555, 7, x_540);
lean_ctor_set(x_555, 8, x_541);
lean_ctor_set(x_555, 9, x_545);
lean_ctor_set_uint8(x_555, sizeof(void*)*10, x_542);
lean_ctor_set_uint8(x_555, sizeof(void*)*10 + 1, x_543);
lean_ctor_set_uint8(x_555, sizeof(void*)*10 + 2, x_544);
lean_ctor_set(x_3, 0, x_555);
x_2 = x_512;
x_4 = x_513;
goto _start;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; uint8_t x_567; uint8_t x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_557 = lean_ctor_get(x_3, 1);
lean_inc(x_557);
lean_dec(x_3);
x_558 = lean_ctor_get(x_514, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_514, 2);
lean_inc(x_559);
x_560 = lean_ctor_get(x_514, 3);
lean_inc(x_560);
x_561 = lean_ctor_get(x_514, 4);
lean_inc(x_561);
x_562 = lean_ctor_get(x_514, 5);
lean_inc(x_562);
x_563 = lean_ctor_get(x_514, 6);
lean_inc(x_563);
x_564 = lean_ctor_get(x_514, 7);
lean_inc(x_564);
x_565 = lean_ctor_get(x_514, 8);
lean_inc(x_565);
x_566 = lean_ctor_get_uint8(x_514, sizeof(void*)*10);
x_567 = lean_ctor_get_uint8(x_514, sizeof(void*)*10 + 1);
x_568 = lean_ctor_get_uint8(x_514, sizeof(void*)*10 + 2);
x_569 = lean_ctor_get(x_514, 9);
lean_inc(x_569);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 lean_ctor_release(x_514, 2);
 lean_ctor_release(x_514, 3);
 lean_ctor_release(x_514, 4);
 lean_ctor_release(x_514, 5);
 lean_ctor_release(x_514, 6);
 lean_ctor_release(x_514, 7);
 lean_ctor_release(x_514, 8);
 lean_ctor_release(x_514, 9);
 x_570 = x_514;
} else {
 lean_dec_ref(x_514);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_515, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_515, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_515, 2);
lean_inc(x_573);
x_574 = lean_ctor_get(x_515, 3);
lean_inc(x_574);
x_575 = lean_ctor_get(x_515, 4);
lean_inc(x_575);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 lean_ctor_release(x_515, 2);
 lean_ctor_release(x_515, 3);
 lean_ctor_release(x_515, 4);
 x_576 = x_515;
} else {
 lean_dec_ref(x_515);
 x_576 = lean_box(0);
}
x_577 = lean_unsigned_to_nat(1u);
x_578 = lean_nat_add(x_574, x_577);
lean_dec(x_574);
if (lean_is_scalar(x_576)) {
 x_579 = lean_alloc_ctor(0, 5, 0);
} else {
 x_579 = x_576;
}
lean_ctor_set(x_579, 0, x_571);
lean_ctor_set(x_579, 1, x_572);
lean_ctor_set(x_579, 2, x_573);
lean_ctor_set(x_579, 3, x_578);
lean_ctor_set(x_579, 4, x_575);
if (lean_is_scalar(x_570)) {
 x_580 = lean_alloc_ctor(0, 10, 3);
} else {
 x_580 = x_570;
}
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_558);
lean_ctor_set(x_580, 2, x_559);
lean_ctor_set(x_580, 3, x_560);
lean_ctor_set(x_580, 4, x_561);
lean_ctor_set(x_580, 5, x_562);
lean_ctor_set(x_580, 6, x_563);
lean_ctor_set(x_580, 7, x_564);
lean_ctor_set(x_580, 8, x_565);
lean_ctor_set(x_580, 9, x_569);
lean_ctor_set_uint8(x_580, sizeof(void*)*10, x_566);
lean_ctor_set_uint8(x_580, sizeof(void*)*10 + 1, x_567);
lean_ctor_set_uint8(x_580, sizeof(void*)*10 + 2, x_568);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_557);
x_2 = x_512;
x_3 = x_581;
x_4 = x_513;
goto _start;
}
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_3);
lean_dec(x_1);
x_596 = !lean_is_exclusive(x_503);
if (x_596 == 0)
{
return x_503;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_503, 0);
x_598 = lean_ctor_get(x_503, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_503);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
}
}
case 5:
{
lean_object* x_613; 
lean_dec(x_8);
lean_inc(x_3);
x_613 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
if (lean_obj_tag(x_614) == 0)
{
uint8_t x_615; 
lean_dec(x_3);
lean_dec(x_1);
x_615 = !lean_is_exclusive(x_613);
if (x_615 == 0)
{
lean_object* x_616; lean_object* x_617; 
x_616 = lean_ctor_get(x_613, 0);
lean_dec(x_616);
x_617 = lean_box(0);
lean_ctor_set(x_613, 0, x_617);
return x_613;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_613, 1);
lean_inc(x_618);
lean_dec(x_613);
x_619 = lean_box(0);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
x_621 = lean_ctor_get(x_613, 1);
lean_inc(x_621);
lean_dec(x_613);
x_622 = lean_ctor_get(x_614, 0);
lean_inc(x_622);
lean_dec(x_614);
x_694 = lean_ctor_get(x_3, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
lean_dec(x_694);
x_696 = lean_ctor_get(x_695, 3);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 4);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_nat_dec_eq(x_696, x_697);
lean_dec(x_697);
lean_dec(x_696);
if (x_698 == 0)
{
x_623 = x_621;
goto block_693;
}
else
{
lean_object* x_699; lean_object* x_700; 
x_699 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_700 = l_Lean_Elab_Tactic_throwError___rarg(x_699, x_3, x_621);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; 
x_701 = lean_ctor_get(x_700, 1);
lean_inc(x_701);
lean_dec(x_700);
x_623 = x_701;
goto block_693;
}
else
{
uint8_t x_702; 
lean_dec(x_622);
lean_dec(x_3);
lean_dec(x_1);
x_702 = !lean_is_exclusive(x_700);
if (x_702 == 0)
{
return x_700;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_703 = lean_ctor_get(x_700, 0);
x_704 = lean_ctor_get(x_700, 1);
lean_inc(x_704);
lean_inc(x_703);
lean_dec(x_700);
x_705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_705, 0, x_703);
lean_ctor_set(x_705, 1, x_704);
return x_705;
}
}
}
block_693:
{
lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_624 = lean_ctor_get(x_3, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = !lean_is_exclusive(x_3);
if (x_626 == 0)
{
lean_object* x_627; uint8_t x_628; 
x_627 = lean_ctor_get(x_3, 0);
lean_dec(x_627);
x_628 = !lean_is_exclusive(x_624);
if (x_628 == 0)
{
lean_object* x_629; uint8_t x_630; 
x_629 = lean_ctor_get(x_624, 0);
lean_dec(x_629);
x_630 = !lean_is_exclusive(x_625);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_625, 3);
x_632 = lean_unsigned_to_nat(1u);
x_633 = lean_nat_add(x_631, x_632);
lean_dec(x_631);
lean_ctor_set(x_625, 3, x_633);
x_2 = x_622;
x_4 = x_623;
goto _start;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_635 = lean_ctor_get(x_625, 0);
x_636 = lean_ctor_get(x_625, 1);
x_637 = lean_ctor_get(x_625, 2);
x_638 = lean_ctor_get(x_625, 3);
x_639 = lean_ctor_get(x_625, 4);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_625);
x_640 = lean_unsigned_to_nat(1u);
x_641 = lean_nat_add(x_638, x_640);
lean_dec(x_638);
x_642 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_642, 0, x_635);
lean_ctor_set(x_642, 1, x_636);
lean_ctor_set(x_642, 2, x_637);
lean_ctor_set(x_642, 3, x_641);
lean_ctor_set(x_642, 4, x_639);
lean_ctor_set(x_624, 0, x_642);
x_2 = x_622;
x_4 = x_623;
goto _start;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; uint8_t x_653; uint8_t x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_644 = lean_ctor_get(x_624, 1);
x_645 = lean_ctor_get(x_624, 2);
x_646 = lean_ctor_get(x_624, 3);
x_647 = lean_ctor_get(x_624, 4);
x_648 = lean_ctor_get(x_624, 5);
x_649 = lean_ctor_get(x_624, 6);
x_650 = lean_ctor_get(x_624, 7);
x_651 = lean_ctor_get(x_624, 8);
x_652 = lean_ctor_get_uint8(x_624, sizeof(void*)*10);
x_653 = lean_ctor_get_uint8(x_624, sizeof(void*)*10 + 1);
x_654 = lean_ctor_get_uint8(x_624, sizeof(void*)*10 + 2);
x_655 = lean_ctor_get(x_624, 9);
lean_inc(x_655);
lean_inc(x_651);
lean_inc(x_650);
lean_inc(x_649);
lean_inc(x_648);
lean_inc(x_647);
lean_inc(x_646);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_624);
x_656 = lean_ctor_get(x_625, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_625, 1);
lean_inc(x_657);
x_658 = lean_ctor_get(x_625, 2);
lean_inc(x_658);
x_659 = lean_ctor_get(x_625, 3);
lean_inc(x_659);
x_660 = lean_ctor_get(x_625, 4);
lean_inc(x_660);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 lean_ctor_release(x_625, 2);
 lean_ctor_release(x_625, 3);
 lean_ctor_release(x_625, 4);
 x_661 = x_625;
} else {
 lean_dec_ref(x_625);
 x_661 = lean_box(0);
}
x_662 = lean_unsigned_to_nat(1u);
x_663 = lean_nat_add(x_659, x_662);
lean_dec(x_659);
if (lean_is_scalar(x_661)) {
 x_664 = lean_alloc_ctor(0, 5, 0);
} else {
 x_664 = x_661;
}
lean_ctor_set(x_664, 0, x_656);
lean_ctor_set(x_664, 1, x_657);
lean_ctor_set(x_664, 2, x_658);
lean_ctor_set(x_664, 3, x_663);
lean_ctor_set(x_664, 4, x_660);
x_665 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_644);
lean_ctor_set(x_665, 2, x_645);
lean_ctor_set(x_665, 3, x_646);
lean_ctor_set(x_665, 4, x_647);
lean_ctor_set(x_665, 5, x_648);
lean_ctor_set(x_665, 6, x_649);
lean_ctor_set(x_665, 7, x_650);
lean_ctor_set(x_665, 8, x_651);
lean_ctor_set(x_665, 9, x_655);
lean_ctor_set_uint8(x_665, sizeof(void*)*10, x_652);
lean_ctor_set_uint8(x_665, sizeof(void*)*10 + 1, x_653);
lean_ctor_set_uint8(x_665, sizeof(void*)*10 + 2, x_654);
lean_ctor_set(x_3, 0, x_665);
x_2 = x_622;
x_4 = x_623;
goto _start;
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; uint8_t x_677; uint8_t x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_667 = lean_ctor_get(x_3, 1);
lean_inc(x_667);
lean_dec(x_3);
x_668 = lean_ctor_get(x_624, 1);
lean_inc(x_668);
x_669 = lean_ctor_get(x_624, 2);
lean_inc(x_669);
x_670 = lean_ctor_get(x_624, 3);
lean_inc(x_670);
x_671 = lean_ctor_get(x_624, 4);
lean_inc(x_671);
x_672 = lean_ctor_get(x_624, 5);
lean_inc(x_672);
x_673 = lean_ctor_get(x_624, 6);
lean_inc(x_673);
x_674 = lean_ctor_get(x_624, 7);
lean_inc(x_674);
x_675 = lean_ctor_get(x_624, 8);
lean_inc(x_675);
x_676 = lean_ctor_get_uint8(x_624, sizeof(void*)*10);
x_677 = lean_ctor_get_uint8(x_624, sizeof(void*)*10 + 1);
x_678 = lean_ctor_get_uint8(x_624, sizeof(void*)*10 + 2);
x_679 = lean_ctor_get(x_624, 9);
lean_inc(x_679);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 lean_ctor_release(x_624, 2);
 lean_ctor_release(x_624, 3);
 lean_ctor_release(x_624, 4);
 lean_ctor_release(x_624, 5);
 lean_ctor_release(x_624, 6);
 lean_ctor_release(x_624, 7);
 lean_ctor_release(x_624, 8);
 lean_ctor_release(x_624, 9);
 x_680 = x_624;
} else {
 lean_dec_ref(x_624);
 x_680 = lean_box(0);
}
x_681 = lean_ctor_get(x_625, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_625, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_625, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_625, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_625, 4);
lean_inc(x_685);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 lean_ctor_release(x_625, 2);
 lean_ctor_release(x_625, 3);
 lean_ctor_release(x_625, 4);
 x_686 = x_625;
} else {
 lean_dec_ref(x_625);
 x_686 = lean_box(0);
}
x_687 = lean_unsigned_to_nat(1u);
x_688 = lean_nat_add(x_684, x_687);
lean_dec(x_684);
if (lean_is_scalar(x_686)) {
 x_689 = lean_alloc_ctor(0, 5, 0);
} else {
 x_689 = x_686;
}
lean_ctor_set(x_689, 0, x_681);
lean_ctor_set(x_689, 1, x_682);
lean_ctor_set(x_689, 2, x_683);
lean_ctor_set(x_689, 3, x_688);
lean_ctor_set(x_689, 4, x_685);
if (lean_is_scalar(x_680)) {
 x_690 = lean_alloc_ctor(0, 10, 3);
} else {
 x_690 = x_680;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_668);
lean_ctor_set(x_690, 2, x_669);
lean_ctor_set(x_690, 3, x_670);
lean_ctor_set(x_690, 4, x_671);
lean_ctor_set(x_690, 5, x_672);
lean_ctor_set(x_690, 6, x_673);
lean_ctor_set(x_690, 7, x_674);
lean_ctor_set(x_690, 8, x_675);
lean_ctor_set(x_690, 9, x_679);
lean_ctor_set_uint8(x_690, sizeof(void*)*10, x_676);
lean_ctor_set_uint8(x_690, sizeof(void*)*10 + 1, x_677);
lean_ctor_set_uint8(x_690, sizeof(void*)*10 + 2, x_678);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_667);
x_2 = x_622;
x_3 = x_691;
x_4 = x_623;
goto _start;
}
}
}
}
else
{
uint8_t x_706; 
lean_dec(x_3);
lean_dec(x_1);
x_706 = !lean_is_exclusive(x_613);
if (x_706 == 0)
{
return x_613;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_707 = lean_ctor_get(x_613, 0);
x_708 = lean_ctor_get(x_613, 1);
lean_inc(x_708);
lean_inc(x_707);
lean_dec(x_613);
x_709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_709, 0, x_707);
lean_ctor_set(x_709, 1, x_708);
return x_709;
}
}
}
case 6:
{
lean_object* x_710; 
lean_dec(x_8);
lean_inc(x_3);
x_710 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; 
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
if (lean_obj_tag(x_711) == 0)
{
uint8_t x_712; 
lean_dec(x_3);
lean_dec(x_1);
x_712 = !lean_is_exclusive(x_710);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; 
x_713 = lean_ctor_get(x_710, 0);
lean_dec(x_713);
x_714 = lean_box(0);
lean_ctor_set(x_710, 0, x_714);
return x_710;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_710, 1);
lean_inc(x_715);
lean_dec(x_710);
x_716 = lean_box(0);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_715);
return x_717;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; uint8_t x_795; 
x_718 = lean_ctor_get(x_710, 1);
lean_inc(x_718);
lean_dec(x_710);
x_719 = lean_ctor_get(x_711, 0);
lean_inc(x_719);
lean_dec(x_711);
x_791 = lean_ctor_get(x_3, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
lean_dec(x_791);
x_793 = lean_ctor_get(x_792, 3);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 4);
lean_inc(x_794);
lean_dec(x_792);
x_795 = lean_nat_dec_eq(x_793, x_794);
lean_dec(x_794);
lean_dec(x_793);
if (x_795 == 0)
{
x_720 = x_718;
goto block_790;
}
else
{
lean_object* x_796; lean_object* x_797; 
x_796 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_797 = l_Lean_Elab_Tactic_throwError___rarg(x_796, x_3, x_718);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; 
x_798 = lean_ctor_get(x_797, 1);
lean_inc(x_798);
lean_dec(x_797);
x_720 = x_798;
goto block_790;
}
else
{
uint8_t x_799; 
lean_dec(x_719);
lean_dec(x_3);
lean_dec(x_1);
x_799 = !lean_is_exclusive(x_797);
if (x_799 == 0)
{
return x_797;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_797, 0);
x_801 = lean_ctor_get(x_797, 1);
lean_inc(x_801);
lean_inc(x_800);
lean_dec(x_797);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
}
block_790:
{
lean_object* x_721; lean_object* x_722; uint8_t x_723; 
x_721 = lean_ctor_get(x_3, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = !lean_is_exclusive(x_3);
if (x_723 == 0)
{
lean_object* x_724; uint8_t x_725; 
x_724 = lean_ctor_get(x_3, 0);
lean_dec(x_724);
x_725 = !lean_is_exclusive(x_721);
if (x_725 == 0)
{
lean_object* x_726; uint8_t x_727; 
x_726 = lean_ctor_get(x_721, 0);
lean_dec(x_726);
x_727 = !lean_is_exclusive(x_722);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_722, 3);
x_729 = lean_unsigned_to_nat(1u);
x_730 = lean_nat_add(x_728, x_729);
lean_dec(x_728);
lean_ctor_set(x_722, 3, x_730);
x_2 = x_719;
x_4 = x_720;
goto _start;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_732 = lean_ctor_get(x_722, 0);
x_733 = lean_ctor_get(x_722, 1);
x_734 = lean_ctor_get(x_722, 2);
x_735 = lean_ctor_get(x_722, 3);
x_736 = lean_ctor_get(x_722, 4);
lean_inc(x_736);
lean_inc(x_735);
lean_inc(x_734);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_722);
x_737 = lean_unsigned_to_nat(1u);
x_738 = lean_nat_add(x_735, x_737);
lean_dec(x_735);
x_739 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_739, 0, x_732);
lean_ctor_set(x_739, 1, x_733);
lean_ctor_set(x_739, 2, x_734);
lean_ctor_set(x_739, 3, x_738);
lean_ctor_set(x_739, 4, x_736);
lean_ctor_set(x_721, 0, x_739);
x_2 = x_719;
x_4 = x_720;
goto _start;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; uint8_t x_749; uint8_t x_750; uint8_t x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_741 = lean_ctor_get(x_721, 1);
x_742 = lean_ctor_get(x_721, 2);
x_743 = lean_ctor_get(x_721, 3);
x_744 = lean_ctor_get(x_721, 4);
x_745 = lean_ctor_get(x_721, 5);
x_746 = lean_ctor_get(x_721, 6);
x_747 = lean_ctor_get(x_721, 7);
x_748 = lean_ctor_get(x_721, 8);
x_749 = lean_ctor_get_uint8(x_721, sizeof(void*)*10);
x_750 = lean_ctor_get_uint8(x_721, sizeof(void*)*10 + 1);
x_751 = lean_ctor_get_uint8(x_721, sizeof(void*)*10 + 2);
x_752 = lean_ctor_get(x_721, 9);
lean_inc(x_752);
lean_inc(x_748);
lean_inc(x_747);
lean_inc(x_746);
lean_inc(x_745);
lean_inc(x_744);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_dec(x_721);
x_753 = lean_ctor_get(x_722, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_722, 1);
lean_inc(x_754);
x_755 = lean_ctor_get(x_722, 2);
lean_inc(x_755);
x_756 = lean_ctor_get(x_722, 3);
lean_inc(x_756);
x_757 = lean_ctor_get(x_722, 4);
lean_inc(x_757);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 lean_ctor_release(x_722, 2);
 lean_ctor_release(x_722, 3);
 lean_ctor_release(x_722, 4);
 x_758 = x_722;
} else {
 lean_dec_ref(x_722);
 x_758 = lean_box(0);
}
x_759 = lean_unsigned_to_nat(1u);
x_760 = lean_nat_add(x_756, x_759);
lean_dec(x_756);
if (lean_is_scalar(x_758)) {
 x_761 = lean_alloc_ctor(0, 5, 0);
} else {
 x_761 = x_758;
}
lean_ctor_set(x_761, 0, x_753);
lean_ctor_set(x_761, 1, x_754);
lean_ctor_set(x_761, 2, x_755);
lean_ctor_set(x_761, 3, x_760);
lean_ctor_set(x_761, 4, x_757);
x_762 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_741);
lean_ctor_set(x_762, 2, x_742);
lean_ctor_set(x_762, 3, x_743);
lean_ctor_set(x_762, 4, x_744);
lean_ctor_set(x_762, 5, x_745);
lean_ctor_set(x_762, 6, x_746);
lean_ctor_set(x_762, 7, x_747);
lean_ctor_set(x_762, 8, x_748);
lean_ctor_set(x_762, 9, x_752);
lean_ctor_set_uint8(x_762, sizeof(void*)*10, x_749);
lean_ctor_set_uint8(x_762, sizeof(void*)*10 + 1, x_750);
lean_ctor_set_uint8(x_762, sizeof(void*)*10 + 2, x_751);
lean_ctor_set(x_3, 0, x_762);
x_2 = x_719;
x_4 = x_720;
goto _start;
}
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; uint8_t x_773; uint8_t x_774; uint8_t x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_764 = lean_ctor_get(x_3, 1);
lean_inc(x_764);
lean_dec(x_3);
x_765 = lean_ctor_get(x_721, 1);
lean_inc(x_765);
x_766 = lean_ctor_get(x_721, 2);
lean_inc(x_766);
x_767 = lean_ctor_get(x_721, 3);
lean_inc(x_767);
x_768 = lean_ctor_get(x_721, 4);
lean_inc(x_768);
x_769 = lean_ctor_get(x_721, 5);
lean_inc(x_769);
x_770 = lean_ctor_get(x_721, 6);
lean_inc(x_770);
x_771 = lean_ctor_get(x_721, 7);
lean_inc(x_771);
x_772 = lean_ctor_get(x_721, 8);
lean_inc(x_772);
x_773 = lean_ctor_get_uint8(x_721, sizeof(void*)*10);
x_774 = lean_ctor_get_uint8(x_721, sizeof(void*)*10 + 1);
x_775 = lean_ctor_get_uint8(x_721, sizeof(void*)*10 + 2);
x_776 = lean_ctor_get(x_721, 9);
lean_inc(x_776);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 lean_ctor_release(x_721, 2);
 lean_ctor_release(x_721, 3);
 lean_ctor_release(x_721, 4);
 lean_ctor_release(x_721, 5);
 lean_ctor_release(x_721, 6);
 lean_ctor_release(x_721, 7);
 lean_ctor_release(x_721, 8);
 lean_ctor_release(x_721, 9);
 x_777 = x_721;
} else {
 lean_dec_ref(x_721);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_722, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_722, 1);
lean_inc(x_779);
x_780 = lean_ctor_get(x_722, 2);
lean_inc(x_780);
x_781 = lean_ctor_get(x_722, 3);
lean_inc(x_781);
x_782 = lean_ctor_get(x_722, 4);
lean_inc(x_782);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 lean_ctor_release(x_722, 2);
 lean_ctor_release(x_722, 3);
 lean_ctor_release(x_722, 4);
 x_783 = x_722;
} else {
 lean_dec_ref(x_722);
 x_783 = lean_box(0);
}
x_784 = lean_unsigned_to_nat(1u);
x_785 = lean_nat_add(x_781, x_784);
lean_dec(x_781);
if (lean_is_scalar(x_783)) {
 x_786 = lean_alloc_ctor(0, 5, 0);
} else {
 x_786 = x_783;
}
lean_ctor_set(x_786, 0, x_778);
lean_ctor_set(x_786, 1, x_779);
lean_ctor_set(x_786, 2, x_780);
lean_ctor_set(x_786, 3, x_785);
lean_ctor_set(x_786, 4, x_782);
if (lean_is_scalar(x_777)) {
 x_787 = lean_alloc_ctor(0, 10, 3);
} else {
 x_787 = x_777;
}
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_787, 1, x_765);
lean_ctor_set(x_787, 2, x_766);
lean_ctor_set(x_787, 3, x_767);
lean_ctor_set(x_787, 4, x_768);
lean_ctor_set(x_787, 5, x_769);
lean_ctor_set(x_787, 6, x_770);
lean_ctor_set(x_787, 7, x_771);
lean_ctor_set(x_787, 8, x_772);
lean_ctor_set(x_787, 9, x_776);
lean_ctor_set_uint8(x_787, sizeof(void*)*10, x_773);
lean_ctor_set_uint8(x_787, sizeof(void*)*10 + 1, x_774);
lean_ctor_set_uint8(x_787, sizeof(void*)*10 + 2, x_775);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_764);
x_2 = x_719;
x_3 = x_788;
x_4 = x_720;
goto _start;
}
}
}
}
else
{
uint8_t x_803; 
lean_dec(x_3);
lean_dec(x_1);
x_803 = !lean_is_exclusive(x_710);
if (x_803 == 0)
{
return x_710;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_710, 0);
x_805 = lean_ctor_get(x_710, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_710);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
case 7:
{
lean_object* x_807; 
lean_dec(x_8);
lean_inc(x_3);
x_807 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
if (lean_obj_tag(x_808) == 0)
{
uint8_t x_809; 
lean_dec(x_3);
lean_dec(x_1);
x_809 = !lean_is_exclusive(x_807);
if (x_809 == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_807, 0);
lean_dec(x_810);
x_811 = lean_box(0);
lean_ctor_set(x_807, 0, x_811);
return x_807;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_807, 1);
lean_inc(x_812);
lean_dec(x_807);
x_813 = lean_box(0);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; 
x_815 = lean_ctor_get(x_807, 1);
lean_inc(x_815);
lean_dec(x_807);
x_816 = lean_ctor_get(x_808, 0);
lean_inc(x_816);
lean_dec(x_808);
x_888 = lean_ctor_get(x_3, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
lean_dec(x_888);
x_890 = lean_ctor_get(x_889, 3);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 4);
lean_inc(x_891);
lean_dec(x_889);
x_892 = lean_nat_dec_eq(x_890, x_891);
lean_dec(x_891);
lean_dec(x_890);
if (x_892 == 0)
{
x_817 = x_815;
goto block_887;
}
else
{
lean_object* x_893; lean_object* x_894; 
x_893 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_894 = l_Lean_Elab_Tactic_throwError___rarg(x_893, x_3, x_815);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; 
x_895 = lean_ctor_get(x_894, 1);
lean_inc(x_895);
lean_dec(x_894);
x_817 = x_895;
goto block_887;
}
else
{
uint8_t x_896; 
lean_dec(x_816);
lean_dec(x_3);
lean_dec(x_1);
x_896 = !lean_is_exclusive(x_894);
if (x_896 == 0)
{
return x_894;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_894, 0);
x_898 = lean_ctor_get(x_894, 1);
lean_inc(x_898);
lean_inc(x_897);
lean_dec(x_894);
x_899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_899, 0, x_897);
lean_ctor_set(x_899, 1, x_898);
return x_899;
}
}
}
block_887:
{
lean_object* x_818; lean_object* x_819; uint8_t x_820; 
x_818 = lean_ctor_get(x_3, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = !lean_is_exclusive(x_3);
if (x_820 == 0)
{
lean_object* x_821; uint8_t x_822; 
x_821 = lean_ctor_get(x_3, 0);
lean_dec(x_821);
x_822 = !lean_is_exclusive(x_818);
if (x_822 == 0)
{
lean_object* x_823; uint8_t x_824; 
x_823 = lean_ctor_get(x_818, 0);
lean_dec(x_823);
x_824 = !lean_is_exclusive(x_819);
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_819, 3);
x_826 = lean_unsigned_to_nat(1u);
x_827 = lean_nat_add(x_825, x_826);
lean_dec(x_825);
lean_ctor_set(x_819, 3, x_827);
x_2 = x_816;
x_4 = x_817;
goto _start;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_829 = lean_ctor_get(x_819, 0);
x_830 = lean_ctor_get(x_819, 1);
x_831 = lean_ctor_get(x_819, 2);
x_832 = lean_ctor_get(x_819, 3);
x_833 = lean_ctor_get(x_819, 4);
lean_inc(x_833);
lean_inc(x_832);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_819);
x_834 = lean_unsigned_to_nat(1u);
x_835 = lean_nat_add(x_832, x_834);
lean_dec(x_832);
x_836 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_836, 0, x_829);
lean_ctor_set(x_836, 1, x_830);
lean_ctor_set(x_836, 2, x_831);
lean_ctor_set(x_836, 3, x_835);
lean_ctor_set(x_836, 4, x_833);
lean_ctor_set(x_818, 0, x_836);
x_2 = x_816;
x_4 = x_817;
goto _start;
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; uint8_t x_846; uint8_t x_847; uint8_t x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_838 = lean_ctor_get(x_818, 1);
x_839 = lean_ctor_get(x_818, 2);
x_840 = lean_ctor_get(x_818, 3);
x_841 = lean_ctor_get(x_818, 4);
x_842 = lean_ctor_get(x_818, 5);
x_843 = lean_ctor_get(x_818, 6);
x_844 = lean_ctor_get(x_818, 7);
x_845 = lean_ctor_get(x_818, 8);
x_846 = lean_ctor_get_uint8(x_818, sizeof(void*)*10);
x_847 = lean_ctor_get_uint8(x_818, sizeof(void*)*10 + 1);
x_848 = lean_ctor_get_uint8(x_818, sizeof(void*)*10 + 2);
x_849 = lean_ctor_get(x_818, 9);
lean_inc(x_849);
lean_inc(x_845);
lean_inc(x_844);
lean_inc(x_843);
lean_inc(x_842);
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_818);
x_850 = lean_ctor_get(x_819, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_819, 1);
lean_inc(x_851);
x_852 = lean_ctor_get(x_819, 2);
lean_inc(x_852);
x_853 = lean_ctor_get(x_819, 3);
lean_inc(x_853);
x_854 = lean_ctor_get(x_819, 4);
lean_inc(x_854);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 lean_ctor_release(x_819, 2);
 lean_ctor_release(x_819, 3);
 lean_ctor_release(x_819, 4);
 x_855 = x_819;
} else {
 lean_dec_ref(x_819);
 x_855 = lean_box(0);
}
x_856 = lean_unsigned_to_nat(1u);
x_857 = lean_nat_add(x_853, x_856);
lean_dec(x_853);
if (lean_is_scalar(x_855)) {
 x_858 = lean_alloc_ctor(0, 5, 0);
} else {
 x_858 = x_855;
}
lean_ctor_set(x_858, 0, x_850);
lean_ctor_set(x_858, 1, x_851);
lean_ctor_set(x_858, 2, x_852);
lean_ctor_set(x_858, 3, x_857);
lean_ctor_set(x_858, 4, x_854);
x_859 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_838);
lean_ctor_set(x_859, 2, x_839);
lean_ctor_set(x_859, 3, x_840);
lean_ctor_set(x_859, 4, x_841);
lean_ctor_set(x_859, 5, x_842);
lean_ctor_set(x_859, 6, x_843);
lean_ctor_set(x_859, 7, x_844);
lean_ctor_set(x_859, 8, x_845);
lean_ctor_set(x_859, 9, x_849);
lean_ctor_set_uint8(x_859, sizeof(void*)*10, x_846);
lean_ctor_set_uint8(x_859, sizeof(void*)*10 + 1, x_847);
lean_ctor_set_uint8(x_859, sizeof(void*)*10 + 2, x_848);
lean_ctor_set(x_3, 0, x_859);
x_2 = x_816;
x_4 = x_817;
goto _start;
}
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; uint8_t x_870; uint8_t x_871; uint8_t x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_861 = lean_ctor_get(x_3, 1);
lean_inc(x_861);
lean_dec(x_3);
x_862 = lean_ctor_get(x_818, 1);
lean_inc(x_862);
x_863 = lean_ctor_get(x_818, 2);
lean_inc(x_863);
x_864 = lean_ctor_get(x_818, 3);
lean_inc(x_864);
x_865 = lean_ctor_get(x_818, 4);
lean_inc(x_865);
x_866 = lean_ctor_get(x_818, 5);
lean_inc(x_866);
x_867 = lean_ctor_get(x_818, 6);
lean_inc(x_867);
x_868 = lean_ctor_get(x_818, 7);
lean_inc(x_868);
x_869 = lean_ctor_get(x_818, 8);
lean_inc(x_869);
x_870 = lean_ctor_get_uint8(x_818, sizeof(void*)*10);
x_871 = lean_ctor_get_uint8(x_818, sizeof(void*)*10 + 1);
x_872 = lean_ctor_get_uint8(x_818, sizeof(void*)*10 + 2);
x_873 = lean_ctor_get(x_818, 9);
lean_inc(x_873);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 lean_ctor_release(x_818, 4);
 lean_ctor_release(x_818, 5);
 lean_ctor_release(x_818, 6);
 lean_ctor_release(x_818, 7);
 lean_ctor_release(x_818, 8);
 lean_ctor_release(x_818, 9);
 x_874 = x_818;
} else {
 lean_dec_ref(x_818);
 x_874 = lean_box(0);
}
x_875 = lean_ctor_get(x_819, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_819, 1);
lean_inc(x_876);
x_877 = lean_ctor_get(x_819, 2);
lean_inc(x_877);
x_878 = lean_ctor_get(x_819, 3);
lean_inc(x_878);
x_879 = lean_ctor_get(x_819, 4);
lean_inc(x_879);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 lean_ctor_release(x_819, 2);
 lean_ctor_release(x_819, 3);
 lean_ctor_release(x_819, 4);
 x_880 = x_819;
} else {
 lean_dec_ref(x_819);
 x_880 = lean_box(0);
}
x_881 = lean_unsigned_to_nat(1u);
x_882 = lean_nat_add(x_878, x_881);
lean_dec(x_878);
if (lean_is_scalar(x_880)) {
 x_883 = lean_alloc_ctor(0, 5, 0);
} else {
 x_883 = x_880;
}
lean_ctor_set(x_883, 0, x_875);
lean_ctor_set(x_883, 1, x_876);
lean_ctor_set(x_883, 2, x_877);
lean_ctor_set(x_883, 3, x_882);
lean_ctor_set(x_883, 4, x_879);
if (lean_is_scalar(x_874)) {
 x_884 = lean_alloc_ctor(0, 10, 3);
} else {
 x_884 = x_874;
}
lean_ctor_set(x_884, 0, x_883);
lean_ctor_set(x_884, 1, x_862);
lean_ctor_set(x_884, 2, x_863);
lean_ctor_set(x_884, 3, x_864);
lean_ctor_set(x_884, 4, x_865);
lean_ctor_set(x_884, 5, x_866);
lean_ctor_set(x_884, 6, x_867);
lean_ctor_set(x_884, 7, x_868);
lean_ctor_set(x_884, 8, x_869);
lean_ctor_set(x_884, 9, x_873);
lean_ctor_set_uint8(x_884, sizeof(void*)*10, x_870);
lean_ctor_set_uint8(x_884, sizeof(void*)*10 + 1, x_871);
lean_ctor_set_uint8(x_884, sizeof(void*)*10 + 2, x_872);
x_885 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_885, 0, x_884);
lean_ctor_set(x_885, 1, x_861);
x_2 = x_816;
x_3 = x_885;
x_4 = x_817;
goto _start;
}
}
}
}
else
{
uint8_t x_900; 
lean_dec(x_3);
lean_dec(x_1);
x_900 = !lean_is_exclusive(x_807);
if (x_900 == 0)
{
return x_807;
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_901 = lean_ctor_get(x_807, 0);
x_902 = lean_ctor_get(x_807, 1);
lean_inc(x_902);
lean_inc(x_901);
lean_dec(x_807);
x_903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_903, 0, x_901);
lean_ctor_set(x_903, 1, x_902);
return x_903;
}
}
}
case 8:
{
lean_object* x_904; 
lean_dec(x_8);
lean_inc(x_3);
x_904 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; 
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
if (lean_obj_tag(x_905) == 0)
{
uint8_t x_906; 
lean_dec(x_3);
lean_dec(x_1);
x_906 = !lean_is_exclusive(x_904);
if (x_906 == 0)
{
lean_object* x_907; lean_object* x_908; 
x_907 = lean_ctor_get(x_904, 0);
lean_dec(x_907);
x_908 = lean_box(0);
lean_ctor_set(x_904, 0, x_908);
return x_904;
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_909 = lean_ctor_get(x_904, 1);
lean_inc(x_909);
lean_dec(x_904);
x_910 = lean_box(0);
x_911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_909);
return x_911;
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; uint8_t x_989; 
x_912 = lean_ctor_get(x_904, 1);
lean_inc(x_912);
lean_dec(x_904);
x_913 = lean_ctor_get(x_905, 0);
lean_inc(x_913);
lean_dec(x_905);
x_985 = lean_ctor_get(x_3, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
lean_dec(x_985);
x_987 = lean_ctor_get(x_986, 3);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 4);
lean_inc(x_988);
lean_dec(x_986);
x_989 = lean_nat_dec_eq(x_987, x_988);
lean_dec(x_988);
lean_dec(x_987);
if (x_989 == 0)
{
x_914 = x_912;
goto block_984;
}
else
{
lean_object* x_990; lean_object* x_991; 
x_990 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_991 = l_Lean_Elab_Tactic_throwError___rarg(x_990, x_3, x_912);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; 
x_992 = lean_ctor_get(x_991, 1);
lean_inc(x_992);
lean_dec(x_991);
x_914 = x_992;
goto block_984;
}
else
{
uint8_t x_993; 
lean_dec(x_913);
lean_dec(x_3);
lean_dec(x_1);
x_993 = !lean_is_exclusive(x_991);
if (x_993 == 0)
{
return x_991;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_994 = lean_ctor_get(x_991, 0);
x_995 = lean_ctor_get(x_991, 1);
lean_inc(x_995);
lean_inc(x_994);
lean_dec(x_991);
x_996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_996, 0, x_994);
lean_ctor_set(x_996, 1, x_995);
return x_996;
}
}
}
block_984:
{
lean_object* x_915; lean_object* x_916; uint8_t x_917; 
x_915 = lean_ctor_get(x_3, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = !lean_is_exclusive(x_3);
if (x_917 == 0)
{
lean_object* x_918; uint8_t x_919; 
x_918 = lean_ctor_get(x_3, 0);
lean_dec(x_918);
x_919 = !lean_is_exclusive(x_915);
if (x_919 == 0)
{
lean_object* x_920; uint8_t x_921; 
x_920 = lean_ctor_get(x_915, 0);
lean_dec(x_920);
x_921 = !lean_is_exclusive(x_916);
if (x_921 == 0)
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_922 = lean_ctor_get(x_916, 3);
x_923 = lean_unsigned_to_nat(1u);
x_924 = lean_nat_add(x_922, x_923);
lean_dec(x_922);
lean_ctor_set(x_916, 3, x_924);
x_2 = x_913;
x_4 = x_914;
goto _start;
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_926 = lean_ctor_get(x_916, 0);
x_927 = lean_ctor_get(x_916, 1);
x_928 = lean_ctor_get(x_916, 2);
x_929 = lean_ctor_get(x_916, 3);
x_930 = lean_ctor_get(x_916, 4);
lean_inc(x_930);
lean_inc(x_929);
lean_inc(x_928);
lean_inc(x_927);
lean_inc(x_926);
lean_dec(x_916);
x_931 = lean_unsigned_to_nat(1u);
x_932 = lean_nat_add(x_929, x_931);
lean_dec(x_929);
x_933 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_933, 0, x_926);
lean_ctor_set(x_933, 1, x_927);
lean_ctor_set(x_933, 2, x_928);
lean_ctor_set(x_933, 3, x_932);
lean_ctor_set(x_933, 4, x_930);
lean_ctor_set(x_915, 0, x_933);
x_2 = x_913;
x_4 = x_914;
goto _start;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint8_t x_943; uint8_t x_944; uint8_t x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_935 = lean_ctor_get(x_915, 1);
x_936 = lean_ctor_get(x_915, 2);
x_937 = lean_ctor_get(x_915, 3);
x_938 = lean_ctor_get(x_915, 4);
x_939 = lean_ctor_get(x_915, 5);
x_940 = lean_ctor_get(x_915, 6);
x_941 = lean_ctor_get(x_915, 7);
x_942 = lean_ctor_get(x_915, 8);
x_943 = lean_ctor_get_uint8(x_915, sizeof(void*)*10);
x_944 = lean_ctor_get_uint8(x_915, sizeof(void*)*10 + 1);
x_945 = lean_ctor_get_uint8(x_915, sizeof(void*)*10 + 2);
x_946 = lean_ctor_get(x_915, 9);
lean_inc(x_946);
lean_inc(x_942);
lean_inc(x_941);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_inc(x_936);
lean_inc(x_935);
lean_dec(x_915);
x_947 = lean_ctor_get(x_916, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_916, 1);
lean_inc(x_948);
x_949 = lean_ctor_get(x_916, 2);
lean_inc(x_949);
x_950 = lean_ctor_get(x_916, 3);
lean_inc(x_950);
x_951 = lean_ctor_get(x_916, 4);
lean_inc(x_951);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 lean_ctor_release(x_916, 2);
 lean_ctor_release(x_916, 3);
 lean_ctor_release(x_916, 4);
 x_952 = x_916;
} else {
 lean_dec_ref(x_916);
 x_952 = lean_box(0);
}
x_953 = lean_unsigned_to_nat(1u);
x_954 = lean_nat_add(x_950, x_953);
lean_dec(x_950);
if (lean_is_scalar(x_952)) {
 x_955 = lean_alloc_ctor(0, 5, 0);
} else {
 x_955 = x_952;
}
lean_ctor_set(x_955, 0, x_947);
lean_ctor_set(x_955, 1, x_948);
lean_ctor_set(x_955, 2, x_949);
lean_ctor_set(x_955, 3, x_954);
lean_ctor_set(x_955, 4, x_951);
x_956 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_935);
lean_ctor_set(x_956, 2, x_936);
lean_ctor_set(x_956, 3, x_937);
lean_ctor_set(x_956, 4, x_938);
lean_ctor_set(x_956, 5, x_939);
lean_ctor_set(x_956, 6, x_940);
lean_ctor_set(x_956, 7, x_941);
lean_ctor_set(x_956, 8, x_942);
lean_ctor_set(x_956, 9, x_946);
lean_ctor_set_uint8(x_956, sizeof(void*)*10, x_943);
lean_ctor_set_uint8(x_956, sizeof(void*)*10 + 1, x_944);
lean_ctor_set_uint8(x_956, sizeof(void*)*10 + 2, x_945);
lean_ctor_set(x_3, 0, x_956);
x_2 = x_913;
x_4 = x_914;
goto _start;
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_967; uint8_t x_968; uint8_t x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_958 = lean_ctor_get(x_3, 1);
lean_inc(x_958);
lean_dec(x_3);
x_959 = lean_ctor_get(x_915, 1);
lean_inc(x_959);
x_960 = lean_ctor_get(x_915, 2);
lean_inc(x_960);
x_961 = lean_ctor_get(x_915, 3);
lean_inc(x_961);
x_962 = lean_ctor_get(x_915, 4);
lean_inc(x_962);
x_963 = lean_ctor_get(x_915, 5);
lean_inc(x_963);
x_964 = lean_ctor_get(x_915, 6);
lean_inc(x_964);
x_965 = lean_ctor_get(x_915, 7);
lean_inc(x_965);
x_966 = lean_ctor_get(x_915, 8);
lean_inc(x_966);
x_967 = lean_ctor_get_uint8(x_915, sizeof(void*)*10);
x_968 = lean_ctor_get_uint8(x_915, sizeof(void*)*10 + 1);
x_969 = lean_ctor_get_uint8(x_915, sizeof(void*)*10 + 2);
x_970 = lean_ctor_get(x_915, 9);
lean_inc(x_970);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 lean_ctor_release(x_915, 2);
 lean_ctor_release(x_915, 3);
 lean_ctor_release(x_915, 4);
 lean_ctor_release(x_915, 5);
 lean_ctor_release(x_915, 6);
 lean_ctor_release(x_915, 7);
 lean_ctor_release(x_915, 8);
 lean_ctor_release(x_915, 9);
 x_971 = x_915;
} else {
 lean_dec_ref(x_915);
 x_971 = lean_box(0);
}
x_972 = lean_ctor_get(x_916, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_916, 1);
lean_inc(x_973);
x_974 = lean_ctor_get(x_916, 2);
lean_inc(x_974);
x_975 = lean_ctor_get(x_916, 3);
lean_inc(x_975);
x_976 = lean_ctor_get(x_916, 4);
lean_inc(x_976);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 lean_ctor_release(x_916, 2);
 lean_ctor_release(x_916, 3);
 lean_ctor_release(x_916, 4);
 x_977 = x_916;
} else {
 lean_dec_ref(x_916);
 x_977 = lean_box(0);
}
x_978 = lean_unsigned_to_nat(1u);
x_979 = lean_nat_add(x_975, x_978);
lean_dec(x_975);
if (lean_is_scalar(x_977)) {
 x_980 = lean_alloc_ctor(0, 5, 0);
} else {
 x_980 = x_977;
}
lean_ctor_set(x_980, 0, x_972);
lean_ctor_set(x_980, 1, x_973);
lean_ctor_set(x_980, 2, x_974);
lean_ctor_set(x_980, 3, x_979);
lean_ctor_set(x_980, 4, x_976);
if (lean_is_scalar(x_971)) {
 x_981 = lean_alloc_ctor(0, 10, 3);
} else {
 x_981 = x_971;
}
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_959);
lean_ctor_set(x_981, 2, x_960);
lean_ctor_set(x_981, 3, x_961);
lean_ctor_set(x_981, 4, x_962);
lean_ctor_set(x_981, 5, x_963);
lean_ctor_set(x_981, 6, x_964);
lean_ctor_set(x_981, 7, x_965);
lean_ctor_set(x_981, 8, x_966);
lean_ctor_set(x_981, 9, x_970);
lean_ctor_set_uint8(x_981, sizeof(void*)*10, x_967);
lean_ctor_set_uint8(x_981, sizeof(void*)*10 + 1, x_968);
lean_ctor_set_uint8(x_981, sizeof(void*)*10 + 2, x_969);
x_982 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_958);
x_2 = x_913;
x_3 = x_982;
x_4 = x_914;
goto _start;
}
}
}
}
else
{
uint8_t x_997; 
lean_dec(x_3);
lean_dec(x_1);
x_997 = !lean_is_exclusive(x_904);
if (x_997 == 0)
{
return x_904;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_904, 0);
x_999 = lean_ctor_get(x_904, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_904);
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
return x_1000;
}
}
}
case 9:
{
lean_object* x_1001; 
lean_dec(x_8);
lean_inc(x_3);
x_1001 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; 
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
if (lean_obj_tag(x_1002) == 0)
{
uint8_t x_1003; 
lean_dec(x_3);
lean_dec(x_1);
x_1003 = !lean_is_exclusive(x_1001);
if (x_1003 == 0)
{
lean_object* x_1004; lean_object* x_1005; 
x_1004 = lean_ctor_get(x_1001, 0);
lean_dec(x_1004);
x_1005 = lean_box(0);
lean_ctor_set(x_1001, 0, x_1005);
return x_1001;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_1001, 1);
lean_inc(x_1006);
lean_dec(x_1001);
x_1007 = lean_box(0);
x_1008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1006);
return x_1008;
}
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; uint8_t x_1086; 
x_1009 = lean_ctor_get(x_1001, 1);
lean_inc(x_1009);
lean_dec(x_1001);
x_1010 = lean_ctor_get(x_1002, 0);
lean_inc(x_1010);
lean_dec(x_1002);
x_1082 = lean_ctor_get(x_3, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
lean_dec(x_1082);
x_1084 = lean_ctor_get(x_1083, 3);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 4);
lean_inc(x_1085);
lean_dec(x_1083);
x_1086 = lean_nat_dec_eq(x_1084, x_1085);
lean_dec(x_1085);
lean_dec(x_1084);
if (x_1086 == 0)
{
x_1011 = x_1009;
goto block_1081;
}
else
{
lean_object* x_1087; lean_object* x_1088; 
x_1087 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_1088 = l_Lean_Elab_Tactic_throwError___rarg(x_1087, x_3, x_1009);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; 
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
lean_dec(x_1088);
x_1011 = x_1089;
goto block_1081;
}
else
{
uint8_t x_1090; 
lean_dec(x_1010);
lean_dec(x_3);
lean_dec(x_1);
x_1090 = !lean_is_exclusive(x_1088);
if (x_1090 == 0)
{
return x_1088;
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1091 = lean_ctor_get(x_1088, 0);
x_1092 = lean_ctor_get(x_1088, 1);
lean_inc(x_1092);
lean_inc(x_1091);
lean_dec(x_1088);
x_1093 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1093, 0, x_1091);
lean_ctor_set(x_1093, 1, x_1092);
return x_1093;
}
}
}
block_1081:
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
x_1012 = lean_ctor_get(x_3, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = !lean_is_exclusive(x_3);
if (x_1014 == 0)
{
lean_object* x_1015; uint8_t x_1016; 
x_1015 = lean_ctor_get(x_3, 0);
lean_dec(x_1015);
x_1016 = !lean_is_exclusive(x_1012);
if (x_1016 == 0)
{
lean_object* x_1017; uint8_t x_1018; 
x_1017 = lean_ctor_get(x_1012, 0);
lean_dec(x_1017);
x_1018 = !lean_is_exclusive(x_1013);
if (x_1018 == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_1013, 3);
x_1020 = lean_unsigned_to_nat(1u);
x_1021 = lean_nat_add(x_1019, x_1020);
lean_dec(x_1019);
lean_ctor_set(x_1013, 3, x_1021);
x_2 = x_1010;
x_4 = x_1011;
goto _start;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1023 = lean_ctor_get(x_1013, 0);
x_1024 = lean_ctor_get(x_1013, 1);
x_1025 = lean_ctor_get(x_1013, 2);
x_1026 = lean_ctor_get(x_1013, 3);
x_1027 = lean_ctor_get(x_1013, 4);
lean_inc(x_1027);
lean_inc(x_1026);
lean_inc(x_1025);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_1013);
x_1028 = lean_unsigned_to_nat(1u);
x_1029 = lean_nat_add(x_1026, x_1028);
lean_dec(x_1026);
x_1030 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1030, 0, x_1023);
lean_ctor_set(x_1030, 1, x_1024);
lean_ctor_set(x_1030, 2, x_1025);
lean_ctor_set(x_1030, 3, x_1029);
lean_ctor_set(x_1030, 4, x_1027);
lean_ctor_set(x_1012, 0, x_1030);
x_2 = x_1010;
x_4 = x_1011;
goto _start;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; uint8_t x_1040; uint8_t x_1041; uint8_t x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1032 = lean_ctor_get(x_1012, 1);
x_1033 = lean_ctor_get(x_1012, 2);
x_1034 = lean_ctor_get(x_1012, 3);
x_1035 = lean_ctor_get(x_1012, 4);
x_1036 = lean_ctor_get(x_1012, 5);
x_1037 = lean_ctor_get(x_1012, 6);
x_1038 = lean_ctor_get(x_1012, 7);
x_1039 = lean_ctor_get(x_1012, 8);
x_1040 = lean_ctor_get_uint8(x_1012, sizeof(void*)*10);
x_1041 = lean_ctor_get_uint8(x_1012, sizeof(void*)*10 + 1);
x_1042 = lean_ctor_get_uint8(x_1012, sizeof(void*)*10 + 2);
x_1043 = lean_ctor_get(x_1012, 9);
lean_inc(x_1043);
lean_inc(x_1039);
lean_inc(x_1038);
lean_inc(x_1037);
lean_inc(x_1036);
lean_inc(x_1035);
lean_inc(x_1034);
lean_inc(x_1033);
lean_inc(x_1032);
lean_dec(x_1012);
x_1044 = lean_ctor_get(x_1013, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1013, 1);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1013, 2);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1013, 3);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1013, 4);
lean_inc(x_1048);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 lean_ctor_release(x_1013, 2);
 lean_ctor_release(x_1013, 3);
 lean_ctor_release(x_1013, 4);
 x_1049 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1049 = lean_box(0);
}
x_1050 = lean_unsigned_to_nat(1u);
x_1051 = lean_nat_add(x_1047, x_1050);
lean_dec(x_1047);
if (lean_is_scalar(x_1049)) {
 x_1052 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1052 = x_1049;
}
lean_ctor_set(x_1052, 0, x_1044);
lean_ctor_set(x_1052, 1, x_1045);
lean_ctor_set(x_1052, 2, x_1046);
lean_ctor_set(x_1052, 3, x_1051);
lean_ctor_set(x_1052, 4, x_1048);
x_1053 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1032);
lean_ctor_set(x_1053, 2, x_1033);
lean_ctor_set(x_1053, 3, x_1034);
lean_ctor_set(x_1053, 4, x_1035);
lean_ctor_set(x_1053, 5, x_1036);
lean_ctor_set(x_1053, 6, x_1037);
lean_ctor_set(x_1053, 7, x_1038);
lean_ctor_set(x_1053, 8, x_1039);
lean_ctor_set(x_1053, 9, x_1043);
lean_ctor_set_uint8(x_1053, sizeof(void*)*10, x_1040);
lean_ctor_set_uint8(x_1053, sizeof(void*)*10 + 1, x_1041);
lean_ctor_set_uint8(x_1053, sizeof(void*)*10 + 2, x_1042);
lean_ctor_set(x_3, 0, x_1053);
x_2 = x_1010;
x_4 = x_1011;
goto _start;
}
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; uint8_t x_1065; uint8_t x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1055 = lean_ctor_get(x_3, 1);
lean_inc(x_1055);
lean_dec(x_3);
x_1056 = lean_ctor_get(x_1012, 1);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1012, 2);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1012, 3);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1012, 4);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1012, 5);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1012, 6);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1012, 7);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1012, 8);
lean_inc(x_1063);
x_1064 = lean_ctor_get_uint8(x_1012, sizeof(void*)*10);
x_1065 = lean_ctor_get_uint8(x_1012, sizeof(void*)*10 + 1);
x_1066 = lean_ctor_get_uint8(x_1012, sizeof(void*)*10 + 2);
x_1067 = lean_ctor_get(x_1012, 9);
lean_inc(x_1067);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 lean_ctor_release(x_1012, 2);
 lean_ctor_release(x_1012, 3);
 lean_ctor_release(x_1012, 4);
 lean_ctor_release(x_1012, 5);
 lean_ctor_release(x_1012, 6);
 lean_ctor_release(x_1012, 7);
 lean_ctor_release(x_1012, 8);
 lean_ctor_release(x_1012, 9);
 x_1068 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1068 = lean_box(0);
}
x_1069 = lean_ctor_get(x_1013, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1013, 1);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1013, 2);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1013, 3);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1013, 4);
lean_inc(x_1073);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 lean_ctor_release(x_1013, 2);
 lean_ctor_release(x_1013, 3);
 lean_ctor_release(x_1013, 4);
 x_1074 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1074 = lean_box(0);
}
x_1075 = lean_unsigned_to_nat(1u);
x_1076 = lean_nat_add(x_1072, x_1075);
lean_dec(x_1072);
if (lean_is_scalar(x_1074)) {
 x_1077 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1077 = x_1074;
}
lean_ctor_set(x_1077, 0, x_1069);
lean_ctor_set(x_1077, 1, x_1070);
lean_ctor_set(x_1077, 2, x_1071);
lean_ctor_set(x_1077, 3, x_1076);
lean_ctor_set(x_1077, 4, x_1073);
if (lean_is_scalar(x_1068)) {
 x_1078 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1078 = x_1068;
}
lean_ctor_set(x_1078, 0, x_1077);
lean_ctor_set(x_1078, 1, x_1056);
lean_ctor_set(x_1078, 2, x_1057);
lean_ctor_set(x_1078, 3, x_1058);
lean_ctor_set(x_1078, 4, x_1059);
lean_ctor_set(x_1078, 5, x_1060);
lean_ctor_set(x_1078, 6, x_1061);
lean_ctor_set(x_1078, 7, x_1062);
lean_ctor_set(x_1078, 8, x_1063);
lean_ctor_set(x_1078, 9, x_1067);
lean_ctor_set_uint8(x_1078, sizeof(void*)*10, x_1064);
lean_ctor_set_uint8(x_1078, sizeof(void*)*10 + 1, x_1065);
lean_ctor_set_uint8(x_1078, sizeof(void*)*10 + 2, x_1066);
x_1079 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1079, 0, x_1078);
lean_ctor_set(x_1079, 1, x_1055);
x_2 = x_1010;
x_3 = x_1079;
x_4 = x_1011;
goto _start;
}
}
}
}
else
{
uint8_t x_1094; 
lean_dec(x_3);
lean_dec(x_1);
x_1094 = !lean_is_exclusive(x_1001);
if (x_1094 == 0)
{
return x_1001;
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1095 = lean_ctor_get(x_1001, 0);
x_1096 = lean_ctor_get(x_1001, 1);
lean_inc(x_1096);
lean_inc(x_1095);
lean_dec(x_1001);
x_1097 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1097, 0, x_1095);
lean_ctor_set(x_1097, 1, x_1096);
return x_1097;
}
}
}
case 10:
{
lean_object* x_1098; 
lean_dec(x_8);
lean_inc(x_3);
x_1098 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; 
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
if (lean_obj_tag(x_1099) == 0)
{
uint8_t x_1100; 
lean_dec(x_3);
lean_dec(x_1);
x_1100 = !lean_is_exclusive(x_1098);
if (x_1100 == 0)
{
lean_object* x_1101; lean_object* x_1102; 
x_1101 = lean_ctor_get(x_1098, 0);
lean_dec(x_1101);
x_1102 = lean_box(0);
lean_ctor_set(x_1098, 0, x_1102);
return x_1098;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1103 = lean_ctor_get(x_1098, 1);
lean_inc(x_1103);
lean_dec(x_1098);
x_1104 = lean_box(0);
x_1105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1105, 0, x_1104);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
else
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
x_1106 = lean_ctor_get(x_1098, 1);
lean_inc(x_1106);
lean_dec(x_1098);
x_1107 = lean_ctor_get(x_1099, 0);
lean_inc(x_1107);
lean_dec(x_1099);
x_1179 = lean_ctor_get(x_3, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
lean_dec(x_1179);
x_1181 = lean_ctor_get(x_1180, 3);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1180, 4);
lean_inc(x_1182);
lean_dec(x_1180);
x_1183 = lean_nat_dec_eq(x_1181, x_1182);
lean_dec(x_1182);
lean_dec(x_1181);
if (x_1183 == 0)
{
x_1108 = x_1106;
goto block_1178;
}
else
{
lean_object* x_1184; lean_object* x_1185; 
x_1184 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_1185 = l_Lean_Elab_Tactic_throwError___rarg(x_1184, x_3, x_1106);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; 
x_1186 = lean_ctor_get(x_1185, 1);
lean_inc(x_1186);
lean_dec(x_1185);
x_1108 = x_1186;
goto block_1178;
}
else
{
uint8_t x_1187; 
lean_dec(x_1107);
lean_dec(x_3);
lean_dec(x_1);
x_1187 = !lean_is_exclusive(x_1185);
if (x_1187 == 0)
{
return x_1185;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1185, 0);
x_1189 = lean_ctor_get(x_1185, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1185);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
block_1178:
{
lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
x_1109 = lean_ctor_get(x_3, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1109, 0);
lean_inc(x_1110);
x_1111 = !lean_is_exclusive(x_3);
if (x_1111 == 0)
{
lean_object* x_1112; uint8_t x_1113; 
x_1112 = lean_ctor_get(x_3, 0);
lean_dec(x_1112);
x_1113 = !lean_is_exclusive(x_1109);
if (x_1113 == 0)
{
lean_object* x_1114; uint8_t x_1115; 
x_1114 = lean_ctor_get(x_1109, 0);
lean_dec(x_1114);
x_1115 = !lean_is_exclusive(x_1110);
if (x_1115 == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1110, 3);
x_1117 = lean_unsigned_to_nat(1u);
x_1118 = lean_nat_add(x_1116, x_1117);
lean_dec(x_1116);
lean_ctor_set(x_1110, 3, x_1118);
x_2 = x_1107;
x_4 = x_1108;
goto _start;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1120 = lean_ctor_get(x_1110, 0);
x_1121 = lean_ctor_get(x_1110, 1);
x_1122 = lean_ctor_get(x_1110, 2);
x_1123 = lean_ctor_get(x_1110, 3);
x_1124 = lean_ctor_get(x_1110, 4);
lean_inc(x_1124);
lean_inc(x_1123);
lean_inc(x_1122);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1110);
x_1125 = lean_unsigned_to_nat(1u);
x_1126 = lean_nat_add(x_1123, x_1125);
lean_dec(x_1123);
x_1127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1127, 0, x_1120);
lean_ctor_set(x_1127, 1, x_1121);
lean_ctor_set(x_1127, 2, x_1122);
lean_ctor_set(x_1127, 3, x_1126);
lean_ctor_set(x_1127, 4, x_1124);
lean_ctor_set(x_1109, 0, x_1127);
x_2 = x_1107;
x_4 = x_1108;
goto _start;
}
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; uint8_t x_1137; uint8_t x_1138; uint8_t x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1129 = lean_ctor_get(x_1109, 1);
x_1130 = lean_ctor_get(x_1109, 2);
x_1131 = lean_ctor_get(x_1109, 3);
x_1132 = lean_ctor_get(x_1109, 4);
x_1133 = lean_ctor_get(x_1109, 5);
x_1134 = lean_ctor_get(x_1109, 6);
x_1135 = lean_ctor_get(x_1109, 7);
x_1136 = lean_ctor_get(x_1109, 8);
x_1137 = lean_ctor_get_uint8(x_1109, sizeof(void*)*10);
x_1138 = lean_ctor_get_uint8(x_1109, sizeof(void*)*10 + 1);
x_1139 = lean_ctor_get_uint8(x_1109, sizeof(void*)*10 + 2);
x_1140 = lean_ctor_get(x_1109, 9);
lean_inc(x_1140);
lean_inc(x_1136);
lean_inc(x_1135);
lean_inc(x_1134);
lean_inc(x_1133);
lean_inc(x_1132);
lean_inc(x_1131);
lean_inc(x_1130);
lean_inc(x_1129);
lean_dec(x_1109);
x_1141 = lean_ctor_get(x_1110, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1110, 1);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1110, 2);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1110, 3);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1110, 4);
lean_inc(x_1145);
if (lean_is_exclusive(x_1110)) {
 lean_ctor_release(x_1110, 0);
 lean_ctor_release(x_1110, 1);
 lean_ctor_release(x_1110, 2);
 lean_ctor_release(x_1110, 3);
 lean_ctor_release(x_1110, 4);
 x_1146 = x_1110;
} else {
 lean_dec_ref(x_1110);
 x_1146 = lean_box(0);
}
x_1147 = lean_unsigned_to_nat(1u);
x_1148 = lean_nat_add(x_1144, x_1147);
lean_dec(x_1144);
if (lean_is_scalar(x_1146)) {
 x_1149 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1149 = x_1146;
}
lean_ctor_set(x_1149, 0, x_1141);
lean_ctor_set(x_1149, 1, x_1142);
lean_ctor_set(x_1149, 2, x_1143);
lean_ctor_set(x_1149, 3, x_1148);
lean_ctor_set(x_1149, 4, x_1145);
x_1150 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_1129);
lean_ctor_set(x_1150, 2, x_1130);
lean_ctor_set(x_1150, 3, x_1131);
lean_ctor_set(x_1150, 4, x_1132);
lean_ctor_set(x_1150, 5, x_1133);
lean_ctor_set(x_1150, 6, x_1134);
lean_ctor_set(x_1150, 7, x_1135);
lean_ctor_set(x_1150, 8, x_1136);
lean_ctor_set(x_1150, 9, x_1140);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10, x_1137);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10 + 1, x_1138);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10 + 2, x_1139);
lean_ctor_set(x_3, 0, x_1150);
x_2 = x_1107;
x_4 = x_1108;
goto _start;
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; uint8_t x_1161; uint8_t x_1162; uint8_t x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1152 = lean_ctor_get(x_3, 1);
lean_inc(x_1152);
lean_dec(x_3);
x_1153 = lean_ctor_get(x_1109, 1);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1109, 2);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1109, 3);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1109, 4);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1109, 5);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1109, 6);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1109, 7);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1109, 8);
lean_inc(x_1160);
x_1161 = lean_ctor_get_uint8(x_1109, sizeof(void*)*10);
x_1162 = lean_ctor_get_uint8(x_1109, sizeof(void*)*10 + 1);
x_1163 = lean_ctor_get_uint8(x_1109, sizeof(void*)*10 + 2);
x_1164 = lean_ctor_get(x_1109, 9);
lean_inc(x_1164);
if (lean_is_exclusive(x_1109)) {
 lean_ctor_release(x_1109, 0);
 lean_ctor_release(x_1109, 1);
 lean_ctor_release(x_1109, 2);
 lean_ctor_release(x_1109, 3);
 lean_ctor_release(x_1109, 4);
 lean_ctor_release(x_1109, 5);
 lean_ctor_release(x_1109, 6);
 lean_ctor_release(x_1109, 7);
 lean_ctor_release(x_1109, 8);
 lean_ctor_release(x_1109, 9);
 x_1165 = x_1109;
} else {
 lean_dec_ref(x_1109);
 x_1165 = lean_box(0);
}
x_1166 = lean_ctor_get(x_1110, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1110, 1);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1110, 2);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1110, 3);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1110, 4);
lean_inc(x_1170);
if (lean_is_exclusive(x_1110)) {
 lean_ctor_release(x_1110, 0);
 lean_ctor_release(x_1110, 1);
 lean_ctor_release(x_1110, 2);
 lean_ctor_release(x_1110, 3);
 lean_ctor_release(x_1110, 4);
 x_1171 = x_1110;
} else {
 lean_dec_ref(x_1110);
 x_1171 = lean_box(0);
}
x_1172 = lean_unsigned_to_nat(1u);
x_1173 = lean_nat_add(x_1169, x_1172);
lean_dec(x_1169);
if (lean_is_scalar(x_1171)) {
 x_1174 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1174 = x_1171;
}
lean_ctor_set(x_1174, 0, x_1166);
lean_ctor_set(x_1174, 1, x_1167);
lean_ctor_set(x_1174, 2, x_1168);
lean_ctor_set(x_1174, 3, x_1173);
lean_ctor_set(x_1174, 4, x_1170);
if (lean_is_scalar(x_1165)) {
 x_1175 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1175 = x_1165;
}
lean_ctor_set(x_1175, 0, x_1174);
lean_ctor_set(x_1175, 1, x_1153);
lean_ctor_set(x_1175, 2, x_1154);
lean_ctor_set(x_1175, 3, x_1155);
lean_ctor_set(x_1175, 4, x_1156);
lean_ctor_set(x_1175, 5, x_1157);
lean_ctor_set(x_1175, 6, x_1158);
lean_ctor_set(x_1175, 7, x_1159);
lean_ctor_set(x_1175, 8, x_1160);
lean_ctor_set(x_1175, 9, x_1164);
lean_ctor_set_uint8(x_1175, sizeof(void*)*10, x_1161);
lean_ctor_set_uint8(x_1175, sizeof(void*)*10 + 1, x_1162);
lean_ctor_set_uint8(x_1175, sizeof(void*)*10 + 2, x_1163);
x_1176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1176, 0, x_1175);
lean_ctor_set(x_1176, 1, x_1152);
x_2 = x_1107;
x_3 = x_1176;
x_4 = x_1108;
goto _start;
}
}
}
}
else
{
uint8_t x_1191; 
lean_dec(x_3);
lean_dec(x_1);
x_1191 = !lean_is_exclusive(x_1098);
if (x_1191 == 0)
{
return x_1098;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1098, 0);
x_1193 = lean_ctor_get(x_1098, 1);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_1098);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
}
case 11:
{
lean_object* x_1195; 
lean_dec(x_8);
lean_inc(x_3);
x_1195 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
if (lean_obj_tag(x_1196) == 0)
{
uint8_t x_1197; 
lean_dec(x_3);
lean_dec(x_1);
x_1197 = !lean_is_exclusive(x_1195);
if (x_1197 == 0)
{
lean_object* x_1198; lean_object* x_1199; 
x_1198 = lean_ctor_get(x_1195, 0);
lean_dec(x_1198);
x_1199 = lean_box(0);
lean_ctor_set(x_1195, 0, x_1199);
return x_1195;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1195, 1);
lean_inc(x_1200);
lean_dec(x_1195);
x_1201 = lean_box(0);
x_1202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1202, 0, x_1201);
lean_ctor_set(x_1202, 1, x_1200);
return x_1202;
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; uint8_t x_1280; 
x_1203 = lean_ctor_get(x_1195, 1);
lean_inc(x_1203);
lean_dec(x_1195);
x_1204 = lean_ctor_get(x_1196, 0);
lean_inc(x_1204);
lean_dec(x_1196);
x_1276 = lean_ctor_get(x_3, 0);
lean_inc(x_1276);
x_1277 = lean_ctor_get(x_1276, 0);
lean_inc(x_1277);
lean_dec(x_1276);
x_1278 = lean_ctor_get(x_1277, 3);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 4);
lean_inc(x_1279);
lean_dec(x_1277);
x_1280 = lean_nat_dec_eq(x_1278, x_1279);
lean_dec(x_1279);
lean_dec(x_1278);
if (x_1280 == 0)
{
x_1205 = x_1203;
goto block_1275;
}
else
{
lean_object* x_1281; lean_object* x_1282; 
x_1281 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_1282 = l_Lean_Elab_Tactic_throwError___rarg(x_1281, x_3, x_1203);
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; 
x_1283 = lean_ctor_get(x_1282, 1);
lean_inc(x_1283);
lean_dec(x_1282);
x_1205 = x_1283;
goto block_1275;
}
else
{
uint8_t x_1284; 
lean_dec(x_1204);
lean_dec(x_3);
lean_dec(x_1);
x_1284 = !lean_is_exclusive(x_1282);
if (x_1284 == 0)
{
return x_1282;
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1285 = lean_ctor_get(x_1282, 0);
x_1286 = lean_ctor_get(x_1282, 1);
lean_inc(x_1286);
lean_inc(x_1285);
lean_dec(x_1282);
x_1287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1287, 0, x_1285);
lean_ctor_set(x_1287, 1, x_1286);
return x_1287;
}
}
}
block_1275:
{
lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; 
x_1206 = lean_ctor_get(x_3, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = !lean_is_exclusive(x_3);
if (x_1208 == 0)
{
lean_object* x_1209; uint8_t x_1210; 
x_1209 = lean_ctor_get(x_3, 0);
lean_dec(x_1209);
x_1210 = !lean_is_exclusive(x_1206);
if (x_1210 == 0)
{
lean_object* x_1211; uint8_t x_1212; 
x_1211 = lean_ctor_get(x_1206, 0);
lean_dec(x_1211);
x_1212 = !lean_is_exclusive(x_1207);
if (x_1212 == 0)
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1207, 3);
x_1214 = lean_unsigned_to_nat(1u);
x_1215 = lean_nat_add(x_1213, x_1214);
lean_dec(x_1213);
lean_ctor_set(x_1207, 3, x_1215);
x_2 = x_1204;
x_4 = x_1205;
goto _start;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1217 = lean_ctor_get(x_1207, 0);
x_1218 = lean_ctor_get(x_1207, 1);
x_1219 = lean_ctor_get(x_1207, 2);
x_1220 = lean_ctor_get(x_1207, 3);
x_1221 = lean_ctor_get(x_1207, 4);
lean_inc(x_1221);
lean_inc(x_1220);
lean_inc(x_1219);
lean_inc(x_1218);
lean_inc(x_1217);
lean_dec(x_1207);
x_1222 = lean_unsigned_to_nat(1u);
x_1223 = lean_nat_add(x_1220, x_1222);
lean_dec(x_1220);
x_1224 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1224, 0, x_1217);
lean_ctor_set(x_1224, 1, x_1218);
lean_ctor_set(x_1224, 2, x_1219);
lean_ctor_set(x_1224, 3, x_1223);
lean_ctor_set(x_1224, 4, x_1221);
lean_ctor_set(x_1206, 0, x_1224);
x_2 = x_1204;
x_4 = x_1205;
goto _start;
}
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; uint8_t x_1235; uint8_t x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1226 = lean_ctor_get(x_1206, 1);
x_1227 = lean_ctor_get(x_1206, 2);
x_1228 = lean_ctor_get(x_1206, 3);
x_1229 = lean_ctor_get(x_1206, 4);
x_1230 = lean_ctor_get(x_1206, 5);
x_1231 = lean_ctor_get(x_1206, 6);
x_1232 = lean_ctor_get(x_1206, 7);
x_1233 = lean_ctor_get(x_1206, 8);
x_1234 = lean_ctor_get_uint8(x_1206, sizeof(void*)*10);
x_1235 = lean_ctor_get_uint8(x_1206, sizeof(void*)*10 + 1);
x_1236 = lean_ctor_get_uint8(x_1206, sizeof(void*)*10 + 2);
x_1237 = lean_ctor_get(x_1206, 9);
lean_inc(x_1237);
lean_inc(x_1233);
lean_inc(x_1232);
lean_inc(x_1231);
lean_inc(x_1230);
lean_inc(x_1229);
lean_inc(x_1228);
lean_inc(x_1227);
lean_inc(x_1226);
lean_dec(x_1206);
x_1238 = lean_ctor_get(x_1207, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1207, 1);
lean_inc(x_1239);
x_1240 = lean_ctor_get(x_1207, 2);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1207, 3);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1207, 4);
lean_inc(x_1242);
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 lean_ctor_release(x_1207, 1);
 lean_ctor_release(x_1207, 2);
 lean_ctor_release(x_1207, 3);
 lean_ctor_release(x_1207, 4);
 x_1243 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1243 = lean_box(0);
}
x_1244 = lean_unsigned_to_nat(1u);
x_1245 = lean_nat_add(x_1241, x_1244);
lean_dec(x_1241);
if (lean_is_scalar(x_1243)) {
 x_1246 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1246 = x_1243;
}
lean_ctor_set(x_1246, 0, x_1238);
lean_ctor_set(x_1246, 1, x_1239);
lean_ctor_set(x_1246, 2, x_1240);
lean_ctor_set(x_1246, 3, x_1245);
lean_ctor_set(x_1246, 4, x_1242);
x_1247 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1247, 0, x_1246);
lean_ctor_set(x_1247, 1, x_1226);
lean_ctor_set(x_1247, 2, x_1227);
lean_ctor_set(x_1247, 3, x_1228);
lean_ctor_set(x_1247, 4, x_1229);
lean_ctor_set(x_1247, 5, x_1230);
lean_ctor_set(x_1247, 6, x_1231);
lean_ctor_set(x_1247, 7, x_1232);
lean_ctor_set(x_1247, 8, x_1233);
lean_ctor_set(x_1247, 9, x_1237);
lean_ctor_set_uint8(x_1247, sizeof(void*)*10, x_1234);
lean_ctor_set_uint8(x_1247, sizeof(void*)*10 + 1, x_1235);
lean_ctor_set_uint8(x_1247, sizeof(void*)*10 + 2, x_1236);
lean_ctor_set(x_3, 0, x_1247);
x_2 = x_1204;
x_4 = x_1205;
goto _start;
}
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; uint8_t x_1258; uint8_t x_1259; uint8_t x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1249 = lean_ctor_get(x_3, 1);
lean_inc(x_1249);
lean_dec(x_3);
x_1250 = lean_ctor_get(x_1206, 1);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1206, 2);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1206, 3);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1206, 4);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1206, 5);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1206, 6);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1206, 7);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_1206, 8);
lean_inc(x_1257);
x_1258 = lean_ctor_get_uint8(x_1206, sizeof(void*)*10);
x_1259 = lean_ctor_get_uint8(x_1206, sizeof(void*)*10 + 1);
x_1260 = lean_ctor_get_uint8(x_1206, sizeof(void*)*10 + 2);
x_1261 = lean_ctor_get(x_1206, 9);
lean_inc(x_1261);
if (lean_is_exclusive(x_1206)) {
 lean_ctor_release(x_1206, 0);
 lean_ctor_release(x_1206, 1);
 lean_ctor_release(x_1206, 2);
 lean_ctor_release(x_1206, 3);
 lean_ctor_release(x_1206, 4);
 lean_ctor_release(x_1206, 5);
 lean_ctor_release(x_1206, 6);
 lean_ctor_release(x_1206, 7);
 lean_ctor_release(x_1206, 8);
 lean_ctor_release(x_1206, 9);
 x_1262 = x_1206;
} else {
 lean_dec_ref(x_1206);
 x_1262 = lean_box(0);
}
x_1263 = lean_ctor_get(x_1207, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1207, 1);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1207, 2);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1207, 3);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1207, 4);
lean_inc(x_1267);
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 lean_ctor_release(x_1207, 1);
 lean_ctor_release(x_1207, 2);
 lean_ctor_release(x_1207, 3);
 lean_ctor_release(x_1207, 4);
 x_1268 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1268 = lean_box(0);
}
x_1269 = lean_unsigned_to_nat(1u);
x_1270 = lean_nat_add(x_1266, x_1269);
lean_dec(x_1266);
if (lean_is_scalar(x_1268)) {
 x_1271 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1271 = x_1268;
}
lean_ctor_set(x_1271, 0, x_1263);
lean_ctor_set(x_1271, 1, x_1264);
lean_ctor_set(x_1271, 2, x_1265);
lean_ctor_set(x_1271, 3, x_1270);
lean_ctor_set(x_1271, 4, x_1267);
if (lean_is_scalar(x_1262)) {
 x_1272 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1272 = x_1262;
}
lean_ctor_set(x_1272, 0, x_1271);
lean_ctor_set(x_1272, 1, x_1250);
lean_ctor_set(x_1272, 2, x_1251);
lean_ctor_set(x_1272, 3, x_1252);
lean_ctor_set(x_1272, 4, x_1253);
lean_ctor_set(x_1272, 5, x_1254);
lean_ctor_set(x_1272, 6, x_1255);
lean_ctor_set(x_1272, 7, x_1256);
lean_ctor_set(x_1272, 8, x_1257);
lean_ctor_set(x_1272, 9, x_1261);
lean_ctor_set_uint8(x_1272, sizeof(void*)*10, x_1258);
lean_ctor_set_uint8(x_1272, sizeof(void*)*10 + 1, x_1259);
lean_ctor_set_uint8(x_1272, sizeof(void*)*10 + 2, x_1260);
x_1273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1273, 0, x_1272);
lean_ctor_set(x_1273, 1, x_1249);
x_2 = x_1204;
x_3 = x_1273;
x_4 = x_1205;
goto _start;
}
}
}
}
else
{
uint8_t x_1288; 
lean_dec(x_3);
lean_dec(x_1);
x_1288 = !lean_is_exclusive(x_1195);
if (x_1288 == 0)
{
return x_1195;
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
x_1289 = lean_ctor_get(x_1195, 0);
x_1290 = lean_ctor_get(x_1195, 1);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_1195);
x_1291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1291, 0, x_1289);
lean_ctor_set(x_1291, 1, x_1290);
return x_1291;
}
}
}
default: 
{
lean_object* x_1292; 
lean_dec(x_8);
lean_inc(x_3);
x_1292 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; 
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
if (lean_obj_tag(x_1293) == 0)
{
uint8_t x_1294; 
lean_dec(x_3);
lean_dec(x_1);
x_1294 = !lean_is_exclusive(x_1292);
if (x_1294 == 0)
{
lean_object* x_1295; lean_object* x_1296; 
x_1295 = lean_ctor_get(x_1292, 0);
lean_dec(x_1295);
x_1296 = lean_box(0);
lean_ctor_set(x_1292, 0, x_1296);
return x_1292;
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1297 = lean_ctor_get(x_1292, 1);
lean_inc(x_1297);
lean_dec(x_1292);
x_1298 = lean_box(0);
x_1299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1299, 0, x_1298);
lean_ctor_set(x_1299, 1, x_1297);
return x_1299;
}
}
else
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; uint8_t x_1377; 
x_1300 = lean_ctor_get(x_1292, 1);
lean_inc(x_1300);
lean_dec(x_1292);
x_1301 = lean_ctor_get(x_1293, 0);
lean_inc(x_1301);
lean_dec(x_1293);
x_1373 = lean_ctor_get(x_3, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1373, 0);
lean_inc(x_1374);
lean_dec(x_1373);
x_1375 = lean_ctor_get(x_1374, 3);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1374, 4);
lean_inc(x_1376);
lean_dec(x_1374);
x_1377 = lean_nat_dec_eq(x_1375, x_1376);
lean_dec(x_1376);
lean_dec(x_1375);
if (x_1377 == 0)
{
x_1302 = x_1300;
goto block_1372;
}
else
{
lean_object* x_1378; lean_object* x_1379; 
x_1378 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_1379 = l_Lean_Elab_Tactic_throwError___rarg(x_1378, x_3, x_1300);
if (lean_obj_tag(x_1379) == 0)
{
lean_object* x_1380; 
x_1380 = lean_ctor_get(x_1379, 1);
lean_inc(x_1380);
lean_dec(x_1379);
x_1302 = x_1380;
goto block_1372;
}
else
{
uint8_t x_1381; 
lean_dec(x_1301);
lean_dec(x_3);
lean_dec(x_1);
x_1381 = !lean_is_exclusive(x_1379);
if (x_1381 == 0)
{
return x_1379;
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
x_1382 = lean_ctor_get(x_1379, 0);
x_1383 = lean_ctor_get(x_1379, 1);
lean_inc(x_1383);
lean_inc(x_1382);
lean_dec(x_1379);
x_1384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1384, 0, x_1382);
lean_ctor_set(x_1384, 1, x_1383);
return x_1384;
}
}
}
block_1372:
{
lean_object* x_1303; lean_object* x_1304; uint8_t x_1305; 
x_1303 = lean_ctor_get(x_3, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = !lean_is_exclusive(x_3);
if (x_1305 == 0)
{
lean_object* x_1306; uint8_t x_1307; 
x_1306 = lean_ctor_get(x_3, 0);
lean_dec(x_1306);
x_1307 = !lean_is_exclusive(x_1303);
if (x_1307 == 0)
{
lean_object* x_1308; uint8_t x_1309; 
x_1308 = lean_ctor_get(x_1303, 0);
lean_dec(x_1308);
x_1309 = !lean_is_exclusive(x_1304);
if (x_1309 == 0)
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1310 = lean_ctor_get(x_1304, 3);
x_1311 = lean_unsigned_to_nat(1u);
x_1312 = lean_nat_add(x_1310, x_1311);
lean_dec(x_1310);
lean_ctor_set(x_1304, 3, x_1312);
x_2 = x_1301;
x_4 = x_1302;
goto _start;
}
else
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
x_1314 = lean_ctor_get(x_1304, 0);
x_1315 = lean_ctor_get(x_1304, 1);
x_1316 = lean_ctor_get(x_1304, 2);
x_1317 = lean_ctor_get(x_1304, 3);
x_1318 = lean_ctor_get(x_1304, 4);
lean_inc(x_1318);
lean_inc(x_1317);
lean_inc(x_1316);
lean_inc(x_1315);
lean_inc(x_1314);
lean_dec(x_1304);
x_1319 = lean_unsigned_to_nat(1u);
x_1320 = lean_nat_add(x_1317, x_1319);
lean_dec(x_1317);
x_1321 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1321, 0, x_1314);
lean_ctor_set(x_1321, 1, x_1315);
lean_ctor_set(x_1321, 2, x_1316);
lean_ctor_set(x_1321, 3, x_1320);
lean_ctor_set(x_1321, 4, x_1318);
lean_ctor_set(x_1303, 0, x_1321);
x_2 = x_1301;
x_4 = x_1302;
goto _start;
}
}
else
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; uint8_t x_1331; uint8_t x_1332; uint8_t x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1323 = lean_ctor_get(x_1303, 1);
x_1324 = lean_ctor_get(x_1303, 2);
x_1325 = lean_ctor_get(x_1303, 3);
x_1326 = lean_ctor_get(x_1303, 4);
x_1327 = lean_ctor_get(x_1303, 5);
x_1328 = lean_ctor_get(x_1303, 6);
x_1329 = lean_ctor_get(x_1303, 7);
x_1330 = lean_ctor_get(x_1303, 8);
x_1331 = lean_ctor_get_uint8(x_1303, sizeof(void*)*10);
x_1332 = lean_ctor_get_uint8(x_1303, sizeof(void*)*10 + 1);
x_1333 = lean_ctor_get_uint8(x_1303, sizeof(void*)*10 + 2);
x_1334 = lean_ctor_get(x_1303, 9);
lean_inc(x_1334);
lean_inc(x_1330);
lean_inc(x_1329);
lean_inc(x_1328);
lean_inc(x_1327);
lean_inc(x_1326);
lean_inc(x_1325);
lean_inc(x_1324);
lean_inc(x_1323);
lean_dec(x_1303);
x_1335 = lean_ctor_get(x_1304, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1304, 1);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1304, 2);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1304, 3);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1304, 4);
lean_inc(x_1339);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 lean_ctor_release(x_1304, 2);
 lean_ctor_release(x_1304, 3);
 lean_ctor_release(x_1304, 4);
 x_1340 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1340 = lean_box(0);
}
x_1341 = lean_unsigned_to_nat(1u);
x_1342 = lean_nat_add(x_1338, x_1341);
lean_dec(x_1338);
if (lean_is_scalar(x_1340)) {
 x_1343 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1343 = x_1340;
}
lean_ctor_set(x_1343, 0, x_1335);
lean_ctor_set(x_1343, 1, x_1336);
lean_ctor_set(x_1343, 2, x_1337);
lean_ctor_set(x_1343, 3, x_1342);
lean_ctor_set(x_1343, 4, x_1339);
x_1344 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1344, 0, x_1343);
lean_ctor_set(x_1344, 1, x_1323);
lean_ctor_set(x_1344, 2, x_1324);
lean_ctor_set(x_1344, 3, x_1325);
lean_ctor_set(x_1344, 4, x_1326);
lean_ctor_set(x_1344, 5, x_1327);
lean_ctor_set(x_1344, 6, x_1328);
lean_ctor_set(x_1344, 7, x_1329);
lean_ctor_set(x_1344, 8, x_1330);
lean_ctor_set(x_1344, 9, x_1334);
lean_ctor_set_uint8(x_1344, sizeof(void*)*10, x_1331);
lean_ctor_set_uint8(x_1344, sizeof(void*)*10 + 1, x_1332);
lean_ctor_set_uint8(x_1344, sizeof(void*)*10 + 2, x_1333);
lean_ctor_set(x_3, 0, x_1344);
x_2 = x_1301;
x_4 = x_1302;
goto _start;
}
}
else
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; uint8_t x_1355; uint8_t x_1356; uint8_t x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
x_1346 = lean_ctor_get(x_3, 1);
lean_inc(x_1346);
lean_dec(x_3);
x_1347 = lean_ctor_get(x_1303, 1);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1303, 2);
lean_inc(x_1348);
x_1349 = lean_ctor_get(x_1303, 3);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1303, 4);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1303, 5);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1303, 6);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1303, 7);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1303, 8);
lean_inc(x_1354);
x_1355 = lean_ctor_get_uint8(x_1303, sizeof(void*)*10);
x_1356 = lean_ctor_get_uint8(x_1303, sizeof(void*)*10 + 1);
x_1357 = lean_ctor_get_uint8(x_1303, sizeof(void*)*10 + 2);
x_1358 = lean_ctor_get(x_1303, 9);
lean_inc(x_1358);
if (lean_is_exclusive(x_1303)) {
 lean_ctor_release(x_1303, 0);
 lean_ctor_release(x_1303, 1);
 lean_ctor_release(x_1303, 2);
 lean_ctor_release(x_1303, 3);
 lean_ctor_release(x_1303, 4);
 lean_ctor_release(x_1303, 5);
 lean_ctor_release(x_1303, 6);
 lean_ctor_release(x_1303, 7);
 lean_ctor_release(x_1303, 8);
 lean_ctor_release(x_1303, 9);
 x_1359 = x_1303;
} else {
 lean_dec_ref(x_1303);
 x_1359 = lean_box(0);
}
x_1360 = lean_ctor_get(x_1304, 0);
lean_inc(x_1360);
x_1361 = lean_ctor_get(x_1304, 1);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1304, 2);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_1304, 3);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1304, 4);
lean_inc(x_1364);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 lean_ctor_release(x_1304, 2);
 lean_ctor_release(x_1304, 3);
 lean_ctor_release(x_1304, 4);
 x_1365 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1365 = lean_box(0);
}
x_1366 = lean_unsigned_to_nat(1u);
x_1367 = lean_nat_add(x_1363, x_1366);
lean_dec(x_1363);
if (lean_is_scalar(x_1365)) {
 x_1368 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1368 = x_1365;
}
lean_ctor_set(x_1368, 0, x_1360);
lean_ctor_set(x_1368, 1, x_1361);
lean_ctor_set(x_1368, 2, x_1362);
lean_ctor_set(x_1368, 3, x_1367);
lean_ctor_set(x_1368, 4, x_1364);
if (lean_is_scalar(x_1359)) {
 x_1369 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1369 = x_1359;
}
lean_ctor_set(x_1369, 0, x_1368);
lean_ctor_set(x_1369, 1, x_1347);
lean_ctor_set(x_1369, 2, x_1348);
lean_ctor_set(x_1369, 3, x_1349);
lean_ctor_set(x_1369, 4, x_1350);
lean_ctor_set(x_1369, 5, x_1351);
lean_ctor_set(x_1369, 6, x_1352);
lean_ctor_set(x_1369, 7, x_1353);
lean_ctor_set(x_1369, 8, x_1354);
lean_ctor_set(x_1369, 9, x_1358);
lean_ctor_set_uint8(x_1369, sizeof(void*)*10, x_1355);
lean_ctor_set_uint8(x_1369, sizeof(void*)*10 + 1, x_1356);
lean_ctor_set_uint8(x_1369, sizeof(void*)*10 + 2, x_1357);
x_1370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1370, 0, x_1369);
lean_ctor_set(x_1370, 1, x_1346);
x_2 = x_1301;
x_3 = x_1370;
x_4 = x_1302;
goto _start;
}
}
}
}
else
{
uint8_t x_1385; 
lean_dec(x_3);
lean_dec(x_1);
x_1385 = !lean_is_exclusive(x_1292);
if (x_1385 == 0)
{
return x_1292;
}
else
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1386 = lean_ctor_get(x_1292, 0);
x_1387 = lean_ctor_get(x_1292, 1);
lean_inc(x_1387);
lean_inc(x_1386);
lean_dec(x_1292);
x_1388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1388, 0, x_1386);
lean_ctor_set(x_1388, 1, x_1387);
return x_1388;
}
}
}
}
}
else
{
uint8_t x_1389; 
lean_dec(x_3);
lean_dec(x_1);
x_1389 = !lean_is_exclusive(x_5);
if (x_1389 == 0)
{
return x_5;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1390 = lean_ctor_get(x_5, 0);
x_1391 = lean_ctor_get(x_5, 1);
lean_inc(x_1391);
lean_inc(x_1390);
lean_dec(x_5);
x_1392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1392, 0, x_1390);
lean_ctor_set(x_1392, 1, x_1391);
return x_1392;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object* x_1) {
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
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
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
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid recursor name '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous recursor name '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getRecFromUsing___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getRecFromUsing___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerTagAttribute___lambda__4___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getRecFromUsing___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Tactic_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_2, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_resolveGlobalName(x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_14 = x_35;
goto block_21;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Elab_Tactic_save(x_13);
lean_inc(x_3);
x_41 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_13);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_46, 0, x_39);
lean_closure_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_47, 0, x_46);
lean_inc(x_3);
x_48 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_44, x_47, x_3, x_43);
lean_dec(x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Elab_Tactic_restore(x_49, x_40);
lean_dec(x_40);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_2);
x_52 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Tactic_throwError___rarg(x_55, x_3, x_50);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_dec(x_41);
x_58 = l_Lean_Elab_Tactic_restore(x_57, x_40);
lean_dec(x_40);
x_59 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_59, 0, x_2);
x_60 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Elab_Tactic_throwError___rarg(x_63, x_3, x_58);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_38);
lean_dec(x_36);
x_65 = lean_box(0);
x_22 = x_65;
goto block_34;
}
}
else
{
lean_object* x_66; 
lean_dec(x_37);
lean_dec(x_36);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
lean_dec(x_12);
x_67 = lean_box(0);
x_14 = x_67;
goto block_21;
}
else
{
lean_object* x_68; 
lean_dec(x_66);
x_68 = lean_box(0);
x_22 = x_68;
goto block_34;
}
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_throwError___rarg(x_19, x_3, x_13);
return x_20;
}
block_34:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_Tactic_getRecFromUsing___closed__8;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_12);
x_29 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_throwError___rarg(x_32, x_3, x_13);
return x_33;
}
}
else
{
uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_8, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_9, 0);
lean_inc(x_75);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_75);
return x_8;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
lean_dec(x_8);
x_77 = lean_ctor_get(x_9, 0);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_8);
if (x_79 == 0)
{
return x_8;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_8, 0);
x_81 = lean_ctor_get(x_8, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_8);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_5);
if (x_83 == 0)
{
return x_5;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_5, 0);
x_85 = lean_ctor_get(x_5, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_5);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_7);
lean_dec(x_7);
x_9 = l_Lean_Name_isSuffixOf___main(x_8, x_1);
lean_dec(x_8);
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_6);
lean_dec(x_6);
x_8 = l_Lean_mkThunk___closed__1;
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for constructor '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_9, x_17, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_17, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
if (x_1 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_7);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_8);
x_22 = l_Lean_Name_toString___closed__1;
x_23 = l_Lean_Name_toStringWithSep___main(x_22, x_9);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_4);
x_30 = l_Lean_Elab_Tactic_throwError___rarg(x_29, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_2 = x_31;
x_3 = x_10;
x_5 = x_32;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
x_38 = lean_box(0);
x_39 = lean_array_push(x_12, x_38);
x_40 = lean_box(0);
x_41 = lean_array_push(x_15, x_40);
lean_ctor_set(x_7, 0, x_41);
lean_ctor_set(x_2, 0, x_39);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_43);
x_45 = l_Array_toList___rarg(x_44);
lean_dec(x_44);
x_46 = lean_array_push(x_12, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = l_Lean_Syntax_getArg(x_43, x_47);
lean_dec(x_43);
x_49 = lean_array_push(x_15, x_48);
lean_ctor_set(x_7, 0, x_49);
lean_ctor_set(x_2, 0, x_46);
x_3 = x_10;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_8);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_8, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_8, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = l_Lean_Syntax_inhabited;
x_57 = lean_array_get(x_56, x_17, x_55);
x_58 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_57);
x_59 = l_Array_toList___rarg(x_58);
lean_dec(x_58);
x_60 = lean_array_push(x_12, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = l_Lean_Syntax_getArg(x_57, x_61);
x_63 = lean_array_push(x_15, x_62);
x_64 = l_Array_eraseIdx___rarg(x_17, x_55);
lean_dec(x_55);
lean_ctor_set(x_21, 0, x_57);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_64);
lean_ctor_set(x_7, 0, x_63);
lean_ctor_set(x_2, 0, x_60);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_21, 0);
lean_inc(x_66);
lean_dec(x_21);
x_67 = l_Lean_Syntax_inhabited;
x_68 = lean_array_get(x_67, x_17, x_66);
x_69 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_68);
x_70 = l_Array_toList___rarg(x_69);
lean_dec(x_69);
x_71 = lean_array_push(x_12, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = l_Lean_Syntax_getArg(x_68, x_72);
x_74 = lean_array_push(x_15, x_73);
x_75 = l_Array_eraseIdx___rarg(x_17, x_66);
lean_dec(x_66);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_8, 1, x_76);
lean_ctor_set(x_8, 0, x_75);
lean_ctor_set(x_7, 0, x_74);
lean_ctor_set(x_2, 0, x_71);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_8);
x_78 = lean_ctor_get(x_21, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_79 = x_21;
} else {
 lean_dec_ref(x_21);
 x_79 = lean_box(0);
}
x_80 = l_Lean_Syntax_inhabited;
x_81 = lean_array_get(x_80, x_17, x_78);
x_82 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_81);
x_83 = l_Array_toList___rarg(x_82);
lean_dec(x_82);
x_84 = lean_array_push(x_12, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = l_Lean_Syntax_getArg(x_81, x_85);
x_87 = lean_array_push(x_15, x_86);
x_88 = l_Array_eraseIdx___rarg(x_17, x_78);
lean_dec(x_78);
if (lean_is_scalar(x_79)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_79;
}
lean_ctor_set(x_89, 0, x_81);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_7, 1, x_90);
lean_ctor_set(x_7, 0, x_87);
lean_ctor_set(x_2, 0, x_84);
x_3 = x_10;
goto _start;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_9);
x_92 = !lean_is_exclusive(x_8);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_ctor_get(x_8, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_8, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_20, 0);
lean_inc(x_95);
lean_dec(x_20);
x_96 = l_Lean_Syntax_inhabited;
x_97 = lean_array_get(x_96, x_17, x_95);
x_98 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_97);
x_99 = l_Array_toList___rarg(x_98);
lean_dec(x_98);
x_100 = lean_array_push(x_12, x_99);
x_101 = lean_unsigned_to_nat(3u);
x_102 = l_Lean_Syntax_getArg(x_97, x_101);
lean_dec(x_97);
x_103 = lean_array_push(x_15, x_102);
x_104 = l_Array_eraseIdx___rarg(x_17, x_95);
lean_dec(x_95);
lean_ctor_set(x_8, 0, x_104);
lean_ctor_set(x_7, 0, x_103);
lean_ctor_set(x_2, 0, x_100);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_8);
x_106 = lean_ctor_get(x_20, 0);
lean_inc(x_106);
lean_dec(x_20);
x_107 = l_Lean_Syntax_inhabited;
x_108 = lean_array_get(x_107, x_17, x_106);
x_109 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_108);
x_110 = l_Array_toList___rarg(x_109);
lean_dec(x_109);
x_111 = lean_array_push(x_12, x_110);
x_112 = lean_unsigned_to_nat(3u);
x_113 = l_Lean_Syntax_getArg(x_108, x_112);
lean_dec(x_108);
x_114 = lean_array_push(x_15, x_113);
x_115 = l_Array_eraseIdx___rarg(x_17, x_106);
lean_dec(x_106);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_18);
lean_ctor_set(x_7, 1, x_116);
lean_ctor_set(x_7, 0, x_114);
lean_ctor_set(x_2, 0, x_111);
x_3 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_7, 0);
lean_inc(x_118);
lean_dec(x_7);
x_119 = lean_ctor_get(x_8, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_8, 1);
lean_inc(x_120);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_9, x_119, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_119, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
if (x_1 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_118);
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_8);
x_124 = l_Lean_Name_toString___closed__1;
x_125 = l_Lean_Name_toStringWithSep___main(x_124, x_9);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_4);
x_132 = l_Lean_Elab_Tactic_throwError___rarg(x_131, x_4, x_5);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_2 = x_133;
x_3 = x_10;
x_5 = x_134;
goto _start;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_10);
lean_dec(x_4);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_9);
x_140 = lean_box(0);
x_141 = lean_array_push(x_12, x_140);
x_142 = lean_box(0);
x_143 = lean_array_push(x_118, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_8);
lean_ctor_set(x_2, 1, x_144);
lean_ctor_set(x_2, 0, x_141);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_9);
x_146 = lean_ctor_get(x_120, 0);
lean_inc(x_146);
lean_dec(x_120);
x_147 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_146);
x_148 = l_Array_toList___rarg(x_147);
lean_dec(x_147);
x_149 = lean_array_push(x_12, x_148);
x_150 = lean_unsigned_to_nat(3u);
x_151 = l_Lean_Syntax_getArg(x_146, x_150);
lean_dec(x_146);
x_152 = lean_array_push(x_118, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_8);
lean_ctor_set(x_2, 1, x_153);
lean_ctor_set(x_2, 0, x_149);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_120);
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_155 = x_8;
} else {
 lean_dec_ref(x_8);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_123, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_157 = x_123;
} else {
 lean_dec_ref(x_123);
 x_157 = lean_box(0);
}
x_158 = l_Lean_Syntax_inhabited;
x_159 = lean_array_get(x_158, x_119, x_156);
x_160 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_159);
x_161 = l_Array_toList___rarg(x_160);
lean_dec(x_160);
x_162 = lean_array_push(x_12, x_161);
x_163 = lean_unsigned_to_nat(3u);
x_164 = l_Lean_Syntax_getArg(x_159, x_163);
x_165 = lean_array_push(x_118, x_164);
x_166 = l_Array_eraseIdx___rarg(x_119, x_156);
lean_dec(x_156);
if (lean_is_scalar(x_157)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_157;
}
lean_ctor_set(x_167, 0, x_159);
if (lean_is_scalar(x_155)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_155;
}
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_2, 1, x_169);
lean_ctor_set(x_2, 0, x_162);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_171 = x_8;
} else {
 lean_dec_ref(x_8);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_122, 0);
lean_inc(x_172);
lean_dec(x_122);
x_173 = l_Lean_Syntax_inhabited;
x_174 = lean_array_get(x_173, x_119, x_172);
x_175 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_174);
x_176 = l_Array_toList___rarg(x_175);
lean_dec(x_175);
x_177 = lean_array_push(x_12, x_176);
x_178 = lean_unsigned_to_nat(3u);
x_179 = l_Lean_Syntax_getArg(x_174, x_178);
lean_dec(x_174);
x_180 = lean_array_push(x_118, x_179);
x_181 = l_Array_eraseIdx___rarg(x_119, x_172);
lean_dec(x_172);
if (lean_is_scalar(x_171)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_171;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_120);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_2, 1, x_183);
lean_ctor_set(x_2, 0, x_177);
x_3 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_2, 0);
lean_inc(x_185);
lean_dec(x_2);
x_186 = lean_ctor_get(x_7, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_187 = x_7;
} else {
 lean_dec_ref(x_7);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_8, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_8, 1);
lean_inc(x_189);
x_190 = lean_unsigned_to_nat(0u);
x_191 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_9, x_188, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_188, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_dec(x_188);
if (lean_obj_tag(x_189) == 0)
{
if (x_1 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_8);
x_193 = l_Lean_Name_toString___closed__1;
x_194 = l_Lean_Name_toStringWithSep___main(x_193, x_9);
x_195 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
x_198 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_200 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_inc(x_4);
x_201 = l_Lean_Elab_Tactic_throwError___rarg(x_200, x_4, x_5);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_2 = x_202;
x_3 = x_10;
x_5 = x_203;
goto _start;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_10);
lean_dec(x_4);
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_9);
x_209 = lean_box(0);
x_210 = lean_array_push(x_185, x_209);
x_211 = lean_box(0);
x_212 = lean_array_push(x_186, x_211);
if (lean_is_scalar(x_187)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_187;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_8);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_213);
x_2 = x_214;
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_9);
x_216 = lean_ctor_get(x_189, 0);
lean_inc(x_216);
lean_dec(x_189);
x_217 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_216);
x_218 = l_Array_toList___rarg(x_217);
lean_dec(x_217);
x_219 = lean_array_push(x_185, x_218);
x_220 = lean_unsigned_to_nat(3u);
x_221 = l_Lean_Syntax_getArg(x_216, x_220);
lean_dec(x_216);
x_222 = lean_array_push(x_186, x_221);
if (lean_is_scalar(x_187)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_187;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_8);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_223);
x_2 = x_224;
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_189);
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_226 = x_8;
} else {
 lean_dec_ref(x_8);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_192, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_228 = x_192;
} else {
 lean_dec_ref(x_192);
 x_228 = lean_box(0);
}
x_229 = l_Lean_Syntax_inhabited;
x_230 = lean_array_get(x_229, x_188, x_227);
x_231 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_230);
x_232 = l_Array_toList___rarg(x_231);
lean_dec(x_231);
x_233 = lean_array_push(x_185, x_232);
x_234 = lean_unsigned_to_nat(3u);
x_235 = l_Lean_Syntax_getArg(x_230, x_234);
x_236 = lean_array_push(x_186, x_235);
x_237 = l_Array_eraseIdx___rarg(x_188, x_227);
lean_dec(x_227);
if (lean_is_scalar(x_228)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_228;
}
lean_ctor_set(x_238, 0, x_230);
if (lean_is_scalar(x_226)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_226;
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
if (lean_is_scalar(x_187)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_187;
}
lean_ctor_set(x_240, 0, x_236);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_233);
lean_ctor_set(x_241, 1, x_240);
x_2 = x_241;
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_243 = x_8;
} else {
 lean_dec_ref(x_8);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_191, 0);
lean_inc(x_244);
lean_dec(x_191);
x_245 = l_Lean_Syntax_inhabited;
x_246 = lean_array_get(x_245, x_188, x_244);
x_247 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_246);
x_248 = l_Array_toList___rarg(x_247);
lean_dec(x_247);
x_249 = lean_array_push(x_185, x_248);
x_250 = lean_unsigned_to_nat(3u);
x_251 = l_Lean_Syntax_getArg(x_246, x_250);
lean_dec(x_246);
x_252 = lean_array_push(x_186, x_251);
x_253 = l_Array_eraseIdx___rarg(x_188, x_244);
lean_dec(x_244);
if (lean_is_scalar(x_243)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_243;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_189);
if (lean_is_scalar(x_187)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_187;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_249);
lean_ctor_set(x_256, 1, x_255);
x_2 = x_256;
x_3 = x_10;
goto _start;
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unused alternative");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Tactic_getInductiveValFromMajor(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_mkRecFor___closed__1;
x_13 = lean_name_mk_string(x_11, x_12);
x_14 = l_Lean_Syntax_isNone(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_2);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_15, x_16, x_17, x_4, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_4);
lean_inc(x_15);
x_25 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_3, x_24, x_15, x_4, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_dec(x_36);
x_37 = l_Array_isEmpty___rarg(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_25);
x_38 = l_Lean_Syntax_inhabited;
x_39 = lean_array_get(x_38, x_35, x_17);
lean_dec(x_35);
x_40 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_41 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_39, x_40, x_4, x_30);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_32);
lean_ctor_set(x_44, 2, x_33);
x_45 = l_List_redLength___main___rarg(x_15);
x_46 = lean_mk_empty_array_with_capacity(x_45);
lean_dec(x_45);
x_47 = l_List_toArrayAux___main___rarg(x_15, x_46);
lean_ctor_set(x_28, 1, x_47);
lean_ctor_set(x_28, 0, x_44);
lean_ctor_set(x_41, 0, x_28);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 2, x_33);
x_50 = l_List_redLength___main___rarg(x_15);
x_51 = lean_mk_empty_array_with_capacity(x_50);
lean_dec(x_50);
x_52 = l_List_toArrayAux___main___rarg(x_15, x_51);
lean_ctor_set(x_28, 1, x_52);
lean_ctor_set(x_28, 0, x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_28);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_15);
lean_dec(x_13);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_35);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_32);
lean_ctor_set(x_58, 2, x_33);
x_59 = l_List_redLength___main___rarg(x_15);
x_60 = lean_mk_empty_array_with_capacity(x_59);
lean_dec(x_59);
x_61 = l_List_toArrayAux___main___rarg(x_15, x_60);
lean_ctor_set(x_28, 1, x_61);
lean_ctor_set(x_28, 0, x_58);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_28, 0);
lean_inc(x_62);
lean_dec(x_28);
x_63 = l_Array_isEmpty___rarg(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_25);
x_64 = l_Lean_Syntax_inhabited;
x_65 = lean_array_get(x_64, x_62, x_17);
lean_dec(x_62);
x_66 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_67 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_65, x_66, x_4, x_30);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
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
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_13);
lean_ctor_set(x_70, 1, x_32);
lean_ctor_set(x_70, 2, x_33);
x_71 = l_List_redLength___main___rarg(x_15);
x_72 = lean_mk_empty_array_with_capacity(x_71);
lean_dec(x_71);
x_73 = l_List_toArrayAux___main___rarg(x_15, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_15);
lean_dec(x_13);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_78 = x_67;
} else {
 lean_dec_ref(x_67);
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
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_62);
lean_dec(x_4);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_13);
lean_ctor_set(x_80, 1, x_32);
lean_ctor_set(x_80, 2, x_33);
x_81 = l_List_redLength___main___rarg(x_15);
x_82 = lean_mk_empty_array_with_capacity(x_81);
lean_dec(x_81);
x_83 = l_List_toArrayAux___main___rarg(x_15, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_25, 0, x_84);
return x_25;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_25, 1);
lean_inc(x_85);
lean_dec(x_25);
x_86 = lean_ctor_get(x_26, 0);
lean_inc(x_86);
lean_dec(x_26);
x_87 = lean_ctor_get(x_27, 0);
lean_inc(x_87);
lean_dec(x_27);
x_88 = lean_ctor_get(x_28, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_89 = x_28;
} else {
 lean_dec_ref(x_28);
 x_89 = lean_box(0);
}
x_90 = l_Array_isEmpty___rarg(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = l_Lean_Syntax_inhabited;
x_92 = lean_array_get(x_91, x_88, x_17);
lean_dec(x_88);
x_93 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_94 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_92, x_93, x_4, x_85);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_13);
lean_ctor_set(x_97, 1, x_86);
lean_ctor_set(x_97, 2, x_87);
x_98 = l_List_redLength___main___rarg(x_15);
x_99 = lean_mk_empty_array_with_capacity(x_98);
lean_dec(x_98);
x_100 = l_List_toArrayAux___main___rarg(x_15, x_99);
if (lean_is_scalar(x_89)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_89;
}
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_96)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_96;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_15);
lean_dec(x_13);
x_103 = lean_ctor_get(x_94, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_105 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_88);
lean_dec(x_4);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_13);
lean_ctor_set(x_107, 1, x_86);
lean_ctor_set(x_107, 2, x_87);
x_108 = l_List_redLength___main___rarg(x_15);
x_109 = lean_mk_empty_array_with_capacity(x_108);
lean_dec(x_108);
x_110 = l_List_toArrayAux___main___rarg(x_15, x_109);
if (lean_is_scalar(x_89)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_89;
}
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_85);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_25);
if (x_113 == 0)
{
return x_25;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_25, 0);
x_115 = lean_ctor_get(x_25, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_25);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_18);
if (x_117 == 0)
{
return x_18;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_18, 0);
x_119 = lean_ctor_get(x_18, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_18);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_8);
lean_dec(x_4);
x_121 = l_Array_empty___closed__1;
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_13);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_6, 0, x_123);
return x_6;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_6, 0);
x_125 = lean_ctor_get(x_6, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_6);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec(x_126);
x_128 = l_Lean_mkRecFor___closed__1;
x_129 = lean_name_mk_string(x_127, x_128);
x_130 = l_Lean_Syntax_isNone(x_2);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_124, 4);
lean_inc(x_131);
lean_dec(x_124);
x_132 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_2);
x_133 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_134 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_131, x_132, x_133, x_4, x_125);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Array_empty___closed__1;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_4);
lean_inc(x_131);
x_141 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_3, x_140, x_131, x_4, x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_146 = x_141;
} else {
 lean_dec_ref(x_141);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_142, 0);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_ctor_get(x_143, 0);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_150 = x_144;
} else {
 lean_dec_ref(x_144);
 x_150 = lean_box(0);
}
x_151 = l_Array_isEmpty___rarg(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_146);
x_152 = l_Lean_Syntax_inhabited;
x_153 = lean_array_get(x_152, x_149, x_133);
lean_dec(x_149);
x_154 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_155 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_153, x_154, x_4, x_145);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
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
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_129);
lean_ctor_set(x_158, 1, x_147);
lean_ctor_set(x_158, 2, x_148);
x_159 = l_List_redLength___main___rarg(x_131);
x_160 = lean_mk_empty_array_with_capacity(x_159);
lean_dec(x_159);
x_161 = l_List_toArrayAux___main___rarg(x_131, x_160);
if (lean_is_scalar(x_150)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_150;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
if (lean_is_scalar(x_157)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_157;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_131);
lean_dec(x_129);
x_164 = lean_ctor_get(x_155, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_155, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_166 = x_155;
} else {
 lean_dec_ref(x_155);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_149);
lean_dec(x_4);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_129);
lean_ctor_set(x_168, 1, x_147);
lean_ctor_set(x_168, 2, x_148);
x_169 = l_List_redLength___main___rarg(x_131);
x_170 = lean_mk_empty_array_with_capacity(x_169);
lean_dec(x_169);
x_171 = l_List_toArrayAux___main___rarg(x_131, x_170);
if (lean_is_scalar(x_150)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_150;
}
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
if (lean_is_scalar(x_146)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_146;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_145);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_4);
x_174 = lean_ctor_get(x_141, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_141, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_176 = x_141;
} else {
 lean_dec_ref(x_141);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_4);
x_178 = lean_ctor_get(x_134, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_134, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_180 = x_134;
} else {
 lean_dec_ref(x_134);
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
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_124);
lean_dec(x_4);
x_182 = l_Array_empty___closed__1;
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_129);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_125);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_4);
x_186 = !lean_is_exclusive(x_6);
if (x_186 == 0)
{
return x_6;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_6, 0);
x_188 = lean_ctor_get(x_6, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_6);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_7);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
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
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for minor premise '");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_Name_inhabited;
x_17 = lean_array_get(x_16, x_2, x_13);
lean_dec(x_13);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
x_28 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_17, x_26, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_26, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_18);
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_21);
lean_dec(x_19);
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_17);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_6);
x_38 = l_Lean_Elab_Tactic_throwError___rarg(x_37, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_4 = x_11;
x_5 = x_39;
x_7 = x_40;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_17);
x_46 = lean_ctor_get(x_27, 0);
lean_inc(x_46);
lean_dec(x_27);
x_47 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_46);
x_48 = l_Array_toList___rarg(x_47);
lean_dec(x_47);
x_49 = lean_array_push(x_21, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = l_Lean_Syntax_getArg(x_46, x_50);
lean_dec(x_46);
x_52 = lean_array_push(x_24, x_51);
lean_ctor_set(x_18, 0, x_52);
lean_ctor_set(x_5, 0, x_49);
x_4 = x_11;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
lean_dec(x_17);
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_19, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_19, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_29);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_29, 0);
x_59 = l_Lean_Syntax_inhabited;
x_60 = lean_array_get(x_59, x_26, x_58);
x_61 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_60);
x_62 = l_Array_toList___rarg(x_61);
lean_dec(x_61);
x_63 = lean_array_push(x_21, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = l_Lean_Syntax_getArg(x_60, x_64);
x_66 = lean_array_push(x_24, x_65);
x_67 = l_Array_eraseIdx___rarg(x_26, x_58);
lean_dec(x_58);
lean_ctor_set(x_29, 0, x_60);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_67);
lean_ctor_set(x_18, 0, x_66);
lean_ctor_set(x_5, 0, x_63);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_29, 0);
lean_inc(x_69);
lean_dec(x_29);
x_70 = l_Lean_Syntax_inhabited;
x_71 = lean_array_get(x_70, x_26, x_69);
x_72 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_71);
x_73 = l_Array_toList___rarg(x_72);
lean_dec(x_72);
x_74 = lean_array_push(x_21, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = l_Lean_Syntax_getArg(x_71, x_75);
x_77 = lean_array_push(x_24, x_76);
x_78 = l_Array_eraseIdx___rarg(x_26, x_69);
lean_dec(x_69);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_19, 1, x_79);
lean_ctor_set(x_19, 0, x_78);
lean_ctor_set(x_18, 0, x_77);
lean_ctor_set(x_5, 0, x_74);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_19);
x_81 = lean_ctor_get(x_29, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_82 = x_29;
} else {
 lean_dec_ref(x_29);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Syntax_inhabited;
x_84 = lean_array_get(x_83, x_26, x_81);
x_85 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_84);
x_86 = l_Array_toList___rarg(x_85);
lean_dec(x_85);
x_87 = lean_array_push(x_21, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = l_Lean_Syntax_getArg(x_84, x_88);
x_90 = lean_array_push(x_24, x_89);
x_91 = l_Array_eraseIdx___rarg(x_26, x_81);
lean_dec(x_81);
if (lean_is_scalar(x_82)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_82;
}
lean_ctor_set(x_92, 0, x_84);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_18, 1, x_93);
lean_ctor_set(x_18, 0, x_90);
lean_ctor_set(x_5, 0, x_87);
x_4 = x_11;
goto _start;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_17);
x_95 = !lean_is_exclusive(x_19);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_96 = lean_ctor_get(x_19, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_19, 0);
lean_dec(x_97);
x_98 = lean_ctor_get(x_28, 0);
lean_inc(x_98);
lean_dec(x_28);
x_99 = l_Lean_Syntax_inhabited;
x_100 = lean_array_get(x_99, x_26, x_98);
x_101 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_100);
x_102 = l_Array_toList___rarg(x_101);
lean_dec(x_101);
x_103 = lean_array_push(x_21, x_102);
x_104 = lean_unsigned_to_nat(3u);
x_105 = l_Lean_Syntax_getArg(x_100, x_104);
lean_dec(x_100);
x_106 = lean_array_push(x_24, x_105);
x_107 = l_Array_eraseIdx___rarg(x_26, x_98);
lean_dec(x_98);
lean_ctor_set(x_19, 0, x_107);
lean_ctor_set(x_18, 0, x_106);
lean_ctor_set(x_5, 0, x_103);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_19);
x_109 = lean_ctor_get(x_28, 0);
lean_inc(x_109);
lean_dec(x_28);
x_110 = l_Lean_Syntax_inhabited;
x_111 = lean_array_get(x_110, x_26, x_109);
x_112 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_111);
x_113 = l_Array_toList___rarg(x_112);
lean_dec(x_112);
x_114 = lean_array_push(x_21, x_113);
x_115 = lean_unsigned_to_nat(3u);
x_116 = l_Lean_Syntax_getArg(x_111, x_115);
lean_dec(x_111);
x_117 = lean_array_push(x_24, x_116);
x_118 = l_Array_eraseIdx___rarg(x_26, x_109);
lean_dec(x_109);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_27);
lean_ctor_set(x_18, 1, x_119);
lean_ctor_set(x_18, 0, x_117);
lean_ctor_set(x_5, 0, x_114);
x_4 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_18, 0);
lean_inc(x_121);
lean_dec(x_18);
x_122 = lean_ctor_get(x_19, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_19, 1);
lean_inc(x_123);
x_124 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_17, x_122, x_8);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_122, x_8);
if (lean_obj_tag(x_125) == 0)
{
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_121);
lean_free_object(x_5);
lean_dec(x_21);
lean_dec(x_19);
x_126 = l_Lean_Name_toString___closed__1;
x_127 = l_Lean_Name_toStringWithSep___main(x_126, x_17);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_6);
x_134 = l_Lean_Elab_Tactic_throwError___rarg(x_133, x_6, x_7);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_4 = x_11;
x_5 = x_135;
x_7 = x_136;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_11);
lean_dec(x_6);
x_138 = lean_ctor_get(x_134, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_140 = x_134;
} else {
 lean_dec_ref(x_134);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_17);
x_142 = lean_ctor_get(x_123, 0);
lean_inc(x_142);
lean_dec(x_123);
x_143 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_142);
x_144 = l_Array_toList___rarg(x_143);
lean_dec(x_143);
x_145 = lean_array_push(x_21, x_144);
x_146 = lean_unsigned_to_nat(3u);
x_147 = l_Lean_Syntax_getArg(x_142, x_146);
lean_dec(x_142);
x_148 = lean_array_push(x_121, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_19);
lean_ctor_set(x_5, 1, x_149);
lean_ctor_set(x_5, 0, x_145);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_123);
lean_dec(x_17);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_151 = x_19;
} else {
 lean_dec_ref(x_19);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_125, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_153 = x_125;
} else {
 lean_dec_ref(x_125);
 x_153 = lean_box(0);
}
x_154 = l_Lean_Syntax_inhabited;
x_155 = lean_array_get(x_154, x_122, x_152);
x_156 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_155);
x_157 = l_Array_toList___rarg(x_156);
lean_dec(x_156);
x_158 = lean_array_push(x_21, x_157);
x_159 = lean_unsigned_to_nat(3u);
x_160 = l_Lean_Syntax_getArg(x_155, x_159);
x_161 = lean_array_push(x_121, x_160);
x_162 = l_Array_eraseIdx___rarg(x_122, x_152);
lean_dec(x_152);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_155);
if (lean_is_scalar(x_151)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_151;
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_5, 1, x_165);
lean_ctor_set(x_5, 0, x_158);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_17);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_167 = x_19;
} else {
 lean_dec_ref(x_19);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_124, 0);
lean_inc(x_168);
lean_dec(x_124);
x_169 = l_Lean_Syntax_inhabited;
x_170 = lean_array_get(x_169, x_122, x_168);
x_171 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_170);
x_172 = l_Array_toList___rarg(x_171);
lean_dec(x_171);
x_173 = lean_array_push(x_21, x_172);
x_174 = lean_unsigned_to_nat(3u);
x_175 = l_Lean_Syntax_getArg(x_170, x_174);
lean_dec(x_170);
x_176 = lean_array_push(x_121, x_175);
x_177 = l_Array_eraseIdx___rarg(x_122, x_168);
lean_dec(x_168);
if (lean_is_scalar(x_167)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_167;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_123);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_5, 1, x_179);
lean_ctor_set(x_5, 0, x_173);
x_4 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_5, 0);
lean_inc(x_181);
lean_dec(x_5);
x_182 = lean_ctor_get(x_18, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_183 = x_18;
} else {
 lean_dec_ref(x_18);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_19, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_19, 1);
lean_inc(x_185);
x_186 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_17, x_184, x_8);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_184, x_8);
if (lean_obj_tag(x_187) == 0)
{
lean_dec(x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_19);
x_188 = l_Lean_Name_toString___closed__1;
x_189 = l_Lean_Name_toStringWithSep___main(x_188, x_17);
x_190 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_193 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_195 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_6);
x_196 = l_Lean_Elab_Tactic_throwError___rarg(x_195, x_6, x_7);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_4 = x_11;
x_5 = x_197;
x_7 = x_198;
goto _start;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_11);
lean_dec(x_6);
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
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
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_17);
x_204 = lean_ctor_get(x_185, 0);
lean_inc(x_204);
lean_dec(x_185);
x_205 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_204);
x_206 = l_Array_toList___rarg(x_205);
lean_dec(x_205);
x_207 = lean_array_push(x_181, x_206);
x_208 = lean_unsigned_to_nat(3u);
x_209 = l_Lean_Syntax_getArg(x_204, x_208);
lean_dec(x_204);
x_210 = lean_array_push(x_182, x_209);
if (lean_is_scalar(x_183)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_183;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_19);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_211);
x_4 = x_11;
x_5 = x_212;
goto _start;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_185);
lean_dec(x_17);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_214 = x_19;
} else {
 lean_dec_ref(x_19);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_187, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_216 = x_187;
} else {
 lean_dec_ref(x_187);
 x_216 = lean_box(0);
}
x_217 = l_Lean_Syntax_inhabited;
x_218 = lean_array_get(x_217, x_184, x_215);
x_219 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_218);
x_220 = l_Array_toList___rarg(x_219);
lean_dec(x_219);
x_221 = lean_array_push(x_181, x_220);
x_222 = lean_unsigned_to_nat(3u);
x_223 = l_Lean_Syntax_getArg(x_218, x_222);
x_224 = lean_array_push(x_182, x_223);
x_225 = l_Array_eraseIdx___rarg(x_184, x_215);
lean_dec(x_215);
if (lean_is_scalar(x_216)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_216;
}
lean_ctor_set(x_226, 0, x_218);
if (lean_is_scalar(x_214)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_214;
}
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
if (lean_is_scalar(x_183)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_183;
}
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_221);
lean_ctor_set(x_229, 1, x_228);
x_4 = x_11;
x_5 = x_229;
goto _start;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_17);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_231 = x_19;
} else {
 lean_dec_ref(x_19);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_186, 0);
lean_inc(x_232);
lean_dec(x_186);
x_233 = l_Lean_Syntax_inhabited;
x_234 = lean_array_get(x_233, x_184, x_232);
x_235 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_234);
x_236 = l_Array_toList___rarg(x_235);
lean_dec(x_235);
x_237 = lean_array_push(x_181, x_236);
x_238 = lean_unsigned_to_nat(3u);
x_239 = l_Lean_Syntax_getArg(x_234, x_238);
lean_dec(x_234);
x_240 = lean_array_push(x_182, x_239);
x_241 = l_Array_eraseIdx___rarg(x_184, x_232);
lean_dec(x_232);
if (lean_is_scalar(x_231)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_231;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_185);
if (lean_is_scalar(x_183)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_183;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_237);
lean_ctor_set(x_244, 1, x_243);
x_4 = x_11;
x_5 = x_244;
goto _start;
}
}
}
}
else
{
lean_object* x_246; 
lean_dec(x_6);
lean_dec(x_4);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_5);
lean_ctor_set(x_246, 1, x_7);
return x_246;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_6);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 9);
x_14 = l_Lean_Elab_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 9, x_14);
if (x_9 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getIdAt(x_6, x_15);
lean_dec(x_6);
x_17 = l_Lean_Name_eraseMacroScopes(x_16);
lean_dec(x_16);
lean_inc(x_3);
x_18 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_17, x_3, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Lean_Syntax_isNone(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
x_24 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_25 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_dec(x_30);
lean_inc(x_22);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_31, 0, x_22);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_3);
x_33 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_29, x_32, x_3, x_27);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_24);
x_37 = l_Array_empty___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_get_size(x_34);
lean_inc(x_3);
lean_inc(x_40);
x_41 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_20, x_34, x_40, x_40, x_39, x_3, x_35);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_20);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_41, 1);
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l_Array_isEmpty___rarg(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_41);
x_52 = l_Lean_Syntax_inhabited;
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get(x_52, x_50, x_53);
lean_dec(x_50);
x_55 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_56 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_54, x_55, x_3, x_46);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_22);
lean_ctor_set(x_59, 1, x_48);
lean_ctor_set(x_59, 2, x_49);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_22);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_22);
x_63 = !lean_is_exclusive(x_56);
if (x_63 == 0)
{
return x_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_56, 0);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_50);
lean_dec(x_3);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_48);
lean_ctor_set(x_67, 2, x_49);
lean_ctor_set(x_41, 0, x_67);
return x_41;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_41, 1);
lean_inc(x_68);
lean_dec(x_41);
x_69 = lean_ctor_get(x_42, 0);
lean_inc(x_69);
lean_dec(x_42);
x_70 = lean_ctor_get(x_43, 0);
lean_inc(x_70);
lean_dec(x_43);
x_71 = lean_ctor_get(x_44, 0);
lean_inc(x_71);
lean_dec(x_44);
x_72 = l_Array_isEmpty___rarg(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = l_Lean_Syntax_inhabited;
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get(x_73, x_71, x_74);
lean_dec(x_71);
x_76 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_77 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_75, x_76, x_3, x_68);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
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
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_22);
lean_ctor_set(x_80, 1, x_69);
lean_ctor_set(x_80, 2, x_70);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_22);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_71);
lean_dec(x_3);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_22);
lean_ctor_set(x_86, 1, x_69);
lean_ctor_set(x_86, 2, x_70);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_68);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_22);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_41);
if (x_88 == 0)
{
return x_41;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_41, 0);
x_90 = lean_ctor_get(x_41, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_41);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_free_object(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_33);
if (x_92 == 0)
{
return x_33;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_33, 0);
x_94 = lean_ctor_get(x_33, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_33);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_26, 0);
lean_inc(x_96);
lean_dec(x_26);
lean_inc(x_22);
x_97 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_97, 0, x_22);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_98, 0, x_97);
lean_inc(x_3);
x_99 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_96, x_98, x_3, x_27);
lean_dec(x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_24);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Array_empty___closed__1;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_get_size(x_100);
lean_inc(x_3);
lean_inc(x_107);
x_108 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_20, x_100, x_107, x_107, x_106, x_3, x_101);
lean_dec(x_107);
lean_dec(x_100);
lean_dec(x_20);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_113 = x_108;
} else {
 lean_dec_ref(x_108);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
lean_dec(x_111);
x_117 = l_Array_isEmpty___rarg(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
x_118 = l_Lean_Syntax_inhabited;
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_array_get(x_118, x_116, x_119);
lean_dec(x_116);
x_121 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_122 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_120, x_121, x_3, x_112);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_22);
lean_ctor_set(x_125, 1, x_114);
lean_ctor_set(x_125, 2, x_115);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_22);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
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
lean_object* x_131; lean_object* x_132; 
lean_dec(x_116);
lean_dec(x_3);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_22);
lean_ctor_set(x_131, 1, x_114);
lean_ctor_set(x_131, 2, x_115);
if (lean_is_scalar(x_113)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_113;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_112);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_22);
lean_dec(x_3);
x_133 = lean_ctor_get(x_108, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_108, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_135 = x_108;
} else {
 lean_dec_ref(x_108);
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
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
x_137 = lean_ctor_get(x_99, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_99, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_139 = x_99;
} else {
 lean_dec_ref(x_99);
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
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_25);
if (x_141 == 0)
{
return x_25;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_25, 0);
x_143 = lean_ctor_get(x_25, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_25);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_8);
x_145 = l_Array_empty___closed__1;
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_22);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_145);
lean_ctor_set(x_18, 0, x_146);
return x_18;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_18, 0);
x_148 = lean_ctor_get(x_18, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_18);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = l_Lean_Syntax_isNone(x_8);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_152 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_148);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
lean_inc(x_149);
x_157 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_157, 0, x_149);
x_158 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_158, 0, x_157);
lean_inc(x_3);
x_159 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_155, x_158, x_3, x_154);
lean_dec(x_155);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_156;
}
lean_ctor_set(x_163, 0, x_151);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Array_empty___closed__1;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_get_size(x_160);
lean_inc(x_3);
lean_inc(x_167);
x_168 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_147, x_160, x_167, x_167, x_166, x_3, x_161);
lean_dec(x_167);
lean_dec(x_160);
lean_dec(x_147);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_173 = x_168;
} else {
 lean_dec_ref(x_168);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_169, 0);
lean_inc(x_174);
lean_dec(x_169);
x_175 = lean_ctor_get(x_170, 0);
lean_inc(x_175);
lean_dec(x_170);
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
lean_dec(x_171);
x_177 = l_Array_isEmpty___rarg(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
x_178 = l_Lean_Syntax_inhabited;
x_179 = lean_unsigned_to_nat(0u);
x_180 = lean_array_get(x_178, x_176, x_179);
lean_dec(x_176);
x_181 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_182 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_180, x_181, x_3, x_172);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
x_185 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_185, 0, x_149);
lean_ctor_set(x_185, 1, x_174);
lean_ctor_set(x_185, 2, x_175);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_149);
x_187 = lean_ctor_get(x_182, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_189 = x_182;
} else {
 lean_dec_ref(x_182);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_176);
lean_dec(x_3);
x_191 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_191, 0, x_149);
lean_ctor_set(x_191, 1, x_174);
lean_ctor_set(x_191, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_173;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_172);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_149);
lean_dec(x_3);
x_193 = lean_ctor_get(x_168, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_168, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_195 = x_168;
} else {
 lean_dec_ref(x_168);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_156);
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_3);
x_197 = lean_ctor_get(x_159, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_159, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_199 = x_159;
} else {
 lean_dec_ref(x_159);
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
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_3);
x_201 = lean_ctor_get(x_152, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_152, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_203 = x_152;
} else {
 lean_dec_ref(x_152);
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
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_147);
lean_dec(x_3);
lean_dec(x_8);
x_205 = l_Array_empty___closed__1;
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_149);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_148);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_3);
lean_dec(x_8);
x_208 = !lean_is_exclusive(x_18);
if (x_208 == 0)
{
return x_18;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_18, 0);
x_210 = lean_ctor_get(x_18, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_18);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; lean_object* x_213; 
lean_dec(x_6);
x_212 = 0;
x_213 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_212, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec(x_215);
lean_ctor_set(x_213, 0, x_216);
return x_213;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_213, 0);
x_218 = lean_ctor_get(x_213, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_213);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
else
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_213);
if (x_221 == 0)
{
return x_213;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_213, 0);
x_223 = lean_ctor_get(x_213, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_213);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_225 = lean_ctor_get(x_11, 0);
x_226 = lean_ctor_get(x_11, 1);
x_227 = lean_ctor_get(x_11, 2);
x_228 = lean_ctor_get(x_11, 3);
x_229 = lean_ctor_get(x_11, 4);
x_230 = lean_ctor_get(x_11, 5);
x_231 = lean_ctor_get(x_11, 6);
x_232 = lean_ctor_get(x_11, 7);
x_233 = lean_ctor_get(x_11, 8);
x_234 = lean_ctor_get_uint8(x_11, sizeof(void*)*10);
x_235 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 1);
x_236 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 2);
x_237 = lean_ctor_get(x_11, 9);
lean_inc(x_237);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_11);
x_238 = l_Lean_Elab_replaceRef(x_1, x_237);
lean_dec(x_237);
x_239 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_239, 0, x_225);
lean_ctor_set(x_239, 1, x_226);
lean_ctor_set(x_239, 2, x_227);
lean_ctor_set(x_239, 3, x_228);
lean_ctor_set(x_239, 4, x_229);
lean_ctor_set(x_239, 5, x_230);
lean_ctor_set(x_239, 6, x_231);
lean_ctor_set(x_239, 7, x_232);
lean_ctor_set(x_239, 8, x_233);
lean_ctor_set(x_239, 9, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*10, x_234);
lean_ctor_set_uint8(x_239, sizeof(void*)*10 + 1, x_235);
lean_ctor_set_uint8(x_239, sizeof(void*)*10 + 2, x_236);
lean_ctor_set(x_3, 0, x_239);
if (x_9 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_unsigned_to_nat(1u);
x_241 = l_Lean_Syntax_getIdAt(x_6, x_240);
lean_dec(x_6);
x_242 = l_Lean_Name_eraseMacroScopes(x_241);
lean_dec(x_241);
lean_inc(x_3);
x_243 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_242, x_3, x_4);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
x_248 = l_Lean_Syntax_isNone(x_8);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_246);
x_249 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_250 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_245);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
lean_inc(x_247);
x_255 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_255, 0, x_247);
x_256 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_256, 0, x_255);
lean_inc(x_3);
x_257 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_253, x_256, x_3, x_252);
lean_dec(x_253);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_box(0);
if (lean_is_scalar(x_254)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_254;
}
lean_ctor_set(x_261, 0, x_249);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Array_empty___closed__1;
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_array_get_size(x_258);
lean_inc(x_3);
lean_inc(x_265);
x_266 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_244, x_258, x_265, x_265, x_264, x_3, x_259);
lean_dec(x_265);
lean_dec(x_258);
lean_dec(x_244);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_266, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_271 = x_266;
} else {
 lean_dec_ref(x_266);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_267, 0);
lean_inc(x_272);
lean_dec(x_267);
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
lean_dec(x_268);
x_274 = lean_ctor_get(x_269, 0);
lean_inc(x_274);
lean_dec(x_269);
x_275 = l_Array_isEmpty___rarg(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_271);
x_276 = l_Lean_Syntax_inhabited;
x_277 = lean_unsigned_to_nat(0u);
x_278 = lean_array_get(x_276, x_274, x_277);
lean_dec(x_274);
x_279 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_280 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_278, x_279, x_3, x_270);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
x_283 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_283, 0, x_247);
lean_ctor_set(x_283, 1, x_272);
lean_ctor_set(x_283, 2, x_273);
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_281);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_247);
x_285 = lean_ctor_get(x_280, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_287 = x_280;
} else {
 lean_dec_ref(x_280);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_274);
lean_dec(x_3);
x_289 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_289, 0, x_247);
lean_ctor_set(x_289, 1, x_272);
lean_ctor_set(x_289, 2, x_273);
if (lean_is_scalar(x_271)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_271;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_270);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_247);
lean_dec(x_3);
x_291 = lean_ctor_get(x_266, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_266, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_293 = x_266;
} else {
 lean_dec_ref(x_266);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_254);
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_3);
x_295 = lean_ctor_get(x_257, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_257, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_297 = x_257;
} else {
 lean_dec_ref(x_257);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_3);
x_299 = lean_ctor_get(x_250, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_250, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_301 = x_250;
} else {
 lean_dec_ref(x_250);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_244);
lean_dec(x_3);
lean_dec(x_8);
x_303 = l_Array_empty___closed__1;
x_304 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_304, 0, x_247);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_303);
if (lean_is_scalar(x_246)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_246;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_245);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_3);
lean_dec(x_8);
x_306 = lean_ctor_get(x_243, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_243, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_308 = x_243;
} else {
 lean_dec_ref(x_243);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
uint8_t x_310; lean_object* x_311; 
lean_dec(x_6);
x_310 = 0;
x_311 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_310, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_314 = x_311;
} else {
 lean_dec_ref(x_311);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_312, 0);
lean_inc(x_315);
lean_dec(x_312);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_313);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_311, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_311, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_319 = x_311;
} else {
 lean_dec_ref(x_311);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_321 = lean_ctor_get(x_3, 0);
x_322 = lean_ctor_get(x_3, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_3);
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_321, 2);
lean_inc(x_325);
x_326 = lean_ctor_get(x_321, 3);
lean_inc(x_326);
x_327 = lean_ctor_get(x_321, 4);
lean_inc(x_327);
x_328 = lean_ctor_get(x_321, 5);
lean_inc(x_328);
x_329 = lean_ctor_get(x_321, 6);
lean_inc(x_329);
x_330 = lean_ctor_get(x_321, 7);
lean_inc(x_330);
x_331 = lean_ctor_get(x_321, 8);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_321, sizeof(void*)*10);
x_333 = lean_ctor_get_uint8(x_321, sizeof(void*)*10 + 1);
x_334 = lean_ctor_get_uint8(x_321, sizeof(void*)*10 + 2);
x_335 = lean_ctor_get(x_321, 9);
lean_inc(x_335);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 lean_ctor_release(x_321, 6);
 lean_ctor_release(x_321, 7);
 lean_ctor_release(x_321, 8);
 lean_ctor_release(x_321, 9);
 x_336 = x_321;
} else {
 lean_dec_ref(x_321);
 x_336 = lean_box(0);
}
x_337 = l_Lean_Elab_replaceRef(x_1, x_335);
lean_dec(x_335);
if (lean_is_scalar(x_336)) {
 x_338 = lean_alloc_ctor(0, 10, 3);
} else {
 x_338 = x_336;
}
lean_ctor_set(x_338, 0, x_323);
lean_ctor_set(x_338, 1, x_324);
lean_ctor_set(x_338, 2, x_325);
lean_ctor_set(x_338, 3, x_326);
lean_ctor_set(x_338, 4, x_327);
lean_ctor_set(x_338, 5, x_328);
lean_ctor_set(x_338, 6, x_329);
lean_ctor_set(x_338, 7, x_330);
lean_ctor_set(x_338, 8, x_331);
lean_ctor_set(x_338, 9, x_337);
lean_ctor_set_uint8(x_338, sizeof(void*)*10, x_332);
lean_ctor_set_uint8(x_338, sizeof(void*)*10 + 1, x_333);
lean_ctor_set_uint8(x_338, sizeof(void*)*10 + 2, x_334);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_322);
if (x_9 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_unsigned_to_nat(1u);
x_341 = l_Lean_Syntax_getIdAt(x_6, x_340);
lean_dec(x_6);
x_342 = l_Lean_Name_eraseMacroScopes(x_341);
lean_dec(x_341);
lean_inc(x_339);
x_343 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_342, x_339, x_4);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
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
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
x_348 = l_Lean_Syntax_isNone(x_8);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_346);
x_349 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_339);
x_350 = l_Lean_Elab_Tactic_getMainGoal(x_339, x_345);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
lean_inc(x_347);
x_355 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_355, 0, x_347);
x_356 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_356, 0, x_355);
lean_inc(x_339);
x_357 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_353, x_356, x_339, x_352);
lean_dec(x_353);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_354;
}
lean_ctor_set(x_361, 0, x_349);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_Array_empty___closed__1;
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_array_get_size(x_358);
lean_inc(x_339);
lean_inc(x_365);
x_366 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_344, x_358, x_365, x_365, x_364, x_339, x_359);
lean_dec(x_365);
lean_dec(x_358);
lean_dec(x_344);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_366, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_371 = x_366;
} else {
 lean_dec_ref(x_366);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_367, 0);
lean_inc(x_372);
lean_dec(x_367);
x_373 = lean_ctor_get(x_368, 0);
lean_inc(x_373);
lean_dec(x_368);
x_374 = lean_ctor_get(x_369, 0);
lean_inc(x_374);
lean_dec(x_369);
x_375 = l_Array_isEmpty___rarg(x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_371);
x_376 = l_Lean_Syntax_inhabited;
x_377 = lean_unsigned_to_nat(0u);
x_378 = lean_array_get(x_376, x_374, x_377);
lean_dec(x_374);
x_379 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_380 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_378, x_379, x_339, x_370);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
x_383 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_383, 0, x_347);
lean_ctor_set(x_383, 1, x_372);
lean_ctor_set(x_383, 2, x_373);
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_381);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_347);
x_385 = lean_ctor_get(x_380, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_380, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_387 = x_380;
} else {
 lean_dec_ref(x_380);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_374);
lean_dec(x_339);
x_389 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_389, 0, x_347);
lean_ctor_set(x_389, 1, x_372);
lean_ctor_set(x_389, 2, x_373);
if (lean_is_scalar(x_371)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_371;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_370);
return x_390;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_347);
lean_dec(x_339);
x_391 = lean_ctor_get(x_366, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_366, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_393 = x_366;
} else {
 lean_dec_ref(x_366);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_354);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_339);
x_395 = lean_ctor_get(x_357, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_357, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_397 = x_357;
} else {
 lean_dec_ref(x_357);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_339);
x_399 = lean_ctor_get(x_350, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_350, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_401 = x_350;
} else {
 lean_dec_ref(x_350);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_344);
lean_dec(x_339);
lean_dec(x_8);
x_403 = l_Array_empty___closed__1;
x_404 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_404, 0, x_347);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set(x_404, 2, x_403);
if (lean_is_scalar(x_346)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_346;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_345);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_339);
lean_dec(x_8);
x_406 = lean_ctor_get(x_343, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_343, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_408 = x_343;
} else {
 lean_dec_ref(x_343);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
uint8_t x_410; lean_object* x_411; 
lean_dec(x_6);
x_410 = 0;
x_411 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_410, x_339, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_414 = x_411;
} else {
 lean_dec_ref(x_411);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_412, 0);
lean_inc(x_415);
lean_dec(x_412);
if (lean_is_scalar(x_414)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_414;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_413);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_411, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_411, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_419 = x_411;
} else {
 lean_dec_ref(x_411);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
uint8_t l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_mkHole___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = 1;
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_15__isTermRHS___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = 0;
lean_inc(x_5);
lean_inc(x_8);
x_10 = l_Lean_Elab_Tactic_elabTerm(x_1, x_8, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
x_13 = l_Lean_Elab_Tactic_ensureHasType(x_8, x_11, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l_Lean_Elab_Tactic_assignExprMVar(x_2, x_14, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_5);
x_18 = l_Lean_Elab_Tactic_collectMVars(x_14, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_inc(x_19);
x_23 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_21, x_22, x_19, x_5, x_20);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_List_append___rarg(x_3, x_19);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_List_append___rarg(x_3, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
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
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Meta_InductionSubgoal_inhabited;
x_15 = lean_array_get(x_14, x_2, x_13);
x_16 = l_Lean_Syntax_inhabited;
x_17 = lean_array_get(x_16, x_1, x_13);
lean_dec(x_13);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_17);
x_19 = l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Tactic_setGoals(x_21, x_6, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_6);
x_24 = l_Lean_Elab_Tactic_evalTactic___main(x_17, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_6);
x_26 = l_Lean_Elab_Tactic_done(x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_4 = x_11;
x_7 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
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
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_18);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_37, 0, x_18);
lean_inc(x_18);
lean_inc(x_17);
x_38 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1), 6, 3);
lean_closure_set(x_38, 0, x_17);
lean_closure_set(x_38, 1, x_18);
lean_closure_set(x_38, 2, x_5);
x_39 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRef___rarg___boxed), 4, 2);
lean_closure_set(x_40, 0, x_17);
lean_closure_set(x_40, 1, x_39);
lean_inc(x_6);
x_41 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_18, x_40, x_6, x_7);
lean_dec(x_18);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_4 = x_11;
x_5 = x_42;
x_7 = x_43;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_6);
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
else
{
lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_4);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(lean_object* x_1) {
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
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
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
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mistmatch on the number of subgoals produced (");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") and ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternatives provided (");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_19; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_eq(x_6, x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_7);
x_20 = l_Nat_repr(x_7);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Nat_repr(x_6);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_3);
x_35 = l_Lean_Elab_Tactic_throwError___rarg(x_34, x_3, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_8 = x_36;
goto block_18;
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_dec(x_6);
x_8 = x_4;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_inc(x_3);
lean_inc(x_7);
x_10 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(x_1, x_2, x_7, x_7, x_9, x_3, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_setGoals(x_11, x_3, x_12);
lean_dec(x_3);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = l_Array_toList___rarg(x_2);
x_42 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_41);
x_43 = l_Lean_Elab_Tactic_setGoals(x_42, x_3, x_4);
lean_dec(x_3);
return x_43;
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_6);
x_8 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_6);
x_10 = l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(x_1, x_6, x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_induction___boxed), 7, 5);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_17);
lean_closure_set(x_22, 2, x_18);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_21);
lean_inc(x_3);
x_23 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_22, x_3, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_11, 2);
lean_inc(x_26);
lean_dec(x_11);
x_27 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_26, x_24, x_3, x_25);
lean_dec(x_24);
lean_dec(x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
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
lean_dec(x_6);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
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
lean_dec(x_6);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
return x_8;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
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
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
return x_5;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_5, 0);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_5);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
x_5 = l___private_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 4, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Tactic_focusAux___rarg(x_8, x_2, x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalInduction___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been provided");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not needed");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_fget(x_1, x_4);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_throwError___rarg(x_20, x_6, x_7);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_fget(x_3, x_5);
x_23 = l_Lean_Syntax_isMissing(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Name_inhabited;
x_25 = lean_array_get(x_24, x_2, x_5);
x_26 = lean_array_get_size(x_1);
x_27 = lean_nat_dec_lt(x_4, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_29 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_throwError___rarg(x_32, x_6, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_array_fget(x_1, x_4);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_name_eq(x_25, x_35);
lean_dec(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Tactic_throwError___rarg(x_41, x_6, x_7);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_35);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_4, x_43);
lean_dec(x_4);
x_45 = lean_nat_add(x_5, x_43);
lean_dec(x_5);
x_4 = x_44;
x_5 = x_45;
goto _start;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_5, x_47);
lean_dec(x_5);
x_5 = x_48;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_7, x_7, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_isMissing(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fswap(x_1, x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_1 = x_14;
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = 1;
lean_inc(x_3);
lean_inc(x_6);
x_15 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_6, x_13, x_14, x_3, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_20 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_cases___boxed), 6, 4);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_20);
lean_closure_set(x_24, 2, x_21);
lean_closure_set(x_24, 3, x_23);
lean_inc(x_3);
x_25 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_24, x_3, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_18, 2);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_3);
x_29 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_26, x_19, x_28, x_3, x_27);
lean_dec(x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = x_26;
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(x_32, x_31);
x_34 = x_33;
x_35 = l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(x_28, x_32, x_32);
x_36 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_35, x_34, x_3, x_30);
lean_dec(x_34);
lean_dec(x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
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
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
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
lean_dec(x_6);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
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
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
return x_5;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_5, 0);
x_55 = lean_ctor_get(x_5, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_5);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalCases(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
x_5 = l___private_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 4, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__1___boxed), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Tactic_focusAux___rarg(x_8, x_2, x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalCases___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_cases___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Generalize(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Generalize(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1);
l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1);
l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1);
l_Lean_Elab_Tactic_getRecFromUsing___closed__1 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__1);
l_Lean_Elab_Tactic_getRecFromUsing___closed__2 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__2);
l_Lean_Elab_Tactic_getRecFromUsing___closed__3 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__3);
l_Lean_Elab_Tactic_getRecFromUsing___closed__4 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__4);
l_Lean_Elab_Tactic_getRecFromUsing___closed__5 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__5);
l_Lean_Elab_Tactic_getRecFromUsing___closed__6 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__6);
l_Lean_Elab_Tactic_getRecFromUsing___closed__7 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__7);
l_Lean_Elab_Tactic_getRecFromUsing___closed__8 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__8);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__2);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__5 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__5();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__5);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6);
l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1);
l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2);
l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3);
l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1 = _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1);
l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2 = _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2);
l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3 = _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8);
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8);
l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9 = _init_l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
