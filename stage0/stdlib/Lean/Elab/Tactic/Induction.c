// Lean compiler output
// Module: Lean.Elab.Tactic.Induction
// Imports: Lean.Meta.RecursorInfo Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Cases Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Generalize
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7;
lean_object* l_Lean_Elab_Tactic_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
lean_object* l_Lean_Elab_Tactic_restore(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__4;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__10;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(lean_object*);
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_15__isTermRHS___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7;
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_cases___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
lean_object* l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_save(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4;
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__8;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__4;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1;
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8;
lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8;
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4;
extern lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__4;
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_local_ctx_find_from_user_name(x_3, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
x_8 = l_Lean_Elab_Tactic_throwError___rarg(x_2, x_7, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_LocalDecl_toExpr(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_8 = lean_local_ctx_get_unused_name(x_4, x_7);
x_9 = lean_box(0);
x_10 = 0;
lean_inc(x_5);
x_11 = l_Lean_Elab_Tactic_elabTerm(x_1, x_9, x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1), 5, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_2);
x_15 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
lean_inc(x_5);
lean_inc(x_2);
x_17 = l_Lean_Elab_Tactic_evalGeneralizeAux(x_2, x_3, x_12, x_8, x_5, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_2, x_16, x_5, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTerm___boxed), 5, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_1, x_9, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2), 6, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
x_12 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_1, x_13, x_4, x_5);
return x_14;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_box(0);
x_5 = x_25;
goto block_23;
}
block_23:
{
lean_object* x_6; 
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_11 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_generalize___boxed), 5, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
x_13 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_9, x_17, x_3, x_8);
lean_dec(x_9);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_inc(x_5);
x_8 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_Tactic_getFVarIds(x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_5, x_8);
lean_dec(x_5);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 6, 4);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_10);
x_13 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_1, x_12, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Expr_fvarId_x21(x_1);
x_10 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_7, x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_7);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_11);
if (x_10 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
x_15 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_16 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_2, x_16, x_4, x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = l_Lean_Expr_fvarId_x21(x_1);
x_25 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_22, x_24);
lean_dec(x_24);
x_26 = lean_array_get_size(x_22);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
if (x_25 == 0)
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
x_31 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_32 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_31, x_2, x_32, x_4, x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
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
lean_inc(x_1);
x_8 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_7);
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
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_10);
lean_inc(x_10);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed), 3, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_10);
x_15 = l_Lean_Parser_Tactic_underscoreFn___closed__4;
x_16 = lean_name_eq(x_13, x_15);
x_17 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_10);
lean_closure_set(x_18, 2, x_14);
lean_inc(x_4);
x_19 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_18, x_4, x_5);
if (x_16 == 0)
{
uint8_t x_20; uint8_t x_21; 
x_20 = 0;
x_21 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_13, x_20, x_1);
if (x_21 == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_10, x_23);
lean_dec(x_10);
x_25 = l_Lean_Name_toString___closed__1;
x_26 = l_Lean_Name_toStringWithSep___main(x_25, x_13);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_Term_mkConst___closed__4;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_4);
x_33 = l_Lean_Elab_Tactic_throwError___rarg(x_24, x_32, x_4, x_22);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_3 = x_12;
x_5 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_3 = x_12;
x_5 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_dec(x_19);
x_3 = x_12;
x_5 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 0);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_19);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_17; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_17 = l_Lean_Expr_getAppFn___main(x_7);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_environment_find(x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_5);
x_21 = lean_box(0);
x_9 = x_21;
goto block_16;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
else
{
lean_object* x_24; 
lean_dec(x_22);
lean_free_object(x_5);
x_24 = lean_box(0);
x_9 = x_24;
goto block_16;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_17);
lean_free_object(x_5);
x_25 = lean_box(0);
x_9 = x_25;
goto block_16;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = l_Lean_indentExpr(x_10);
x_12 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_1, x_13, x_3, x_8);
lean_dec(x_3);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_36; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_36 = l_Lean_Expr_getAppFn___main(x_26);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
x_39 = lean_environment_find(x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_28 = x_40;
goto block_35;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 5)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_41);
x_44 = lean_box(0);
x_28 = x_44;
goto block_35;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_36);
x_45 = lean_box(0);
x_28 = x_45;
goto block_35;
}
block_35:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = l_Lean_indentExpr(x_29);
x_31 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_33, x_1, x_32, x_3, x_27);
lean_dec(x_3);
return x_34;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
return x_5;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_5);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_inferType), 3, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1), 4, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_8, x_12, x_3, x_7);
lean_dec(x_8);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Elab_Tactic_whnfCore(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_getAppFn___main(x_7);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 6);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 7);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 8);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 9);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_18, sizeof(void*)*10);
x_34 = lean_ctor_get_uint8(x_18, sizeof(void*)*10 + 1);
x_35 = lean_ctor_get_uint8(x_18, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 lean_ctor_release(x_18, 8);
 lean_ctor_release(x_18, 9);
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_19, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_19, 4);
lean_inc(x_38);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_dec(x_4);
x_40 = x_20;
goto block_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_60 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_59, x_4, x_20);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_40 = x_61;
goto block_58;
}
else
{
uint8_t x_62; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_60);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
block_58:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_19, 4);
lean_dec(x_42);
x_43 = lean_ctor_get(x_19, 3);
lean_dec(x_43);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_37, x_44);
lean_dec(x_37);
lean_ctor_set(x_19, 3, x_45);
if (lean_is_scalar(x_36)) {
 x_46 = lean_alloc_ctor(0, 10, 3);
} else {
 x_46 = x_36;
}
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_24);
lean_ctor_set(x_46, 2, x_25);
lean_ctor_set(x_46, 3, x_26);
lean_ctor_set(x_46, 4, x_27);
lean_ctor_set(x_46, 5, x_28);
lean_ctor_set(x_46, 6, x_29);
lean_ctor_set(x_46, 7, x_30);
lean_ctor_set(x_46, 8, x_31);
lean_ctor_set(x_46, 9, x_32);
lean_ctor_set_uint8(x_46, sizeof(void*)*10, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 1, x_34);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 2, x_35);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_22);
lean_ctor_set(x_47, 2, x_23);
x_3 = x_21;
x_4 = x_47;
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
x_51 = lean_ctor_get(x_19, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_37, x_52);
lean_dec(x_37);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_38);
if (lean_is_scalar(x_36)) {
 x_55 = lean_alloc_ctor(0, 10, 3);
} else {
 x_55 = x_36;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_24);
lean_ctor_set(x_55, 2, x_25);
lean_ctor_set(x_55, 3, x_26);
lean_ctor_set(x_55, 4, x_27);
lean_ctor_set(x_55, 5, x_28);
lean_ctor_set(x_55, 6, x_29);
lean_ctor_set(x_55, 7, x_30);
lean_ctor_set(x_55, 8, x_31);
lean_ctor_set(x_55, 9, x_32);
lean_ctor_set_uint8(x_55, sizeof(void*)*10, x_33);
lean_ctor_set_uint8(x_55, sizeof(void*)*10 + 1, x_34);
lean_ctor_set_uint8(x_55, sizeof(void*)*10 + 2, x_35);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_22);
lean_ctor_set(x_56, 2, x_23);
x_3 = x_21;
x_4 = x_56;
x_5 = x_40;
goto _start;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_10);
if (x_66 == 0)
{
return x_10;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_10, 0);
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_10);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 1:
{
lean_object* x_70; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_70 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_ctor_set(x_70, 0, x_74);
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_dec(x_70);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_ctor_get(x_4, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_4, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 5);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 6);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 7);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 8);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 9);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_78, sizeof(void*)*10);
x_94 = lean_ctor_get_uint8(x_78, sizeof(void*)*10 + 1);
x_95 = lean_ctor_get_uint8(x_78, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 lean_ctor_release(x_78, 9);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_79, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_79, 4);
lean_inc(x_98);
x_99 = lean_nat_dec_eq(x_97, x_98);
if (x_99 == 0)
{
lean_dec(x_4);
x_100 = x_80;
goto block_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_120 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_119, x_4, x_80);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_100 = x_121;
goto block_118;
}
else
{
uint8_t x_122; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_120);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
block_118:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_79);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_79, 4);
lean_dec(x_102);
x_103 = lean_ctor_get(x_79, 3);
lean_dec(x_103);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_97, x_104);
lean_dec(x_97);
lean_ctor_set(x_79, 3, x_105);
if (lean_is_scalar(x_96)) {
 x_106 = lean_alloc_ctor(0, 10, 3);
} else {
 x_106 = x_96;
}
lean_ctor_set(x_106, 0, x_79);
lean_ctor_set(x_106, 1, x_84);
lean_ctor_set(x_106, 2, x_85);
lean_ctor_set(x_106, 3, x_86);
lean_ctor_set(x_106, 4, x_87);
lean_ctor_set(x_106, 5, x_88);
lean_ctor_set(x_106, 6, x_89);
lean_ctor_set(x_106, 7, x_90);
lean_ctor_set(x_106, 8, x_91);
lean_ctor_set(x_106, 9, x_92);
lean_ctor_set_uint8(x_106, sizeof(void*)*10, x_93);
lean_ctor_set_uint8(x_106, sizeof(void*)*10 + 1, x_94);
lean_ctor_set_uint8(x_106, sizeof(void*)*10 + 2, x_95);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_82);
lean_ctor_set(x_107, 2, x_83);
x_3 = x_81;
x_4 = x_107;
x_5 = x_100;
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_79, 0);
x_110 = lean_ctor_get(x_79, 1);
x_111 = lean_ctor_get(x_79, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_79);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_97, x_112);
lean_dec(x_97);
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
lean_ctor_set(x_114, 4, x_98);
if (lean_is_scalar(x_96)) {
 x_115 = lean_alloc_ctor(0, 10, 3);
} else {
 x_115 = x_96;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_84);
lean_ctor_set(x_115, 2, x_85);
lean_ctor_set(x_115, 3, x_86);
lean_ctor_set(x_115, 4, x_87);
lean_ctor_set(x_115, 5, x_88);
lean_ctor_set(x_115, 6, x_89);
lean_ctor_set(x_115, 7, x_90);
lean_ctor_set(x_115, 8, x_91);
lean_ctor_set(x_115, 9, x_92);
lean_ctor_set_uint8(x_115, sizeof(void*)*10, x_93);
lean_ctor_set_uint8(x_115, sizeof(void*)*10 + 1, x_94);
lean_ctor_set_uint8(x_115, sizeof(void*)*10 + 2, x_95);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_82);
lean_ctor_set(x_116, 2, x_83);
x_3 = x_81;
x_4 = x_116;
x_5 = x_100;
goto _start;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_70);
if (x_126 == 0)
{
return x_70;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_70, 0);
x_128 = lean_ctor_get(x_70, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_70);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
case 2:
{
lean_object* x_130; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_130 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 0);
lean_dec(x_133);
x_134 = lean_box(0);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_dec(x_130);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_138 = lean_ctor_get(x_4, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
lean_dec(x_130);
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
lean_dec(x_131);
x_142 = lean_ctor_get(x_4, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_4, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_138, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 5);
lean_inc(x_148);
x_149 = lean_ctor_get(x_138, 6);
lean_inc(x_149);
x_150 = lean_ctor_get(x_138, 7);
lean_inc(x_150);
x_151 = lean_ctor_get(x_138, 8);
lean_inc(x_151);
x_152 = lean_ctor_get(x_138, 9);
lean_inc(x_152);
x_153 = lean_ctor_get_uint8(x_138, sizeof(void*)*10);
x_154 = lean_ctor_get_uint8(x_138, sizeof(void*)*10 + 1);
x_155 = lean_ctor_get_uint8(x_138, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 lean_ctor_release(x_138, 5);
 lean_ctor_release(x_138, 6);
 lean_ctor_release(x_138, 7);
 lean_ctor_release(x_138, 8);
 lean_ctor_release(x_138, 9);
 x_156 = x_138;
} else {
 lean_dec_ref(x_138);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_139, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_139, 4);
lean_inc(x_158);
x_159 = lean_nat_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_dec(x_4);
x_160 = x_140;
goto block_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_180 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_179, x_4, x_140);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_160 = x_181;
goto block_178;
}
else
{
uint8_t x_182; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_180);
if (x_182 == 0)
{
return x_180;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_180, 0);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_180);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
block_178:
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_139);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_139, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_139, 3);
lean_dec(x_163);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_add(x_157, x_164);
lean_dec(x_157);
lean_ctor_set(x_139, 3, x_165);
if (lean_is_scalar(x_156)) {
 x_166 = lean_alloc_ctor(0, 10, 3);
} else {
 x_166 = x_156;
}
lean_ctor_set(x_166, 0, x_139);
lean_ctor_set(x_166, 1, x_144);
lean_ctor_set(x_166, 2, x_145);
lean_ctor_set(x_166, 3, x_146);
lean_ctor_set(x_166, 4, x_147);
lean_ctor_set(x_166, 5, x_148);
lean_ctor_set(x_166, 6, x_149);
lean_ctor_set(x_166, 7, x_150);
lean_ctor_set(x_166, 8, x_151);
lean_ctor_set(x_166, 9, x_152);
lean_ctor_set_uint8(x_166, sizeof(void*)*10, x_153);
lean_ctor_set_uint8(x_166, sizeof(void*)*10 + 1, x_154);
lean_ctor_set_uint8(x_166, sizeof(void*)*10 + 2, x_155);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_142);
lean_ctor_set(x_167, 2, x_143);
x_3 = x_141;
x_4 = x_167;
x_5 = x_160;
goto _start;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = lean_ctor_get(x_139, 0);
x_170 = lean_ctor_get(x_139, 1);
x_171 = lean_ctor_get(x_139, 2);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_139);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_157, x_172);
lean_dec(x_157);
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_169);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_171);
lean_ctor_set(x_174, 3, x_173);
lean_ctor_set(x_174, 4, x_158);
if (lean_is_scalar(x_156)) {
 x_175 = lean_alloc_ctor(0, 10, 3);
} else {
 x_175 = x_156;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_144);
lean_ctor_set(x_175, 2, x_145);
lean_ctor_set(x_175, 3, x_146);
lean_ctor_set(x_175, 4, x_147);
lean_ctor_set(x_175, 5, x_148);
lean_ctor_set(x_175, 6, x_149);
lean_ctor_set(x_175, 7, x_150);
lean_ctor_set(x_175, 8, x_151);
lean_ctor_set(x_175, 9, x_152);
lean_ctor_set_uint8(x_175, sizeof(void*)*10, x_153);
lean_ctor_set_uint8(x_175, sizeof(void*)*10 + 1, x_154);
lean_ctor_set_uint8(x_175, sizeof(void*)*10 + 2, x_155);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_142);
lean_ctor_set(x_176, 2, x_143);
x_3 = x_141;
x_4 = x_176;
x_5 = x_160;
goto _start;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_130);
if (x_186 == 0)
{
return x_130;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_130, 0);
x_188 = lean_ctor_get(x_130, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_130);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
case 3:
{
lean_object* x_190; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_190 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_190, 0);
lean_dec(x_193);
x_194 = lean_box(0);
lean_ctor_set(x_190, 0, x_194);
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_190, 1);
lean_inc(x_195);
lean_dec(x_190);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; 
x_198 = lean_ctor_get(x_4, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_190, 1);
lean_inc(x_200);
lean_dec(x_190);
x_201 = lean_ctor_get(x_191, 0);
lean_inc(x_201);
lean_dec(x_191);
x_202 = lean_ctor_get(x_4, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_4, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_198, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_198, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_198, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_198, 5);
lean_inc(x_208);
x_209 = lean_ctor_get(x_198, 6);
lean_inc(x_209);
x_210 = lean_ctor_get(x_198, 7);
lean_inc(x_210);
x_211 = lean_ctor_get(x_198, 8);
lean_inc(x_211);
x_212 = lean_ctor_get(x_198, 9);
lean_inc(x_212);
x_213 = lean_ctor_get_uint8(x_198, sizeof(void*)*10);
x_214 = lean_ctor_get_uint8(x_198, sizeof(void*)*10 + 1);
x_215 = lean_ctor_get_uint8(x_198, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 lean_ctor_release(x_198, 5);
 lean_ctor_release(x_198, 6);
 lean_ctor_release(x_198, 7);
 lean_ctor_release(x_198, 8);
 lean_ctor_release(x_198, 9);
 x_216 = x_198;
} else {
 lean_dec_ref(x_198);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_199, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_199, 4);
lean_inc(x_218);
x_219 = lean_nat_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_dec(x_4);
x_220 = x_200;
goto block_238;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_240 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_239, x_4, x_200);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_220 = x_241;
goto block_238;
}
else
{
uint8_t x_242; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_2);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_240);
if (x_242 == 0)
{
return x_240;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_240, 0);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_240);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
block_238:
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_199);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_199, 4);
lean_dec(x_222);
x_223 = lean_ctor_get(x_199, 3);
lean_dec(x_223);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_add(x_217, x_224);
lean_dec(x_217);
lean_ctor_set(x_199, 3, x_225);
if (lean_is_scalar(x_216)) {
 x_226 = lean_alloc_ctor(0, 10, 3);
} else {
 x_226 = x_216;
}
lean_ctor_set(x_226, 0, x_199);
lean_ctor_set(x_226, 1, x_204);
lean_ctor_set(x_226, 2, x_205);
lean_ctor_set(x_226, 3, x_206);
lean_ctor_set(x_226, 4, x_207);
lean_ctor_set(x_226, 5, x_208);
lean_ctor_set(x_226, 6, x_209);
lean_ctor_set(x_226, 7, x_210);
lean_ctor_set(x_226, 8, x_211);
lean_ctor_set(x_226, 9, x_212);
lean_ctor_set_uint8(x_226, sizeof(void*)*10, x_213);
lean_ctor_set_uint8(x_226, sizeof(void*)*10 + 1, x_214);
lean_ctor_set_uint8(x_226, sizeof(void*)*10 + 2, x_215);
x_227 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_202);
lean_ctor_set(x_227, 2, x_203);
x_3 = x_201;
x_4 = x_227;
x_5 = x_220;
goto _start;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_229 = lean_ctor_get(x_199, 0);
x_230 = lean_ctor_get(x_199, 1);
x_231 = lean_ctor_get(x_199, 2);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_199);
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_add(x_217, x_232);
lean_dec(x_217);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_229);
lean_ctor_set(x_234, 1, x_230);
lean_ctor_set(x_234, 2, x_231);
lean_ctor_set(x_234, 3, x_233);
lean_ctor_set(x_234, 4, x_218);
if (lean_is_scalar(x_216)) {
 x_235 = lean_alloc_ctor(0, 10, 3);
} else {
 x_235 = x_216;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_204);
lean_ctor_set(x_235, 2, x_205);
lean_ctor_set(x_235, 3, x_206);
lean_ctor_set(x_235, 4, x_207);
lean_ctor_set(x_235, 5, x_208);
lean_ctor_set(x_235, 6, x_209);
lean_ctor_set(x_235, 7, x_210);
lean_ctor_set(x_235, 8, x_211);
lean_ctor_set(x_235, 9, x_212);
lean_ctor_set_uint8(x_235, sizeof(void*)*10, x_213);
lean_ctor_set_uint8(x_235, sizeof(void*)*10 + 1, x_214);
lean_ctor_set_uint8(x_235, sizeof(void*)*10 + 2, x_215);
x_236 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_202);
lean_ctor_set(x_236, 2, x_203);
x_3 = x_201;
x_4 = x_236;
x_5 = x_220;
goto _start;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_190);
if (x_246 == 0)
{
return x_190;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_190, 0);
x_248 = lean_ctor_get(x_190, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_190);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
case 4:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_250 = lean_ctor_get(x_9, 0);
lean_inc(x_250);
lean_dec(x_9);
lean_inc(x_2);
x_251 = l_Lean_Name_append___main(x_250, x_2);
lean_dec(x_250);
x_252 = l_Lean_Elab_Tactic_getEnv___rarg(x_8);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_251);
x_255 = lean_environment_find(x_253, x_251);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
lean_dec(x_251);
lean_inc(x_4);
lean_inc(x_1);
x_256 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_254);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_256);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_256, 0);
lean_dec(x_259);
x_260 = lean_box(0);
lean_ctor_set(x_256, 0, x_260);
return x_256;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
lean_dec(x_256);
x_262 = lean_box(0);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; 
x_264 = lean_ctor_get(x_4, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_256, 1);
lean_inc(x_266);
lean_dec(x_256);
x_267 = lean_ctor_get(x_257, 0);
lean_inc(x_267);
lean_dec(x_257);
x_268 = lean_ctor_get(x_4, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_4, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_264, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_264, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_264, 3);
lean_inc(x_272);
x_273 = lean_ctor_get(x_264, 4);
lean_inc(x_273);
x_274 = lean_ctor_get(x_264, 5);
lean_inc(x_274);
x_275 = lean_ctor_get(x_264, 6);
lean_inc(x_275);
x_276 = lean_ctor_get(x_264, 7);
lean_inc(x_276);
x_277 = lean_ctor_get(x_264, 8);
lean_inc(x_277);
x_278 = lean_ctor_get(x_264, 9);
lean_inc(x_278);
x_279 = lean_ctor_get_uint8(x_264, sizeof(void*)*10);
x_280 = lean_ctor_get_uint8(x_264, sizeof(void*)*10 + 1);
x_281 = lean_ctor_get_uint8(x_264, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 lean_ctor_release(x_264, 5);
 lean_ctor_release(x_264, 6);
 lean_ctor_release(x_264, 7);
 lean_ctor_release(x_264, 8);
 lean_ctor_release(x_264, 9);
 x_282 = x_264;
} else {
 lean_dec_ref(x_264);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_265, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_265, 4);
lean_inc(x_284);
x_285 = lean_nat_dec_eq(x_283, x_284);
if (x_285 == 0)
{
lean_dec(x_4);
x_286 = x_266;
goto block_304;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_306 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_305, x_4, x_266);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_286 = x_307;
goto block_304;
}
else
{
uint8_t x_308; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
return x_306;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_306, 0);
x_310 = lean_ctor_get(x_306, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_306);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
block_304:
{
uint8_t x_287; 
x_287 = !lean_is_exclusive(x_265);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_288 = lean_ctor_get(x_265, 4);
lean_dec(x_288);
x_289 = lean_ctor_get(x_265, 3);
lean_dec(x_289);
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_nat_add(x_283, x_290);
lean_dec(x_283);
lean_ctor_set(x_265, 3, x_291);
if (lean_is_scalar(x_282)) {
 x_292 = lean_alloc_ctor(0, 10, 3);
} else {
 x_292 = x_282;
}
lean_ctor_set(x_292, 0, x_265);
lean_ctor_set(x_292, 1, x_270);
lean_ctor_set(x_292, 2, x_271);
lean_ctor_set(x_292, 3, x_272);
lean_ctor_set(x_292, 4, x_273);
lean_ctor_set(x_292, 5, x_274);
lean_ctor_set(x_292, 6, x_275);
lean_ctor_set(x_292, 7, x_276);
lean_ctor_set(x_292, 8, x_277);
lean_ctor_set(x_292, 9, x_278);
lean_ctor_set_uint8(x_292, sizeof(void*)*10, x_279);
lean_ctor_set_uint8(x_292, sizeof(void*)*10 + 1, x_280);
lean_ctor_set_uint8(x_292, sizeof(void*)*10 + 2, x_281);
x_293 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_268);
lean_ctor_set(x_293, 2, x_269);
x_3 = x_267;
x_4 = x_293;
x_5 = x_286;
goto _start;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_295 = lean_ctor_get(x_265, 0);
x_296 = lean_ctor_get(x_265, 1);
x_297 = lean_ctor_get(x_265, 2);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_265);
x_298 = lean_unsigned_to_nat(1u);
x_299 = lean_nat_add(x_283, x_298);
lean_dec(x_283);
x_300 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_300, 0, x_295);
lean_ctor_set(x_300, 1, x_296);
lean_ctor_set(x_300, 2, x_297);
lean_ctor_set(x_300, 3, x_299);
lean_ctor_set(x_300, 4, x_284);
if (lean_is_scalar(x_282)) {
 x_301 = lean_alloc_ctor(0, 10, 3);
} else {
 x_301 = x_282;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_270);
lean_ctor_set(x_301, 2, x_271);
lean_ctor_set(x_301, 3, x_272);
lean_ctor_set(x_301, 4, x_273);
lean_ctor_set(x_301, 5, x_274);
lean_ctor_set(x_301, 6, x_275);
lean_ctor_set(x_301, 7, x_276);
lean_ctor_set(x_301, 8, x_277);
lean_ctor_set(x_301, 9, x_278);
lean_ctor_set_uint8(x_301, sizeof(void*)*10, x_279);
lean_ctor_set_uint8(x_301, sizeof(void*)*10 + 1, x_280);
lean_ctor_set_uint8(x_301, sizeof(void*)*10 + 2, x_281);
x_302 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_268);
lean_ctor_set(x_302, 2, x_269);
x_3 = x_267;
x_4 = x_302;
x_5 = x_286;
goto _start;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_256);
if (x_312 == 0)
{
return x_256;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_256, 0);
x_314 = lean_ctor_get(x_256, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_256);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_380; 
lean_dec(x_255);
x_316 = l_Lean_Elab_Tactic_save(x_254);
lean_inc(x_4);
lean_inc(x_1);
x_380 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_4, x_254);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_box(0);
x_385 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_385, 0, x_251);
lean_closure_set(x_385, 1, x_384);
x_386 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_387 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_387, 0, x_385);
lean_closure_set(x_387, 1, x_386);
lean_inc(x_1);
x_388 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_388, 0, x_1);
lean_closure_set(x_388, 1, x_387);
lean_inc(x_4);
x_389 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_383, x_388, x_4, x_382);
lean_dec(x_383);
if (lean_obj_tag(x_389) == 0)
{
lean_dec(x_316);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_389;
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
x_317 = x_390;
goto block_379;
}
}
else
{
lean_object* x_391; 
lean_dec(x_251);
x_391 = lean_ctor_get(x_380, 1);
lean_inc(x_391);
lean_dec(x_380);
x_317 = x_391;
goto block_379;
}
block_379:
{
lean_object* x_318; lean_object* x_319; 
x_318 = l_Lean_Elab_Tactic_restore(x_317, x_316);
lean_dec(x_316);
lean_inc(x_4);
lean_inc(x_1);
x_319 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_321 = !lean_is_exclusive(x_319);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_319, 0);
lean_dec(x_322);
x_323 = lean_box(0);
lean_ctor_set(x_319, 0, x_323);
return x_319;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_319, 1);
lean_inc(x_324);
lean_dec(x_319);
x_325 = lean_box(0);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_327 = lean_ctor_get(x_4, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_319, 1);
lean_inc(x_329);
lean_dec(x_319);
x_330 = lean_ctor_get(x_320, 0);
lean_inc(x_330);
lean_dec(x_320);
x_331 = lean_ctor_get(x_4, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_4, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_327, 1);
lean_inc(x_333);
x_334 = lean_ctor_get(x_327, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_327, 3);
lean_inc(x_335);
x_336 = lean_ctor_get(x_327, 4);
lean_inc(x_336);
x_337 = lean_ctor_get(x_327, 5);
lean_inc(x_337);
x_338 = lean_ctor_get(x_327, 6);
lean_inc(x_338);
x_339 = lean_ctor_get(x_327, 7);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 8);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 9);
lean_inc(x_341);
x_342 = lean_ctor_get_uint8(x_327, sizeof(void*)*10);
x_343 = lean_ctor_get_uint8(x_327, sizeof(void*)*10 + 1);
x_344 = lean_ctor_get_uint8(x_327, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 lean_ctor_release(x_327, 4);
 lean_ctor_release(x_327, 5);
 lean_ctor_release(x_327, 6);
 lean_ctor_release(x_327, 7);
 lean_ctor_release(x_327, 8);
 lean_ctor_release(x_327, 9);
 x_345 = x_327;
} else {
 lean_dec_ref(x_327);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_328, 3);
lean_inc(x_346);
x_347 = lean_ctor_get(x_328, 4);
lean_inc(x_347);
x_348 = lean_nat_dec_eq(x_346, x_347);
if (x_348 == 0)
{
lean_dec(x_4);
x_349 = x_329;
goto block_367;
}
else
{
lean_object* x_368; lean_object* x_369; 
x_368 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_369 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_368, x_4, x_329);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec(x_369);
x_349 = x_370;
goto block_367;
}
else
{
uint8_t x_371; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_2);
lean_dec(x_1);
x_371 = !lean_is_exclusive(x_369);
if (x_371 == 0)
{
return x_369;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_369, 0);
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_369);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
block_367:
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_328);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_328, 4);
lean_dec(x_351);
x_352 = lean_ctor_get(x_328, 3);
lean_dec(x_352);
x_353 = lean_unsigned_to_nat(1u);
x_354 = lean_nat_add(x_346, x_353);
lean_dec(x_346);
lean_ctor_set(x_328, 3, x_354);
if (lean_is_scalar(x_345)) {
 x_355 = lean_alloc_ctor(0, 10, 3);
} else {
 x_355 = x_345;
}
lean_ctor_set(x_355, 0, x_328);
lean_ctor_set(x_355, 1, x_333);
lean_ctor_set(x_355, 2, x_334);
lean_ctor_set(x_355, 3, x_335);
lean_ctor_set(x_355, 4, x_336);
lean_ctor_set(x_355, 5, x_337);
lean_ctor_set(x_355, 6, x_338);
lean_ctor_set(x_355, 7, x_339);
lean_ctor_set(x_355, 8, x_340);
lean_ctor_set(x_355, 9, x_341);
lean_ctor_set_uint8(x_355, sizeof(void*)*10, x_342);
lean_ctor_set_uint8(x_355, sizeof(void*)*10 + 1, x_343);
lean_ctor_set_uint8(x_355, sizeof(void*)*10 + 2, x_344);
x_356 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_331);
lean_ctor_set(x_356, 2, x_332);
x_3 = x_330;
x_4 = x_356;
x_5 = x_349;
goto _start;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_358 = lean_ctor_get(x_328, 0);
x_359 = lean_ctor_get(x_328, 1);
x_360 = lean_ctor_get(x_328, 2);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_328);
x_361 = lean_unsigned_to_nat(1u);
x_362 = lean_nat_add(x_346, x_361);
lean_dec(x_346);
x_363 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_363, 0, x_358);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set(x_363, 2, x_360);
lean_ctor_set(x_363, 3, x_362);
lean_ctor_set(x_363, 4, x_347);
if (lean_is_scalar(x_345)) {
 x_364 = lean_alloc_ctor(0, 10, 3);
} else {
 x_364 = x_345;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_333);
lean_ctor_set(x_364, 2, x_334);
lean_ctor_set(x_364, 3, x_335);
lean_ctor_set(x_364, 4, x_336);
lean_ctor_set(x_364, 5, x_337);
lean_ctor_set(x_364, 6, x_338);
lean_ctor_set(x_364, 7, x_339);
lean_ctor_set(x_364, 8, x_340);
lean_ctor_set(x_364, 9, x_341);
lean_ctor_set_uint8(x_364, sizeof(void*)*10, x_342);
lean_ctor_set_uint8(x_364, sizeof(void*)*10 + 1, x_343);
lean_ctor_set_uint8(x_364, sizeof(void*)*10 + 2, x_344);
x_365 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_331);
lean_ctor_set(x_365, 2, x_332);
x_3 = x_330;
x_4 = x_365;
x_5 = x_349;
goto _start;
}
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_375 = !lean_is_exclusive(x_319);
if (x_375 == 0)
{
return x_319;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_319, 0);
x_377 = lean_ctor_get(x_319, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_319);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
}
}
case 5:
{
lean_object* x_392; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_392 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
uint8_t x_394; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_394 = !lean_is_exclusive(x_392);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_392, 0);
lean_dec(x_395);
x_396 = lean_box(0);
lean_ctor_set(x_392, 0, x_396);
return x_392;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_392, 1);
lean_inc(x_397);
lean_dec(x_392);
x_398 = lean_box(0);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_400 = lean_ctor_get(x_4, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_392, 1);
lean_inc(x_402);
lean_dec(x_392);
x_403 = lean_ctor_get(x_393, 0);
lean_inc(x_403);
lean_dec(x_393);
x_404 = lean_ctor_get(x_4, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_4, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_400, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_400, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_400, 3);
lean_inc(x_408);
x_409 = lean_ctor_get(x_400, 4);
lean_inc(x_409);
x_410 = lean_ctor_get(x_400, 5);
lean_inc(x_410);
x_411 = lean_ctor_get(x_400, 6);
lean_inc(x_411);
x_412 = lean_ctor_get(x_400, 7);
lean_inc(x_412);
x_413 = lean_ctor_get(x_400, 8);
lean_inc(x_413);
x_414 = lean_ctor_get(x_400, 9);
lean_inc(x_414);
x_415 = lean_ctor_get_uint8(x_400, sizeof(void*)*10);
x_416 = lean_ctor_get_uint8(x_400, sizeof(void*)*10 + 1);
x_417 = lean_ctor_get_uint8(x_400, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 lean_ctor_release(x_400, 2);
 lean_ctor_release(x_400, 3);
 lean_ctor_release(x_400, 4);
 lean_ctor_release(x_400, 5);
 lean_ctor_release(x_400, 6);
 lean_ctor_release(x_400, 7);
 lean_ctor_release(x_400, 8);
 lean_ctor_release(x_400, 9);
 x_418 = x_400;
} else {
 lean_dec_ref(x_400);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_401, 3);
lean_inc(x_419);
x_420 = lean_ctor_get(x_401, 4);
lean_inc(x_420);
x_421 = lean_nat_dec_eq(x_419, x_420);
if (x_421 == 0)
{
lean_dec(x_4);
x_422 = x_402;
goto block_440;
}
else
{
lean_object* x_441; lean_object* x_442; 
x_441 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_442 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_441, x_4, x_402);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_422 = x_443;
goto block_440;
}
else
{
uint8_t x_444; 
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_2);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_442);
if (x_444 == 0)
{
return x_442;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_442, 0);
x_446 = lean_ctor_get(x_442, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_442);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
block_440:
{
uint8_t x_423; 
x_423 = !lean_is_exclusive(x_401);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_401, 4);
lean_dec(x_424);
x_425 = lean_ctor_get(x_401, 3);
lean_dec(x_425);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_nat_add(x_419, x_426);
lean_dec(x_419);
lean_ctor_set(x_401, 3, x_427);
if (lean_is_scalar(x_418)) {
 x_428 = lean_alloc_ctor(0, 10, 3);
} else {
 x_428 = x_418;
}
lean_ctor_set(x_428, 0, x_401);
lean_ctor_set(x_428, 1, x_406);
lean_ctor_set(x_428, 2, x_407);
lean_ctor_set(x_428, 3, x_408);
lean_ctor_set(x_428, 4, x_409);
lean_ctor_set(x_428, 5, x_410);
lean_ctor_set(x_428, 6, x_411);
lean_ctor_set(x_428, 7, x_412);
lean_ctor_set(x_428, 8, x_413);
lean_ctor_set(x_428, 9, x_414);
lean_ctor_set_uint8(x_428, sizeof(void*)*10, x_415);
lean_ctor_set_uint8(x_428, sizeof(void*)*10 + 1, x_416);
lean_ctor_set_uint8(x_428, sizeof(void*)*10 + 2, x_417);
x_429 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_404);
lean_ctor_set(x_429, 2, x_405);
x_3 = x_403;
x_4 = x_429;
x_5 = x_422;
goto _start;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_431 = lean_ctor_get(x_401, 0);
x_432 = lean_ctor_get(x_401, 1);
x_433 = lean_ctor_get(x_401, 2);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_401);
x_434 = lean_unsigned_to_nat(1u);
x_435 = lean_nat_add(x_419, x_434);
lean_dec(x_419);
x_436 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_436, 0, x_431);
lean_ctor_set(x_436, 1, x_432);
lean_ctor_set(x_436, 2, x_433);
lean_ctor_set(x_436, 3, x_435);
lean_ctor_set(x_436, 4, x_420);
if (lean_is_scalar(x_418)) {
 x_437 = lean_alloc_ctor(0, 10, 3);
} else {
 x_437 = x_418;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_406);
lean_ctor_set(x_437, 2, x_407);
lean_ctor_set(x_437, 3, x_408);
lean_ctor_set(x_437, 4, x_409);
lean_ctor_set(x_437, 5, x_410);
lean_ctor_set(x_437, 6, x_411);
lean_ctor_set(x_437, 7, x_412);
lean_ctor_set(x_437, 8, x_413);
lean_ctor_set(x_437, 9, x_414);
lean_ctor_set_uint8(x_437, sizeof(void*)*10, x_415);
lean_ctor_set_uint8(x_437, sizeof(void*)*10 + 1, x_416);
lean_ctor_set_uint8(x_437, sizeof(void*)*10 + 2, x_417);
x_438 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_404);
lean_ctor_set(x_438, 2, x_405);
x_3 = x_403;
x_4 = x_438;
x_5 = x_422;
goto _start;
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_448 = !lean_is_exclusive(x_392);
if (x_448 == 0)
{
return x_392;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_392, 0);
x_450 = lean_ctor_get(x_392, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_392);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
case 6:
{
lean_object* x_452; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_452 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
if (lean_obj_tag(x_453) == 0)
{
uint8_t x_454; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_454 = !lean_is_exclusive(x_452);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_452, 0);
lean_dec(x_455);
x_456 = lean_box(0);
lean_ctor_set(x_452, 0, x_456);
return x_452;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_452, 1);
lean_inc(x_457);
lean_dec(x_452);
x_458 = lean_box(0);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_460 = lean_ctor_get(x_4, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_452, 1);
lean_inc(x_462);
lean_dec(x_452);
x_463 = lean_ctor_get(x_453, 0);
lean_inc(x_463);
lean_dec(x_453);
x_464 = lean_ctor_get(x_4, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_4, 2);
lean_inc(x_465);
x_466 = lean_ctor_get(x_460, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_460, 2);
lean_inc(x_467);
x_468 = lean_ctor_get(x_460, 3);
lean_inc(x_468);
x_469 = lean_ctor_get(x_460, 4);
lean_inc(x_469);
x_470 = lean_ctor_get(x_460, 5);
lean_inc(x_470);
x_471 = lean_ctor_get(x_460, 6);
lean_inc(x_471);
x_472 = lean_ctor_get(x_460, 7);
lean_inc(x_472);
x_473 = lean_ctor_get(x_460, 8);
lean_inc(x_473);
x_474 = lean_ctor_get(x_460, 9);
lean_inc(x_474);
x_475 = lean_ctor_get_uint8(x_460, sizeof(void*)*10);
x_476 = lean_ctor_get_uint8(x_460, sizeof(void*)*10 + 1);
x_477 = lean_ctor_get_uint8(x_460, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 lean_ctor_release(x_460, 4);
 lean_ctor_release(x_460, 5);
 lean_ctor_release(x_460, 6);
 lean_ctor_release(x_460, 7);
 lean_ctor_release(x_460, 8);
 lean_ctor_release(x_460, 9);
 x_478 = x_460;
} else {
 lean_dec_ref(x_460);
 x_478 = lean_box(0);
}
x_479 = lean_ctor_get(x_461, 3);
lean_inc(x_479);
x_480 = lean_ctor_get(x_461, 4);
lean_inc(x_480);
x_481 = lean_nat_dec_eq(x_479, x_480);
if (x_481 == 0)
{
lean_dec(x_4);
x_482 = x_462;
goto block_500;
}
else
{
lean_object* x_501; lean_object* x_502; 
x_501 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_502 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_501, x_4, x_462);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; 
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
lean_dec(x_502);
x_482 = x_503;
goto block_500;
}
else
{
uint8_t x_504; 
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_2);
lean_dec(x_1);
x_504 = !lean_is_exclusive(x_502);
if (x_504 == 0)
{
return x_502;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_502, 0);
x_506 = lean_ctor_get(x_502, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_502);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
}
}
block_500:
{
uint8_t x_483; 
x_483 = !lean_is_exclusive(x_461);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_484 = lean_ctor_get(x_461, 4);
lean_dec(x_484);
x_485 = lean_ctor_get(x_461, 3);
lean_dec(x_485);
x_486 = lean_unsigned_to_nat(1u);
x_487 = lean_nat_add(x_479, x_486);
lean_dec(x_479);
lean_ctor_set(x_461, 3, x_487);
if (lean_is_scalar(x_478)) {
 x_488 = lean_alloc_ctor(0, 10, 3);
} else {
 x_488 = x_478;
}
lean_ctor_set(x_488, 0, x_461);
lean_ctor_set(x_488, 1, x_466);
lean_ctor_set(x_488, 2, x_467);
lean_ctor_set(x_488, 3, x_468);
lean_ctor_set(x_488, 4, x_469);
lean_ctor_set(x_488, 5, x_470);
lean_ctor_set(x_488, 6, x_471);
lean_ctor_set(x_488, 7, x_472);
lean_ctor_set(x_488, 8, x_473);
lean_ctor_set(x_488, 9, x_474);
lean_ctor_set_uint8(x_488, sizeof(void*)*10, x_475);
lean_ctor_set_uint8(x_488, sizeof(void*)*10 + 1, x_476);
lean_ctor_set_uint8(x_488, sizeof(void*)*10 + 2, x_477);
x_489 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_464);
lean_ctor_set(x_489, 2, x_465);
x_3 = x_463;
x_4 = x_489;
x_5 = x_482;
goto _start;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_491 = lean_ctor_get(x_461, 0);
x_492 = lean_ctor_get(x_461, 1);
x_493 = lean_ctor_get(x_461, 2);
lean_inc(x_493);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_461);
x_494 = lean_unsigned_to_nat(1u);
x_495 = lean_nat_add(x_479, x_494);
lean_dec(x_479);
x_496 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_496, 0, x_491);
lean_ctor_set(x_496, 1, x_492);
lean_ctor_set(x_496, 2, x_493);
lean_ctor_set(x_496, 3, x_495);
lean_ctor_set(x_496, 4, x_480);
if (lean_is_scalar(x_478)) {
 x_497 = lean_alloc_ctor(0, 10, 3);
} else {
 x_497 = x_478;
}
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_466);
lean_ctor_set(x_497, 2, x_467);
lean_ctor_set(x_497, 3, x_468);
lean_ctor_set(x_497, 4, x_469);
lean_ctor_set(x_497, 5, x_470);
lean_ctor_set(x_497, 6, x_471);
lean_ctor_set(x_497, 7, x_472);
lean_ctor_set(x_497, 8, x_473);
lean_ctor_set(x_497, 9, x_474);
lean_ctor_set_uint8(x_497, sizeof(void*)*10, x_475);
lean_ctor_set_uint8(x_497, sizeof(void*)*10 + 1, x_476);
lean_ctor_set_uint8(x_497, sizeof(void*)*10 + 2, x_477);
x_498 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_464);
lean_ctor_set(x_498, 2, x_465);
x_3 = x_463;
x_4 = x_498;
x_5 = x_482;
goto _start;
}
}
}
}
else
{
uint8_t x_508; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_508 = !lean_is_exclusive(x_452);
if (x_508 == 0)
{
return x_452;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_452, 0);
x_510 = lean_ctor_get(x_452, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_452);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
case 7:
{
lean_object* x_512; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_512 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
if (lean_obj_tag(x_513) == 0)
{
uint8_t x_514; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_514 = !lean_is_exclusive(x_512);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_512, 0);
lean_dec(x_515);
x_516 = lean_box(0);
lean_ctor_set(x_512, 0, x_516);
return x_512;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_512, 1);
lean_inc(x_517);
lean_dec(x_512);
x_518 = lean_box(0);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; uint8_t x_536; uint8_t x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; 
x_520 = lean_ctor_get(x_4, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_512, 1);
lean_inc(x_522);
lean_dec(x_512);
x_523 = lean_ctor_get(x_513, 0);
lean_inc(x_523);
lean_dec(x_513);
x_524 = lean_ctor_get(x_4, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_4, 2);
lean_inc(x_525);
x_526 = lean_ctor_get(x_520, 1);
lean_inc(x_526);
x_527 = lean_ctor_get(x_520, 2);
lean_inc(x_527);
x_528 = lean_ctor_get(x_520, 3);
lean_inc(x_528);
x_529 = lean_ctor_get(x_520, 4);
lean_inc(x_529);
x_530 = lean_ctor_get(x_520, 5);
lean_inc(x_530);
x_531 = lean_ctor_get(x_520, 6);
lean_inc(x_531);
x_532 = lean_ctor_get(x_520, 7);
lean_inc(x_532);
x_533 = lean_ctor_get(x_520, 8);
lean_inc(x_533);
x_534 = lean_ctor_get(x_520, 9);
lean_inc(x_534);
x_535 = lean_ctor_get_uint8(x_520, sizeof(void*)*10);
x_536 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 1);
x_537 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 lean_ctor_release(x_520, 2);
 lean_ctor_release(x_520, 3);
 lean_ctor_release(x_520, 4);
 lean_ctor_release(x_520, 5);
 lean_ctor_release(x_520, 6);
 lean_ctor_release(x_520, 7);
 lean_ctor_release(x_520, 8);
 lean_ctor_release(x_520, 9);
 x_538 = x_520;
} else {
 lean_dec_ref(x_520);
 x_538 = lean_box(0);
}
x_539 = lean_ctor_get(x_521, 3);
lean_inc(x_539);
x_540 = lean_ctor_get(x_521, 4);
lean_inc(x_540);
x_541 = lean_nat_dec_eq(x_539, x_540);
if (x_541 == 0)
{
lean_dec(x_4);
x_542 = x_522;
goto block_560;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_562 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_561, x_4, x_522);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_562, 1);
lean_inc(x_563);
lean_dec(x_562);
x_542 = x_563;
goto block_560;
}
else
{
uint8_t x_564; 
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_534);
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_2);
lean_dec(x_1);
x_564 = !lean_is_exclusive(x_562);
if (x_564 == 0)
{
return x_562;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_562, 0);
x_566 = lean_ctor_get(x_562, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_562);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
block_560:
{
uint8_t x_543; 
x_543 = !lean_is_exclusive(x_521);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_544 = lean_ctor_get(x_521, 4);
lean_dec(x_544);
x_545 = lean_ctor_get(x_521, 3);
lean_dec(x_545);
x_546 = lean_unsigned_to_nat(1u);
x_547 = lean_nat_add(x_539, x_546);
lean_dec(x_539);
lean_ctor_set(x_521, 3, x_547);
if (lean_is_scalar(x_538)) {
 x_548 = lean_alloc_ctor(0, 10, 3);
} else {
 x_548 = x_538;
}
lean_ctor_set(x_548, 0, x_521);
lean_ctor_set(x_548, 1, x_526);
lean_ctor_set(x_548, 2, x_527);
lean_ctor_set(x_548, 3, x_528);
lean_ctor_set(x_548, 4, x_529);
lean_ctor_set(x_548, 5, x_530);
lean_ctor_set(x_548, 6, x_531);
lean_ctor_set(x_548, 7, x_532);
lean_ctor_set(x_548, 8, x_533);
lean_ctor_set(x_548, 9, x_534);
lean_ctor_set_uint8(x_548, sizeof(void*)*10, x_535);
lean_ctor_set_uint8(x_548, sizeof(void*)*10 + 1, x_536);
lean_ctor_set_uint8(x_548, sizeof(void*)*10 + 2, x_537);
x_549 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_524);
lean_ctor_set(x_549, 2, x_525);
x_3 = x_523;
x_4 = x_549;
x_5 = x_542;
goto _start;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_551 = lean_ctor_get(x_521, 0);
x_552 = lean_ctor_get(x_521, 1);
x_553 = lean_ctor_get(x_521, 2);
lean_inc(x_553);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_521);
x_554 = lean_unsigned_to_nat(1u);
x_555 = lean_nat_add(x_539, x_554);
lean_dec(x_539);
x_556 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_556, 0, x_551);
lean_ctor_set(x_556, 1, x_552);
lean_ctor_set(x_556, 2, x_553);
lean_ctor_set(x_556, 3, x_555);
lean_ctor_set(x_556, 4, x_540);
if (lean_is_scalar(x_538)) {
 x_557 = lean_alloc_ctor(0, 10, 3);
} else {
 x_557 = x_538;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_526);
lean_ctor_set(x_557, 2, x_527);
lean_ctor_set(x_557, 3, x_528);
lean_ctor_set(x_557, 4, x_529);
lean_ctor_set(x_557, 5, x_530);
lean_ctor_set(x_557, 6, x_531);
lean_ctor_set(x_557, 7, x_532);
lean_ctor_set(x_557, 8, x_533);
lean_ctor_set(x_557, 9, x_534);
lean_ctor_set_uint8(x_557, sizeof(void*)*10, x_535);
lean_ctor_set_uint8(x_557, sizeof(void*)*10 + 1, x_536);
lean_ctor_set_uint8(x_557, sizeof(void*)*10 + 2, x_537);
x_558 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_524);
lean_ctor_set(x_558, 2, x_525);
x_3 = x_523;
x_4 = x_558;
x_5 = x_542;
goto _start;
}
}
}
}
else
{
uint8_t x_568; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_568 = !lean_is_exclusive(x_512);
if (x_568 == 0)
{
return x_512;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_512, 0);
x_570 = lean_ctor_get(x_512, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_512);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
case 8:
{
lean_object* x_572; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_572 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
if (lean_obj_tag(x_573) == 0)
{
uint8_t x_574; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_574 = !lean_is_exclusive(x_572);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; 
x_575 = lean_ctor_get(x_572, 0);
lean_dec(x_575);
x_576 = lean_box(0);
lean_ctor_set(x_572, 0, x_576);
return x_572;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_box(0);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_577);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_596; uint8_t x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; lean_object* x_602; 
x_580 = lean_ctor_get(x_4, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_572, 1);
lean_inc(x_582);
lean_dec(x_572);
x_583 = lean_ctor_get(x_573, 0);
lean_inc(x_583);
lean_dec(x_573);
x_584 = lean_ctor_get(x_4, 1);
lean_inc(x_584);
x_585 = lean_ctor_get(x_4, 2);
lean_inc(x_585);
x_586 = lean_ctor_get(x_580, 1);
lean_inc(x_586);
x_587 = lean_ctor_get(x_580, 2);
lean_inc(x_587);
x_588 = lean_ctor_get(x_580, 3);
lean_inc(x_588);
x_589 = lean_ctor_get(x_580, 4);
lean_inc(x_589);
x_590 = lean_ctor_get(x_580, 5);
lean_inc(x_590);
x_591 = lean_ctor_get(x_580, 6);
lean_inc(x_591);
x_592 = lean_ctor_get(x_580, 7);
lean_inc(x_592);
x_593 = lean_ctor_get(x_580, 8);
lean_inc(x_593);
x_594 = lean_ctor_get(x_580, 9);
lean_inc(x_594);
x_595 = lean_ctor_get_uint8(x_580, sizeof(void*)*10);
x_596 = lean_ctor_get_uint8(x_580, sizeof(void*)*10 + 1);
x_597 = lean_ctor_get_uint8(x_580, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 lean_ctor_release(x_580, 2);
 lean_ctor_release(x_580, 3);
 lean_ctor_release(x_580, 4);
 lean_ctor_release(x_580, 5);
 lean_ctor_release(x_580, 6);
 lean_ctor_release(x_580, 7);
 lean_ctor_release(x_580, 8);
 lean_ctor_release(x_580, 9);
 x_598 = x_580;
} else {
 lean_dec_ref(x_580);
 x_598 = lean_box(0);
}
x_599 = lean_ctor_get(x_581, 3);
lean_inc(x_599);
x_600 = lean_ctor_get(x_581, 4);
lean_inc(x_600);
x_601 = lean_nat_dec_eq(x_599, x_600);
if (x_601 == 0)
{
lean_dec(x_4);
x_602 = x_582;
goto block_620;
}
else
{
lean_object* x_621; lean_object* x_622; 
x_621 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_622 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_621, x_4, x_582);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
lean_dec(x_622);
x_602 = x_623;
goto block_620;
}
else
{
uint8_t x_624; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_583);
lean_dec(x_581);
lean_dec(x_2);
lean_dec(x_1);
x_624 = !lean_is_exclusive(x_622);
if (x_624 == 0)
{
return x_622;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_622, 0);
x_626 = lean_ctor_get(x_622, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_622);
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set(x_627, 1, x_626);
return x_627;
}
}
}
block_620:
{
uint8_t x_603; 
x_603 = !lean_is_exclusive(x_581);
if (x_603 == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_604 = lean_ctor_get(x_581, 4);
lean_dec(x_604);
x_605 = lean_ctor_get(x_581, 3);
lean_dec(x_605);
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_add(x_599, x_606);
lean_dec(x_599);
lean_ctor_set(x_581, 3, x_607);
if (lean_is_scalar(x_598)) {
 x_608 = lean_alloc_ctor(0, 10, 3);
} else {
 x_608 = x_598;
}
lean_ctor_set(x_608, 0, x_581);
lean_ctor_set(x_608, 1, x_586);
lean_ctor_set(x_608, 2, x_587);
lean_ctor_set(x_608, 3, x_588);
lean_ctor_set(x_608, 4, x_589);
lean_ctor_set(x_608, 5, x_590);
lean_ctor_set(x_608, 6, x_591);
lean_ctor_set(x_608, 7, x_592);
lean_ctor_set(x_608, 8, x_593);
lean_ctor_set(x_608, 9, x_594);
lean_ctor_set_uint8(x_608, sizeof(void*)*10, x_595);
lean_ctor_set_uint8(x_608, sizeof(void*)*10 + 1, x_596);
lean_ctor_set_uint8(x_608, sizeof(void*)*10 + 2, x_597);
x_609 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_584);
lean_ctor_set(x_609, 2, x_585);
x_3 = x_583;
x_4 = x_609;
x_5 = x_602;
goto _start;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_611 = lean_ctor_get(x_581, 0);
x_612 = lean_ctor_get(x_581, 1);
x_613 = lean_ctor_get(x_581, 2);
lean_inc(x_613);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_581);
x_614 = lean_unsigned_to_nat(1u);
x_615 = lean_nat_add(x_599, x_614);
lean_dec(x_599);
x_616 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_616, 0, x_611);
lean_ctor_set(x_616, 1, x_612);
lean_ctor_set(x_616, 2, x_613);
lean_ctor_set(x_616, 3, x_615);
lean_ctor_set(x_616, 4, x_600);
if (lean_is_scalar(x_598)) {
 x_617 = lean_alloc_ctor(0, 10, 3);
} else {
 x_617 = x_598;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_586);
lean_ctor_set(x_617, 2, x_587);
lean_ctor_set(x_617, 3, x_588);
lean_ctor_set(x_617, 4, x_589);
lean_ctor_set(x_617, 5, x_590);
lean_ctor_set(x_617, 6, x_591);
lean_ctor_set(x_617, 7, x_592);
lean_ctor_set(x_617, 8, x_593);
lean_ctor_set(x_617, 9, x_594);
lean_ctor_set_uint8(x_617, sizeof(void*)*10, x_595);
lean_ctor_set_uint8(x_617, sizeof(void*)*10 + 1, x_596);
lean_ctor_set_uint8(x_617, sizeof(void*)*10 + 2, x_597);
x_618 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_584);
lean_ctor_set(x_618, 2, x_585);
x_3 = x_583;
x_4 = x_618;
x_5 = x_602;
goto _start;
}
}
}
}
else
{
uint8_t x_628; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_628 = !lean_is_exclusive(x_572);
if (x_628 == 0)
{
return x_572;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_572, 0);
x_630 = lean_ctor_get(x_572, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_572);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
case 9:
{
lean_object* x_632; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_632 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
if (lean_obj_tag(x_633) == 0)
{
uint8_t x_634; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_634 = !lean_is_exclusive(x_632);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_632, 0);
lean_dec(x_635);
x_636 = lean_box(0);
lean_ctor_set(x_632, 0, x_636);
return x_632;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_632, 1);
lean_inc(x_637);
lean_dec(x_632);
x_638 = lean_box(0);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_656; uint8_t x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; lean_object* x_662; 
x_640 = lean_ctor_get(x_4, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_632, 1);
lean_inc(x_642);
lean_dec(x_632);
x_643 = lean_ctor_get(x_633, 0);
lean_inc(x_643);
lean_dec(x_633);
x_644 = lean_ctor_get(x_4, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_4, 2);
lean_inc(x_645);
x_646 = lean_ctor_get(x_640, 1);
lean_inc(x_646);
x_647 = lean_ctor_get(x_640, 2);
lean_inc(x_647);
x_648 = lean_ctor_get(x_640, 3);
lean_inc(x_648);
x_649 = lean_ctor_get(x_640, 4);
lean_inc(x_649);
x_650 = lean_ctor_get(x_640, 5);
lean_inc(x_650);
x_651 = lean_ctor_get(x_640, 6);
lean_inc(x_651);
x_652 = lean_ctor_get(x_640, 7);
lean_inc(x_652);
x_653 = lean_ctor_get(x_640, 8);
lean_inc(x_653);
x_654 = lean_ctor_get(x_640, 9);
lean_inc(x_654);
x_655 = lean_ctor_get_uint8(x_640, sizeof(void*)*10);
x_656 = lean_ctor_get_uint8(x_640, sizeof(void*)*10 + 1);
x_657 = lean_ctor_get_uint8(x_640, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 lean_ctor_release(x_640, 2);
 lean_ctor_release(x_640, 3);
 lean_ctor_release(x_640, 4);
 lean_ctor_release(x_640, 5);
 lean_ctor_release(x_640, 6);
 lean_ctor_release(x_640, 7);
 lean_ctor_release(x_640, 8);
 lean_ctor_release(x_640, 9);
 x_658 = x_640;
} else {
 lean_dec_ref(x_640);
 x_658 = lean_box(0);
}
x_659 = lean_ctor_get(x_641, 3);
lean_inc(x_659);
x_660 = lean_ctor_get(x_641, 4);
lean_inc(x_660);
x_661 = lean_nat_dec_eq(x_659, x_660);
if (x_661 == 0)
{
lean_dec(x_4);
x_662 = x_642;
goto block_680;
}
else
{
lean_object* x_681; lean_object* x_682; 
x_681 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_682 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_681, x_4, x_642);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; 
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
lean_dec(x_682);
x_662 = x_683;
goto block_680;
}
else
{
uint8_t x_684; 
lean_dec(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_641);
lean_dec(x_2);
lean_dec(x_1);
x_684 = !lean_is_exclusive(x_682);
if (x_684 == 0)
{
return x_682;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_682, 0);
x_686 = lean_ctor_get(x_682, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_682);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
block_680:
{
uint8_t x_663; 
x_663 = !lean_is_exclusive(x_641);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_664 = lean_ctor_get(x_641, 4);
lean_dec(x_664);
x_665 = lean_ctor_get(x_641, 3);
lean_dec(x_665);
x_666 = lean_unsigned_to_nat(1u);
x_667 = lean_nat_add(x_659, x_666);
lean_dec(x_659);
lean_ctor_set(x_641, 3, x_667);
if (lean_is_scalar(x_658)) {
 x_668 = lean_alloc_ctor(0, 10, 3);
} else {
 x_668 = x_658;
}
lean_ctor_set(x_668, 0, x_641);
lean_ctor_set(x_668, 1, x_646);
lean_ctor_set(x_668, 2, x_647);
lean_ctor_set(x_668, 3, x_648);
lean_ctor_set(x_668, 4, x_649);
lean_ctor_set(x_668, 5, x_650);
lean_ctor_set(x_668, 6, x_651);
lean_ctor_set(x_668, 7, x_652);
lean_ctor_set(x_668, 8, x_653);
lean_ctor_set(x_668, 9, x_654);
lean_ctor_set_uint8(x_668, sizeof(void*)*10, x_655);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 1, x_656);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 2, x_657);
x_669 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_644);
lean_ctor_set(x_669, 2, x_645);
x_3 = x_643;
x_4 = x_669;
x_5 = x_662;
goto _start;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_671 = lean_ctor_get(x_641, 0);
x_672 = lean_ctor_get(x_641, 1);
x_673 = lean_ctor_get(x_641, 2);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_641);
x_674 = lean_unsigned_to_nat(1u);
x_675 = lean_nat_add(x_659, x_674);
lean_dec(x_659);
x_676 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_676, 0, x_671);
lean_ctor_set(x_676, 1, x_672);
lean_ctor_set(x_676, 2, x_673);
lean_ctor_set(x_676, 3, x_675);
lean_ctor_set(x_676, 4, x_660);
if (lean_is_scalar(x_658)) {
 x_677 = lean_alloc_ctor(0, 10, 3);
} else {
 x_677 = x_658;
}
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_646);
lean_ctor_set(x_677, 2, x_647);
lean_ctor_set(x_677, 3, x_648);
lean_ctor_set(x_677, 4, x_649);
lean_ctor_set(x_677, 5, x_650);
lean_ctor_set(x_677, 6, x_651);
lean_ctor_set(x_677, 7, x_652);
lean_ctor_set(x_677, 8, x_653);
lean_ctor_set(x_677, 9, x_654);
lean_ctor_set_uint8(x_677, sizeof(void*)*10, x_655);
lean_ctor_set_uint8(x_677, sizeof(void*)*10 + 1, x_656);
lean_ctor_set_uint8(x_677, sizeof(void*)*10 + 2, x_657);
x_678 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_644);
lean_ctor_set(x_678, 2, x_645);
x_3 = x_643;
x_4 = x_678;
x_5 = x_662;
goto _start;
}
}
}
}
else
{
uint8_t x_688; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_688 = !lean_is_exclusive(x_632);
if (x_688 == 0)
{
return x_632;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_632, 0);
x_690 = lean_ctor_get(x_632, 1);
lean_inc(x_690);
lean_inc(x_689);
lean_dec(x_632);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
return x_691;
}
}
}
case 10:
{
lean_object* x_692; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_692 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_693; 
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
if (lean_obj_tag(x_693) == 0)
{
uint8_t x_694; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_694 = !lean_is_exclusive(x_692);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; 
x_695 = lean_ctor_get(x_692, 0);
lean_dec(x_695);
x_696 = lean_box(0);
lean_ctor_set(x_692, 0, x_696);
return x_692;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_692, 1);
lean_inc(x_697);
lean_dec(x_692);
x_698 = lean_box(0);
x_699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; uint8_t x_716; uint8_t x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; 
x_700 = lean_ctor_get(x_4, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_692, 1);
lean_inc(x_702);
lean_dec(x_692);
x_703 = lean_ctor_get(x_693, 0);
lean_inc(x_703);
lean_dec(x_693);
x_704 = lean_ctor_get(x_4, 1);
lean_inc(x_704);
x_705 = lean_ctor_get(x_4, 2);
lean_inc(x_705);
x_706 = lean_ctor_get(x_700, 1);
lean_inc(x_706);
x_707 = lean_ctor_get(x_700, 2);
lean_inc(x_707);
x_708 = lean_ctor_get(x_700, 3);
lean_inc(x_708);
x_709 = lean_ctor_get(x_700, 4);
lean_inc(x_709);
x_710 = lean_ctor_get(x_700, 5);
lean_inc(x_710);
x_711 = lean_ctor_get(x_700, 6);
lean_inc(x_711);
x_712 = lean_ctor_get(x_700, 7);
lean_inc(x_712);
x_713 = lean_ctor_get(x_700, 8);
lean_inc(x_713);
x_714 = lean_ctor_get(x_700, 9);
lean_inc(x_714);
x_715 = lean_ctor_get_uint8(x_700, sizeof(void*)*10);
x_716 = lean_ctor_get_uint8(x_700, sizeof(void*)*10 + 1);
x_717 = lean_ctor_get_uint8(x_700, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 lean_ctor_release(x_700, 2);
 lean_ctor_release(x_700, 3);
 lean_ctor_release(x_700, 4);
 lean_ctor_release(x_700, 5);
 lean_ctor_release(x_700, 6);
 lean_ctor_release(x_700, 7);
 lean_ctor_release(x_700, 8);
 lean_ctor_release(x_700, 9);
 x_718 = x_700;
} else {
 lean_dec_ref(x_700);
 x_718 = lean_box(0);
}
x_719 = lean_ctor_get(x_701, 3);
lean_inc(x_719);
x_720 = lean_ctor_get(x_701, 4);
lean_inc(x_720);
x_721 = lean_nat_dec_eq(x_719, x_720);
if (x_721 == 0)
{
lean_dec(x_4);
x_722 = x_702;
goto block_740;
}
else
{
lean_object* x_741; lean_object* x_742; 
x_741 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_742 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_741, x_4, x_702);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec(x_742);
x_722 = x_743;
goto block_740;
}
else
{
uint8_t x_744; 
lean_dec(x_720);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_2);
lean_dec(x_1);
x_744 = !lean_is_exclusive(x_742);
if (x_744 == 0)
{
return x_742;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = lean_ctor_get(x_742, 0);
x_746 = lean_ctor_get(x_742, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_742);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
return x_747;
}
}
}
block_740:
{
uint8_t x_723; 
x_723 = !lean_is_exclusive(x_701);
if (x_723 == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_724 = lean_ctor_get(x_701, 4);
lean_dec(x_724);
x_725 = lean_ctor_get(x_701, 3);
lean_dec(x_725);
x_726 = lean_unsigned_to_nat(1u);
x_727 = lean_nat_add(x_719, x_726);
lean_dec(x_719);
lean_ctor_set(x_701, 3, x_727);
if (lean_is_scalar(x_718)) {
 x_728 = lean_alloc_ctor(0, 10, 3);
} else {
 x_728 = x_718;
}
lean_ctor_set(x_728, 0, x_701);
lean_ctor_set(x_728, 1, x_706);
lean_ctor_set(x_728, 2, x_707);
lean_ctor_set(x_728, 3, x_708);
lean_ctor_set(x_728, 4, x_709);
lean_ctor_set(x_728, 5, x_710);
lean_ctor_set(x_728, 6, x_711);
lean_ctor_set(x_728, 7, x_712);
lean_ctor_set(x_728, 8, x_713);
lean_ctor_set(x_728, 9, x_714);
lean_ctor_set_uint8(x_728, sizeof(void*)*10, x_715);
lean_ctor_set_uint8(x_728, sizeof(void*)*10 + 1, x_716);
lean_ctor_set_uint8(x_728, sizeof(void*)*10 + 2, x_717);
x_729 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_704);
lean_ctor_set(x_729, 2, x_705);
x_3 = x_703;
x_4 = x_729;
x_5 = x_722;
goto _start;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_731 = lean_ctor_get(x_701, 0);
x_732 = lean_ctor_get(x_701, 1);
x_733 = lean_ctor_get(x_701, 2);
lean_inc(x_733);
lean_inc(x_732);
lean_inc(x_731);
lean_dec(x_701);
x_734 = lean_unsigned_to_nat(1u);
x_735 = lean_nat_add(x_719, x_734);
lean_dec(x_719);
x_736 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_736, 0, x_731);
lean_ctor_set(x_736, 1, x_732);
lean_ctor_set(x_736, 2, x_733);
lean_ctor_set(x_736, 3, x_735);
lean_ctor_set(x_736, 4, x_720);
if (lean_is_scalar(x_718)) {
 x_737 = lean_alloc_ctor(0, 10, 3);
} else {
 x_737 = x_718;
}
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_706);
lean_ctor_set(x_737, 2, x_707);
lean_ctor_set(x_737, 3, x_708);
lean_ctor_set(x_737, 4, x_709);
lean_ctor_set(x_737, 5, x_710);
lean_ctor_set(x_737, 6, x_711);
lean_ctor_set(x_737, 7, x_712);
lean_ctor_set(x_737, 8, x_713);
lean_ctor_set(x_737, 9, x_714);
lean_ctor_set_uint8(x_737, sizeof(void*)*10, x_715);
lean_ctor_set_uint8(x_737, sizeof(void*)*10 + 1, x_716);
lean_ctor_set_uint8(x_737, sizeof(void*)*10 + 2, x_717);
x_738 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_704);
lean_ctor_set(x_738, 2, x_705);
x_3 = x_703;
x_4 = x_738;
x_5 = x_722;
goto _start;
}
}
}
}
else
{
uint8_t x_748; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_748 = !lean_is_exclusive(x_692);
if (x_748 == 0)
{
return x_692;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_692, 0);
x_750 = lean_ctor_get(x_692, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_692);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
case 11:
{
lean_object* x_752; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_752 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
if (lean_obj_tag(x_753) == 0)
{
uint8_t x_754; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_754 = !lean_is_exclusive(x_752);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_752, 0);
lean_dec(x_755);
x_756 = lean_box(0);
lean_ctor_set(x_752, 0, x_756);
return x_752;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_752, 1);
lean_inc(x_757);
lean_dec(x_752);
x_758 = lean_box(0);
x_759 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
return x_759;
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; uint8_t x_775; uint8_t x_776; uint8_t x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; lean_object* x_782; 
x_760 = lean_ctor_get(x_4, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_752, 1);
lean_inc(x_762);
lean_dec(x_752);
x_763 = lean_ctor_get(x_753, 0);
lean_inc(x_763);
lean_dec(x_753);
x_764 = lean_ctor_get(x_4, 1);
lean_inc(x_764);
x_765 = lean_ctor_get(x_4, 2);
lean_inc(x_765);
x_766 = lean_ctor_get(x_760, 1);
lean_inc(x_766);
x_767 = lean_ctor_get(x_760, 2);
lean_inc(x_767);
x_768 = lean_ctor_get(x_760, 3);
lean_inc(x_768);
x_769 = lean_ctor_get(x_760, 4);
lean_inc(x_769);
x_770 = lean_ctor_get(x_760, 5);
lean_inc(x_770);
x_771 = lean_ctor_get(x_760, 6);
lean_inc(x_771);
x_772 = lean_ctor_get(x_760, 7);
lean_inc(x_772);
x_773 = lean_ctor_get(x_760, 8);
lean_inc(x_773);
x_774 = lean_ctor_get(x_760, 9);
lean_inc(x_774);
x_775 = lean_ctor_get_uint8(x_760, sizeof(void*)*10);
x_776 = lean_ctor_get_uint8(x_760, sizeof(void*)*10 + 1);
x_777 = lean_ctor_get_uint8(x_760, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 lean_ctor_release(x_760, 1);
 lean_ctor_release(x_760, 2);
 lean_ctor_release(x_760, 3);
 lean_ctor_release(x_760, 4);
 lean_ctor_release(x_760, 5);
 lean_ctor_release(x_760, 6);
 lean_ctor_release(x_760, 7);
 lean_ctor_release(x_760, 8);
 lean_ctor_release(x_760, 9);
 x_778 = x_760;
} else {
 lean_dec_ref(x_760);
 x_778 = lean_box(0);
}
x_779 = lean_ctor_get(x_761, 3);
lean_inc(x_779);
x_780 = lean_ctor_get(x_761, 4);
lean_inc(x_780);
x_781 = lean_nat_dec_eq(x_779, x_780);
if (x_781 == 0)
{
lean_dec(x_4);
x_782 = x_762;
goto block_800;
}
else
{
lean_object* x_801; lean_object* x_802; 
x_801 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_802 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_801, x_4, x_762);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; 
x_803 = lean_ctor_get(x_802, 1);
lean_inc(x_803);
lean_dec(x_802);
x_782 = x_803;
goto block_800;
}
else
{
uint8_t x_804; 
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_761);
lean_dec(x_2);
lean_dec(x_1);
x_804 = !lean_is_exclusive(x_802);
if (x_804 == 0)
{
return x_802;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_802, 0);
x_806 = lean_ctor_get(x_802, 1);
lean_inc(x_806);
lean_inc(x_805);
lean_dec(x_802);
x_807 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
return x_807;
}
}
}
block_800:
{
uint8_t x_783; 
x_783 = !lean_is_exclusive(x_761);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_784 = lean_ctor_get(x_761, 4);
lean_dec(x_784);
x_785 = lean_ctor_get(x_761, 3);
lean_dec(x_785);
x_786 = lean_unsigned_to_nat(1u);
x_787 = lean_nat_add(x_779, x_786);
lean_dec(x_779);
lean_ctor_set(x_761, 3, x_787);
if (lean_is_scalar(x_778)) {
 x_788 = lean_alloc_ctor(0, 10, 3);
} else {
 x_788 = x_778;
}
lean_ctor_set(x_788, 0, x_761);
lean_ctor_set(x_788, 1, x_766);
lean_ctor_set(x_788, 2, x_767);
lean_ctor_set(x_788, 3, x_768);
lean_ctor_set(x_788, 4, x_769);
lean_ctor_set(x_788, 5, x_770);
lean_ctor_set(x_788, 6, x_771);
lean_ctor_set(x_788, 7, x_772);
lean_ctor_set(x_788, 8, x_773);
lean_ctor_set(x_788, 9, x_774);
lean_ctor_set_uint8(x_788, sizeof(void*)*10, x_775);
lean_ctor_set_uint8(x_788, sizeof(void*)*10 + 1, x_776);
lean_ctor_set_uint8(x_788, sizeof(void*)*10 + 2, x_777);
x_789 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_764);
lean_ctor_set(x_789, 2, x_765);
x_3 = x_763;
x_4 = x_789;
x_5 = x_782;
goto _start;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_791 = lean_ctor_get(x_761, 0);
x_792 = lean_ctor_get(x_761, 1);
x_793 = lean_ctor_get(x_761, 2);
lean_inc(x_793);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_761);
x_794 = lean_unsigned_to_nat(1u);
x_795 = lean_nat_add(x_779, x_794);
lean_dec(x_779);
x_796 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_796, 0, x_791);
lean_ctor_set(x_796, 1, x_792);
lean_ctor_set(x_796, 2, x_793);
lean_ctor_set(x_796, 3, x_795);
lean_ctor_set(x_796, 4, x_780);
if (lean_is_scalar(x_778)) {
 x_797 = lean_alloc_ctor(0, 10, 3);
} else {
 x_797 = x_778;
}
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_766);
lean_ctor_set(x_797, 2, x_767);
lean_ctor_set(x_797, 3, x_768);
lean_ctor_set(x_797, 4, x_769);
lean_ctor_set(x_797, 5, x_770);
lean_ctor_set(x_797, 6, x_771);
lean_ctor_set(x_797, 7, x_772);
lean_ctor_set(x_797, 8, x_773);
lean_ctor_set(x_797, 9, x_774);
lean_ctor_set_uint8(x_797, sizeof(void*)*10, x_775);
lean_ctor_set_uint8(x_797, sizeof(void*)*10 + 1, x_776);
lean_ctor_set_uint8(x_797, sizeof(void*)*10 + 2, x_777);
x_798 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_764);
lean_ctor_set(x_798, 2, x_765);
x_3 = x_763;
x_4 = x_798;
x_5 = x_782;
goto _start;
}
}
}
}
else
{
uint8_t x_808; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_808 = !lean_is_exclusive(x_752);
if (x_808 == 0)
{
return x_752;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_752, 0);
x_810 = lean_ctor_get(x_752, 1);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_752);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
}
default: 
{
lean_object* x_812; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_812 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; 
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
if (lean_obj_tag(x_813) == 0)
{
uint8_t x_814; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_814 = !lean_is_exclusive(x_812);
if (x_814 == 0)
{
lean_object* x_815; lean_object* x_816; 
x_815 = lean_ctor_get(x_812, 0);
lean_dec(x_815);
x_816 = lean_box(0);
lean_ctor_set(x_812, 0, x_816);
return x_812;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_812, 1);
lean_inc(x_817);
lean_dec(x_812);
x_818 = lean_box(0);
x_819 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_817);
return x_819;
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; uint8_t x_836; uint8_t x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; uint8_t x_841; lean_object* x_842; 
x_820 = lean_ctor_get(x_4, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_812, 1);
lean_inc(x_822);
lean_dec(x_812);
x_823 = lean_ctor_get(x_813, 0);
lean_inc(x_823);
lean_dec(x_813);
x_824 = lean_ctor_get(x_4, 1);
lean_inc(x_824);
x_825 = lean_ctor_get(x_4, 2);
lean_inc(x_825);
x_826 = lean_ctor_get(x_820, 1);
lean_inc(x_826);
x_827 = lean_ctor_get(x_820, 2);
lean_inc(x_827);
x_828 = lean_ctor_get(x_820, 3);
lean_inc(x_828);
x_829 = lean_ctor_get(x_820, 4);
lean_inc(x_829);
x_830 = lean_ctor_get(x_820, 5);
lean_inc(x_830);
x_831 = lean_ctor_get(x_820, 6);
lean_inc(x_831);
x_832 = lean_ctor_get(x_820, 7);
lean_inc(x_832);
x_833 = lean_ctor_get(x_820, 8);
lean_inc(x_833);
x_834 = lean_ctor_get(x_820, 9);
lean_inc(x_834);
x_835 = lean_ctor_get_uint8(x_820, sizeof(void*)*10);
x_836 = lean_ctor_get_uint8(x_820, sizeof(void*)*10 + 1);
x_837 = lean_ctor_get_uint8(x_820, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_820)) {
 lean_ctor_release(x_820, 0);
 lean_ctor_release(x_820, 1);
 lean_ctor_release(x_820, 2);
 lean_ctor_release(x_820, 3);
 lean_ctor_release(x_820, 4);
 lean_ctor_release(x_820, 5);
 lean_ctor_release(x_820, 6);
 lean_ctor_release(x_820, 7);
 lean_ctor_release(x_820, 8);
 lean_ctor_release(x_820, 9);
 x_838 = x_820;
} else {
 lean_dec_ref(x_820);
 x_838 = lean_box(0);
}
x_839 = lean_ctor_get(x_821, 3);
lean_inc(x_839);
x_840 = lean_ctor_get(x_821, 4);
lean_inc(x_840);
x_841 = lean_nat_dec_eq(x_839, x_840);
if (x_841 == 0)
{
lean_dec(x_4);
x_842 = x_822;
goto block_860;
}
else
{
lean_object* x_861; lean_object* x_862; 
x_861 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_1);
x_862 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_861, x_4, x_822);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; 
x_863 = lean_ctor_get(x_862, 1);
lean_inc(x_863);
lean_dec(x_862);
x_842 = x_863;
goto block_860;
}
else
{
uint8_t x_864; 
lean_dec(x_840);
lean_dec(x_839);
lean_dec(x_838);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_828);
lean_dec(x_827);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_821);
lean_dec(x_2);
lean_dec(x_1);
x_864 = !lean_is_exclusive(x_862);
if (x_864 == 0)
{
return x_862;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_862, 0);
x_866 = lean_ctor_get(x_862, 1);
lean_inc(x_866);
lean_inc(x_865);
lean_dec(x_862);
x_867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_867, 0, x_865);
lean_ctor_set(x_867, 1, x_866);
return x_867;
}
}
}
block_860:
{
uint8_t x_843; 
x_843 = !lean_is_exclusive(x_821);
if (x_843 == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_844 = lean_ctor_get(x_821, 4);
lean_dec(x_844);
x_845 = lean_ctor_get(x_821, 3);
lean_dec(x_845);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_add(x_839, x_846);
lean_dec(x_839);
lean_ctor_set(x_821, 3, x_847);
if (lean_is_scalar(x_838)) {
 x_848 = lean_alloc_ctor(0, 10, 3);
} else {
 x_848 = x_838;
}
lean_ctor_set(x_848, 0, x_821);
lean_ctor_set(x_848, 1, x_826);
lean_ctor_set(x_848, 2, x_827);
lean_ctor_set(x_848, 3, x_828);
lean_ctor_set(x_848, 4, x_829);
lean_ctor_set(x_848, 5, x_830);
lean_ctor_set(x_848, 6, x_831);
lean_ctor_set(x_848, 7, x_832);
lean_ctor_set(x_848, 8, x_833);
lean_ctor_set(x_848, 9, x_834);
lean_ctor_set_uint8(x_848, sizeof(void*)*10, x_835);
lean_ctor_set_uint8(x_848, sizeof(void*)*10 + 1, x_836);
lean_ctor_set_uint8(x_848, sizeof(void*)*10 + 2, x_837);
x_849 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_824);
lean_ctor_set(x_849, 2, x_825);
x_3 = x_823;
x_4 = x_849;
x_5 = x_842;
goto _start;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_851 = lean_ctor_get(x_821, 0);
x_852 = lean_ctor_get(x_821, 1);
x_853 = lean_ctor_get(x_821, 2);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_dec(x_821);
x_854 = lean_unsigned_to_nat(1u);
x_855 = lean_nat_add(x_839, x_854);
lean_dec(x_839);
x_856 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_856, 0, x_851);
lean_ctor_set(x_856, 1, x_852);
lean_ctor_set(x_856, 2, x_853);
lean_ctor_set(x_856, 3, x_855);
lean_ctor_set(x_856, 4, x_840);
if (lean_is_scalar(x_838)) {
 x_857 = lean_alloc_ctor(0, 10, 3);
} else {
 x_857 = x_838;
}
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_826);
lean_ctor_set(x_857, 2, x_827);
lean_ctor_set(x_857, 3, x_828);
lean_ctor_set(x_857, 4, x_829);
lean_ctor_set(x_857, 5, x_830);
lean_ctor_set(x_857, 6, x_831);
lean_ctor_set(x_857, 7, x_832);
lean_ctor_set(x_857, 8, x_833);
lean_ctor_set(x_857, 9, x_834);
lean_ctor_set_uint8(x_857, sizeof(void*)*10, x_835);
lean_ctor_set_uint8(x_857, sizeof(void*)*10 + 1, x_836);
lean_ctor_set_uint8(x_857, sizeof(void*)*10 + 2, x_837);
x_858 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_824);
lean_ctor_set(x_858, 2, x_825);
x_3 = x_823;
x_4 = x_858;
x_5 = x_842;
goto _start;
}
}
}
}
else
{
uint8_t x_868; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_868 = !lean_is_exclusive(x_812);
if (x_868 == 0)
{
return x_812;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_869 = lean_ctor_get(x_812, 0);
x_870 = lean_ctor_get(x_812, 1);
lean_inc(x_870);
lean_inc(x_869);
lean_dec(x_812);
x_871 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_871, 0, x_869);
lean_ctor_set(x_871, 1, x_870);
return x_871;
}
}
}
}
}
else
{
uint8_t x_872; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_872 = !lean_is_exclusive(x_6);
if (x_872 == 0)
{
return x_6;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_6, 0);
x_874 = lean_ctor_get(x_6, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_6);
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_875, 1, x_874);
return x_875;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_1 = l_Lean_registerTagAttribute___lambda__4___closed__4;
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
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Elab_Tactic_inferType(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_1, x_3, x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Tactic_resolveGlobalName(x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_15 = x_36;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_13);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Elab_Tactic_save(x_14);
lean_inc(x_4);
lean_inc(x_1);
x_42 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_4, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_47, 0, x_40);
lean_closure_set(x_47, 1, x_46);
lean_inc(x_1);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_47);
lean_inc(x_4);
x_49 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_45, x_48, x_4, x_44);
lean_dec(x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Elab_Tactic_restore(x_50, x_41);
lean_dec(x_41);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_3);
x_53 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_Term_mkConst___closed__4;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_56, x_4, x_51);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_40);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_dec(x_42);
x_59 = l_Lean_Elab_Tactic_restore(x_58, x_41);
lean_dec(x_41);
x_60 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_60, 0, x_3);
x_61 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Elab_Term_mkConst___closed__4;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_64, x_4, x_59);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_39);
lean_dec(x_37);
x_66 = lean_box(0);
x_23 = x_66;
goto block_35;
}
}
else
{
lean_object* x_67; 
lean_dec(x_38);
lean_dec(x_37);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_13);
x_68 = lean_box(0);
x_15 = x_68;
goto block_22;
}
else
{
lean_object* x_69; 
lean_dec(x_67);
x_69 = lean_box(0);
x_23 = x_69;
goto block_35;
}
}
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_3);
x_17 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_mkConst___closed__4;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_20, x_4, x_14);
return x_21;
}
block_35:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_3);
x_25 = l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Tactic_getRecFromUsing___closed__8;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_13);
x_30 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_33, x_4, x_14);
return x_34;
}
}
else
{
uint8_t x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_12);
if (x_70 == 0)
{
return x_12;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_12, 0);
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_12);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_9);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_9, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_10, 0);
lean_inc(x_76);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_76);
return x_9;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_9, 1);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_ctor_get(x_10, 0);
lean_inc(x_78);
lean_dec(x_10);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_9);
if (x_80 == 0)
{
return x_9;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_9, 0);
x_82 = lean_ctor_get(x_9, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_9);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_6);
if (x_84 == 0)
{
return x_6;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_6, 0);
x_86 = lean_ctor_get(x_6, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_6);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
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
x_8 = l_Lean_Parser_Tactic_underscoreFn___closed__4;
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_10, x_18, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_18, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
if (x_2 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_8);
lean_dec(x_16);
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_9);
x_23 = l_Lean_Name_toString___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_10);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_5);
lean_inc(x_1);
x_31 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_30, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_3 = x_32;
x_4 = x_11;
x_6 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
x_39 = lean_box(0);
x_40 = lean_array_push(x_13, x_39);
x_41 = lean_box(0);
x_42 = lean_array_push(x_16, x_41);
lean_ctor_set(x_8, 0, x_42);
lean_ctor_set(x_3, 0, x_40);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_10);
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
lean_dec(x_19);
x_45 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_44);
x_46 = l_Array_toList___rarg(x_45);
lean_dec(x_45);
x_47 = lean_array_push(x_13, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = l_Lean_Syntax_getArg(x_44, x_48);
lean_dec(x_44);
x_50 = lean_array_push(x_16, x_49);
lean_ctor_set(x_8, 0, x_50);
lean_ctor_set(x_3, 0, x_47);
x_4 = x_11;
goto _start;
}
}
else
{
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_9, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_9, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_22);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = l_Lean_Syntax_inhabited;
x_58 = lean_array_get(x_57, x_18, x_56);
x_59 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_58);
x_60 = l_Array_toList___rarg(x_59);
lean_dec(x_59);
x_61 = lean_array_push(x_13, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = l_Lean_Syntax_getArg(x_58, x_62);
x_64 = lean_array_push(x_16, x_63);
x_65 = l_Array_eraseIdx___rarg(x_18, x_56);
lean_dec(x_56);
lean_ctor_set(x_22, 0, x_58);
lean_ctor_set(x_9, 1, x_22);
lean_ctor_set(x_9, 0, x_65);
lean_ctor_set(x_8, 0, x_64);
lean_ctor_set(x_3, 0, x_61);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_22, 0);
lean_inc(x_67);
lean_dec(x_22);
x_68 = l_Lean_Syntax_inhabited;
x_69 = lean_array_get(x_68, x_18, x_67);
x_70 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_69);
x_71 = l_Array_toList___rarg(x_70);
lean_dec(x_70);
x_72 = lean_array_push(x_13, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = l_Lean_Syntax_getArg(x_69, x_73);
x_75 = lean_array_push(x_16, x_74);
x_76 = l_Array_eraseIdx___rarg(x_18, x_67);
lean_dec(x_67);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_9, 1, x_77);
lean_ctor_set(x_9, 0, x_76);
lean_ctor_set(x_8, 0, x_75);
lean_ctor_set(x_3, 0, x_72);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_9);
x_79 = lean_ctor_get(x_22, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_80 = x_22;
} else {
 lean_dec_ref(x_22);
 x_80 = lean_box(0);
}
x_81 = l_Lean_Syntax_inhabited;
x_82 = lean_array_get(x_81, x_18, x_79);
x_83 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_82);
x_84 = l_Array_toList___rarg(x_83);
lean_dec(x_83);
x_85 = lean_array_push(x_13, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = l_Lean_Syntax_getArg(x_82, x_86);
x_88 = lean_array_push(x_16, x_87);
x_89 = l_Array_eraseIdx___rarg(x_18, x_79);
lean_dec(x_79);
if (lean_is_scalar(x_80)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_80;
}
lean_ctor_set(x_90, 0, x_82);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_8, 1, x_91);
lean_ctor_set(x_8, 0, x_88);
lean_ctor_set(x_3, 0, x_85);
x_4 = x_11;
goto _start;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
x_93 = !lean_is_exclusive(x_9);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_94 = lean_ctor_get(x_9, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_9, 0);
lean_dec(x_95);
x_96 = lean_ctor_get(x_21, 0);
lean_inc(x_96);
lean_dec(x_21);
x_97 = l_Lean_Syntax_inhabited;
x_98 = lean_array_get(x_97, x_18, x_96);
x_99 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_98);
x_100 = l_Array_toList___rarg(x_99);
lean_dec(x_99);
x_101 = lean_array_push(x_13, x_100);
x_102 = lean_unsigned_to_nat(3u);
x_103 = l_Lean_Syntax_getArg(x_98, x_102);
lean_dec(x_98);
x_104 = lean_array_push(x_16, x_103);
x_105 = l_Array_eraseIdx___rarg(x_18, x_96);
lean_dec(x_96);
lean_ctor_set(x_9, 0, x_105);
lean_ctor_set(x_8, 0, x_104);
lean_ctor_set(x_3, 0, x_101);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_9);
x_107 = lean_ctor_get(x_21, 0);
lean_inc(x_107);
lean_dec(x_21);
x_108 = l_Lean_Syntax_inhabited;
x_109 = lean_array_get(x_108, x_18, x_107);
x_110 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_109);
x_111 = l_Array_toList___rarg(x_110);
lean_dec(x_110);
x_112 = lean_array_push(x_13, x_111);
x_113 = lean_unsigned_to_nat(3u);
x_114 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_115 = lean_array_push(x_16, x_114);
x_116 = l_Array_eraseIdx___rarg(x_18, x_107);
lean_dec(x_107);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_19);
lean_ctor_set(x_8, 1, x_117);
lean_ctor_set(x_8, 0, x_115);
lean_ctor_set(x_3, 0, x_112);
x_4 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_8, 0);
lean_inc(x_119);
lean_dec(x_8);
x_120 = lean_ctor_get(x_9, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_9, 1);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_10, x_120, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_120, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_dec(x_120);
if (lean_obj_tag(x_121) == 0)
{
if (x_2 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_119);
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_9);
x_125 = l_Lean_Name_toString___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_10);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_5);
lean_inc(x_1);
x_133 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_132, x_5, x_6);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_3 = x_134;
x_4 = x_11;
x_6 = x_135;
goto _start;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
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
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_10);
x_141 = lean_box(0);
x_142 = lean_array_push(x_13, x_141);
x_143 = lean_box(0);
x_144 = lean_array_push(x_119, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_9);
lean_ctor_set(x_3, 1, x_145);
lean_ctor_set(x_3, 0, x_142);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_10);
x_147 = lean_ctor_get(x_121, 0);
lean_inc(x_147);
lean_dec(x_121);
x_148 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_147);
x_149 = l_Array_toList___rarg(x_148);
lean_dec(x_148);
x_150 = lean_array_push(x_13, x_149);
x_151 = lean_unsigned_to_nat(3u);
x_152 = l_Lean_Syntax_getArg(x_147, x_151);
lean_dec(x_147);
x_153 = lean_array_push(x_119, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_9);
lean_ctor_set(x_3, 1, x_154);
lean_ctor_set(x_3, 0, x_150);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_121);
lean_dec(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_156 = x_9;
} else {
 lean_dec_ref(x_9);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_124, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_158 = x_124;
} else {
 lean_dec_ref(x_124);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Syntax_inhabited;
x_160 = lean_array_get(x_159, x_120, x_157);
x_161 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_160);
x_162 = l_Array_toList___rarg(x_161);
lean_dec(x_161);
x_163 = lean_array_push(x_13, x_162);
x_164 = lean_unsigned_to_nat(3u);
x_165 = l_Lean_Syntax_getArg(x_160, x_164);
x_166 = lean_array_push(x_119, x_165);
x_167 = l_Array_eraseIdx___rarg(x_120, x_157);
lean_dec(x_157);
if (lean_is_scalar(x_158)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_158;
}
lean_ctor_set(x_168, 0, x_160);
if (lean_is_scalar(x_156)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_156;
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_3, 1, x_170);
lean_ctor_set(x_3, 0, x_163);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_172 = x_9;
} else {
 lean_dec_ref(x_9);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_123, 0);
lean_inc(x_173);
lean_dec(x_123);
x_174 = l_Lean_Syntax_inhabited;
x_175 = lean_array_get(x_174, x_120, x_173);
x_176 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_175);
x_177 = l_Array_toList___rarg(x_176);
lean_dec(x_176);
x_178 = lean_array_push(x_13, x_177);
x_179 = lean_unsigned_to_nat(3u);
x_180 = l_Lean_Syntax_getArg(x_175, x_179);
lean_dec(x_175);
x_181 = lean_array_push(x_119, x_180);
x_182 = l_Array_eraseIdx___rarg(x_120, x_173);
lean_dec(x_173);
if (lean_is_scalar(x_172)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_172;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_121);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_3, 1, x_184);
lean_ctor_set(x_3, 0, x_178);
x_4 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_186 = lean_ctor_get(x_3, 0);
lean_inc(x_186);
lean_dec(x_3);
x_187 = lean_ctor_get(x_8, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_188 = x_8;
} else {
 lean_dec_ref(x_8);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_9, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_9, 1);
lean_inc(x_190);
x_191 = lean_unsigned_to_nat(0u);
x_192 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_10, x_189, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_189, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_dec(x_189);
if (lean_obj_tag(x_190) == 0)
{
if (x_2 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_9);
x_194 = l_Lean_Name_toString___closed__1;
x_195 = l_Lean_Name_toStringWithSep___main(x_194, x_10);
x_196 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__3;
x_199 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_201 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_5);
lean_inc(x_1);
x_202 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_201, x_5, x_6);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_3 = x_203;
x_4 = x_11;
x_6 = x_204;
goto _start;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_208 = x_202;
} else {
 lean_dec_ref(x_202);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_10);
x_210 = lean_box(0);
x_211 = lean_array_push(x_186, x_210);
x_212 = lean_box(0);
x_213 = lean_array_push(x_187, x_212);
if (lean_is_scalar(x_188)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_188;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_9);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_214);
x_3 = x_215;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_10);
x_217 = lean_ctor_get(x_190, 0);
lean_inc(x_217);
lean_dec(x_190);
x_218 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_217);
x_219 = l_Array_toList___rarg(x_218);
lean_dec(x_218);
x_220 = lean_array_push(x_186, x_219);
x_221 = lean_unsigned_to_nat(3u);
x_222 = l_Lean_Syntax_getArg(x_217, x_221);
lean_dec(x_217);
x_223 = lean_array_push(x_187, x_222);
if (lean_is_scalar(x_188)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_188;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_9);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_224);
x_3 = x_225;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_190);
lean_dec(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_227 = x_9;
} else {
 lean_dec_ref(x_9);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_193, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_229 = x_193;
} else {
 lean_dec_ref(x_193);
 x_229 = lean_box(0);
}
x_230 = l_Lean_Syntax_inhabited;
x_231 = lean_array_get(x_230, x_189, x_228);
x_232 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_231);
x_233 = l_Array_toList___rarg(x_232);
lean_dec(x_232);
x_234 = lean_array_push(x_186, x_233);
x_235 = lean_unsigned_to_nat(3u);
x_236 = l_Lean_Syntax_getArg(x_231, x_235);
x_237 = lean_array_push(x_187, x_236);
x_238 = l_Array_eraseIdx___rarg(x_189, x_228);
lean_dec(x_228);
if (lean_is_scalar(x_229)) {
 x_239 = lean_alloc_ctor(1, 1, 0);
} else {
 x_239 = x_229;
}
lean_ctor_set(x_239, 0, x_231);
if (lean_is_scalar(x_227)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_227;
}
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
if (lean_is_scalar(x_188)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_188;
}
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_234);
lean_ctor_set(x_242, 1, x_241);
x_3 = x_242;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_244 = x_9;
} else {
 lean_dec_ref(x_9);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_192, 0);
lean_inc(x_245);
lean_dec(x_192);
x_246 = l_Lean_Syntax_inhabited;
x_247 = lean_array_get(x_246, x_189, x_245);
x_248 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_247);
x_249 = l_Array_toList___rarg(x_248);
lean_dec(x_248);
x_250 = lean_array_push(x_186, x_249);
x_251 = lean_unsigned_to_nat(3u);
x_252 = l_Lean_Syntax_getArg(x_247, x_251);
lean_dec(x_247);
x_253 = lean_array_push(x_187, x_252);
x_254 = l_Array_eraseIdx___rarg(x_189, x_245);
lean_dec(x_245);
if (lean_is_scalar(x_244)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_244;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_190);
if (lean_is_scalar(x_188)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_188;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_250);
lean_ctor_set(x_257, 1, x_256);
x_3 = x_257;
x_4 = x_11;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Elab_Tactic_getInductiveValFromMajor(x_1, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_mkRecFor___closed__1;
x_14 = lean_name_mk_string(x_12, x_13);
x_15 = l_Lean_Syntax_isNone(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_9, 4);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_3);
x_18 = lean_box(0);
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Array_empty___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_24 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_16, x_17, x_23, x_5, x_10);
lean_dec(x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_5);
lean_inc(x_16);
x_26 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_1, x_4, x_22, x_16, x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_26, 1);
x_32 = lean_ctor_get(x_26, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_dec(x_37);
x_38 = l_Array_isEmpty___rarg(x_36);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
x_40 = l_List_redLength___main___rarg(x_16);
x_41 = lean_mk_empty_array_with_capacity(x_40);
lean_dec(x_40);
x_42 = l_List_toArrayAux___main___rarg(x_16, x_41);
lean_ctor_set(x_29, 1, x_42);
lean_ctor_set(x_29, 0, x_39);
if (x_38 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_26);
x_43 = l_Lean_Syntax_inhabited;
x_44 = lean_array_get(x_43, x_36, x_23);
lean_dec(x_36);
x_45 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_46 = l_Lean_Elab_Tactic_throwError___rarg(x_44, x_45, x_5, x_31);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_29);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_29);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_5);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
lean_dec(x_29);
x_56 = l_Array_isEmpty___rarg(x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_33);
lean_ctor_set(x_57, 2, x_34);
x_58 = l_List_redLength___main___rarg(x_16);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l_List_toArrayAux___main___rarg(x_16, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
if (x_56 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_26);
x_62 = l_Lean_Syntax_inhabited;
x_63 = lean_array_get(x_62, x_55, x_23);
lean_dec(x_55);
x_64 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_65 = l_Lean_Elab_Tactic_throwError___rarg(x_63, x_64, x_5, x_31);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
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
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_dec(x_55);
lean_dec(x_5);
lean_ctor_set(x_26, 0, x_61);
return x_26;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_dec(x_26);
x_74 = lean_ctor_get(x_27, 0);
lean_inc(x_74);
lean_dec(x_27);
x_75 = lean_ctor_get(x_28, 0);
lean_inc(x_75);
lean_dec(x_28);
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_77 = x_29;
} else {
 lean_dec_ref(x_29);
 x_77 = lean_box(0);
}
x_78 = l_Array_isEmpty___rarg(x_76);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_14);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
x_80 = l_List_redLength___main___rarg(x_16);
x_81 = lean_mk_empty_array_with_capacity(x_80);
lean_dec(x_80);
x_82 = l_List_toArrayAux___main___rarg(x_16, x_81);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
if (x_78 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = l_Lean_Syntax_inhabited;
x_85 = lean_array_get(x_84, x_76, x_23);
lean_dec(x_76);
x_86 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_87 = l_Lean_Elab_Tactic_throwError___rarg(x_85, x_86, x_5, x_73);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_83);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
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
else
{
lean_object* x_95; 
lean_dec(x_76);
lean_dec(x_5);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_83);
lean_ctor_set(x_95, 1, x_73);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_26);
if (x_96 == 0)
{
return x_26;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_26, 0);
x_98 = lean_ctor_get(x_26, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_26);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_24);
if (x_100 == 0)
{
return x_24;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_24, 0);
x_102 = lean_ctor_get(x_24, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_24);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_104 = l_Array_empty___closed__1;
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_14);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_7, 0, x_106);
return x_7;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = lean_ctor_get(x_7, 0);
x_108 = lean_ctor_get(x_7, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_7);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_mkRecFor___closed__1;
x_112 = lean_name_mk_string(x_110, x_111);
x_113 = l_Lean_Syntax_isNone(x_3);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_107, 4);
lean_inc(x_114);
lean_dec(x_107);
x_115 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_3);
x_116 = lean_box(0);
lean_inc(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_empty___closed__1;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_122 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_114, x_115, x_121, x_5, x_108);
lean_dec(x_115);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
lean_inc(x_5);
lean_inc(x_114);
x_124 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_1, x_4, x_120, x_114, x_5, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_129 = x_124;
} else {
 lean_dec_ref(x_124);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
x_134 = l_Array_isEmpty___rarg(x_132);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_112);
lean_ctor_set(x_135, 1, x_130);
lean_ctor_set(x_135, 2, x_131);
x_136 = l_List_redLength___main___rarg(x_114);
x_137 = lean_mk_empty_array_with_capacity(x_136);
lean_dec(x_136);
x_138 = l_List_toArrayAux___main___rarg(x_114, x_137);
if (lean_is_scalar(x_133)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_133;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_138);
if (x_134 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_129);
x_140 = l_Lean_Syntax_inhabited;
x_141 = lean_array_get(x_140, x_132, x_121);
lean_dec(x_132);
x_142 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_143 = l_Lean_Elab_Tactic_throwError___rarg(x_141, x_142, x_5, x_128);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
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
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_139);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
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
lean_object* x_151; 
lean_dec(x_132);
lean_dec(x_5);
if (lean_is_scalar(x_129)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_129;
}
lean_ctor_set(x_151, 0, x_139);
lean_ctor_set(x_151, 1, x_128);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_5);
x_152 = lean_ctor_get(x_124, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_124, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_154 = x_124;
} else {
 lean_dec_ref(x_124);
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
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_120);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_5);
lean_dec(x_1);
x_156 = lean_ctor_get(x_122, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_122, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_158 = x_122;
} else {
 lean_dec_ref(x_122);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_107);
lean_dec(x_5);
lean_dec(x_1);
x_160 = l_Array_empty___closed__1;
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_112);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_108);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_5);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_7);
if (x_164 == 0)
{
return x_7;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_7, 0);
x_166 = lean_ctor_get(x_7, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_7);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
return x_8;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_nat_sub(x_4, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Lean_Meta_RecursorInfo_isMinor(x_2, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l_Lean_Name_inhabited;
x_18 = lean_array_get(x_17, x_3, x_14);
lean_dec(x_14);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
x_29 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_18, x_27, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_27, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_19);
lean_dec(x_25);
lean_free_object(x_6);
lean_dec(x_22);
lean_dec(x_20);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_18);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_7);
lean_inc(x_1);
x_39 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_38, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_5 = x_12;
x_6 = x_40;
x_8 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_18);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec(x_28);
x_48 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_47);
x_49 = l_Array_toList___rarg(x_48);
lean_dec(x_48);
x_50 = lean_array_push(x_22, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = l_Lean_Syntax_getArg(x_47, x_51);
lean_dec(x_47);
x_53 = lean_array_push(x_25, x_52);
lean_ctor_set(x_19, 0, x_53);
lean_ctor_set(x_6, 0, x_50);
x_5 = x_12;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_28);
lean_dec(x_18);
x_55 = !lean_is_exclusive(x_20);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_20, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_20, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_30);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = l_Lean_Syntax_inhabited;
x_61 = lean_array_get(x_60, x_27, x_59);
x_62 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_61);
x_63 = l_Array_toList___rarg(x_62);
lean_dec(x_62);
x_64 = lean_array_push(x_22, x_63);
x_65 = lean_unsigned_to_nat(3u);
x_66 = l_Lean_Syntax_getArg(x_61, x_65);
x_67 = lean_array_push(x_25, x_66);
x_68 = l_Array_eraseIdx___rarg(x_27, x_59);
lean_dec(x_59);
lean_ctor_set(x_30, 0, x_61);
lean_ctor_set(x_20, 1, x_30);
lean_ctor_set(x_20, 0, x_68);
lean_ctor_set(x_19, 0, x_67);
lean_ctor_set(x_6, 0, x_64);
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_30, 0);
lean_inc(x_70);
lean_dec(x_30);
x_71 = l_Lean_Syntax_inhabited;
x_72 = lean_array_get(x_71, x_27, x_70);
x_73 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_72);
x_74 = l_Array_toList___rarg(x_73);
lean_dec(x_73);
x_75 = lean_array_push(x_22, x_74);
x_76 = lean_unsigned_to_nat(3u);
x_77 = l_Lean_Syntax_getArg(x_72, x_76);
x_78 = lean_array_push(x_25, x_77);
x_79 = l_Array_eraseIdx___rarg(x_27, x_70);
lean_dec(x_70);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_20, 1, x_80);
lean_ctor_set(x_20, 0, x_79);
lean_ctor_set(x_19, 0, x_78);
lean_ctor_set(x_6, 0, x_75);
x_5 = x_12;
goto _start;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_20);
x_82 = lean_ctor_get(x_30, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_83 = x_30;
} else {
 lean_dec_ref(x_30);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Syntax_inhabited;
x_85 = lean_array_get(x_84, x_27, x_82);
x_86 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_85);
x_87 = l_Array_toList___rarg(x_86);
lean_dec(x_86);
x_88 = lean_array_push(x_22, x_87);
x_89 = lean_unsigned_to_nat(3u);
x_90 = l_Lean_Syntax_getArg(x_85, x_89);
x_91 = lean_array_push(x_25, x_90);
x_92 = l_Array_eraseIdx___rarg(x_27, x_82);
lean_dec(x_82);
if (lean_is_scalar(x_83)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_83;
}
lean_ctor_set(x_93, 0, x_85);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_19, 1, x_94);
lean_ctor_set(x_19, 0, x_91);
lean_ctor_set(x_6, 0, x_88);
x_5 = x_12;
goto _start;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_18);
x_96 = !lean_is_exclusive(x_20);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_ctor_get(x_20, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_20, 0);
lean_dec(x_98);
x_99 = lean_ctor_get(x_29, 0);
lean_inc(x_99);
lean_dec(x_29);
x_100 = l_Lean_Syntax_inhabited;
x_101 = lean_array_get(x_100, x_27, x_99);
x_102 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_101);
x_103 = l_Array_toList___rarg(x_102);
lean_dec(x_102);
x_104 = lean_array_push(x_22, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = l_Lean_Syntax_getArg(x_101, x_105);
lean_dec(x_101);
x_107 = lean_array_push(x_25, x_106);
x_108 = l_Array_eraseIdx___rarg(x_27, x_99);
lean_dec(x_99);
lean_ctor_set(x_20, 0, x_108);
lean_ctor_set(x_19, 0, x_107);
lean_ctor_set(x_6, 0, x_104);
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_20);
x_110 = lean_ctor_get(x_29, 0);
lean_inc(x_110);
lean_dec(x_29);
x_111 = l_Lean_Syntax_inhabited;
x_112 = lean_array_get(x_111, x_27, x_110);
x_113 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_112);
x_114 = l_Array_toList___rarg(x_113);
lean_dec(x_113);
x_115 = lean_array_push(x_22, x_114);
x_116 = lean_unsigned_to_nat(3u);
x_117 = l_Lean_Syntax_getArg(x_112, x_116);
lean_dec(x_112);
x_118 = lean_array_push(x_25, x_117);
x_119 = l_Array_eraseIdx___rarg(x_27, x_110);
lean_dec(x_110);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_28);
lean_ctor_set(x_19, 1, x_120);
lean_ctor_set(x_19, 0, x_118);
lean_ctor_set(x_6, 0, x_115);
x_5 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_19, 0);
lean_inc(x_122);
lean_dec(x_19);
x_123 = lean_ctor_get(x_20, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_20, 1);
lean_inc(x_124);
x_125 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_18, x_123, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_123, x_9);
if (lean_obj_tag(x_126) == 0)
{
lean_dec(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_122);
lean_free_object(x_6);
lean_dec(x_22);
lean_dec(x_20);
x_127 = l_Lean_Name_toString___closed__1;
x_128 = l_Lean_Name_toStringWithSep___main(x_127, x_18);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_inc(x_7);
lean_inc(x_1);
x_135 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_134, x_7, x_8);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_5 = x_12;
x_6 = x_136;
x_8 = x_137;
goto _start;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_141 = x_135;
} else {
 lean_dec_ref(x_135);
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
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_18);
x_143 = lean_ctor_get(x_124, 0);
lean_inc(x_143);
lean_dec(x_124);
x_144 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_143);
x_145 = l_Array_toList___rarg(x_144);
lean_dec(x_144);
x_146 = lean_array_push(x_22, x_145);
x_147 = lean_unsigned_to_nat(3u);
x_148 = l_Lean_Syntax_getArg(x_143, x_147);
lean_dec(x_143);
x_149 = lean_array_push(x_122, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_20);
lean_ctor_set(x_6, 1, x_150);
lean_ctor_set(x_6, 0, x_146);
x_5 = x_12;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_124);
lean_dec(x_18);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_152 = x_20;
} else {
 lean_dec_ref(x_20);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_126, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_154 = x_126;
} else {
 lean_dec_ref(x_126);
 x_154 = lean_box(0);
}
x_155 = l_Lean_Syntax_inhabited;
x_156 = lean_array_get(x_155, x_123, x_153);
x_157 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_156);
x_158 = l_Array_toList___rarg(x_157);
lean_dec(x_157);
x_159 = lean_array_push(x_22, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = l_Lean_Syntax_getArg(x_156, x_160);
x_162 = lean_array_push(x_122, x_161);
x_163 = l_Array_eraseIdx___rarg(x_123, x_153);
lean_dec(x_153);
if (lean_is_scalar(x_154)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_154;
}
lean_ctor_set(x_164, 0, x_156);
if (lean_is_scalar(x_152)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_152;
}
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_6, 1, x_166);
lean_ctor_set(x_6, 0, x_159);
x_5 = x_12;
goto _start;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_18);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_168 = x_20;
} else {
 lean_dec_ref(x_20);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_125, 0);
lean_inc(x_169);
lean_dec(x_125);
x_170 = l_Lean_Syntax_inhabited;
x_171 = lean_array_get(x_170, x_123, x_169);
x_172 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_171);
x_173 = l_Array_toList___rarg(x_172);
lean_dec(x_172);
x_174 = lean_array_push(x_22, x_173);
x_175 = lean_unsigned_to_nat(3u);
x_176 = l_Lean_Syntax_getArg(x_171, x_175);
lean_dec(x_171);
x_177 = lean_array_push(x_122, x_176);
x_178 = l_Array_eraseIdx___rarg(x_123, x_169);
lean_dec(x_169);
if (lean_is_scalar(x_168)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_168;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_124);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_6, 1, x_180);
lean_ctor_set(x_6, 0, x_174);
x_5 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_6, 0);
lean_inc(x_182);
lean_dec(x_6);
x_183 = lean_ctor_get(x_19, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_184 = x_19;
} else {
 lean_dec_ref(x_19);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_20, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_20, 1);
lean_inc(x_186);
x_187 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_18, x_185, x_9);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_185, x_9);
if (lean_obj_tag(x_188) == 0)
{
lean_dec(x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_20);
x_189 = l_Lean_Name_toString___closed__1;
x_190 = l_Lean_Name_toStringWithSep___main(x_189, x_18);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__6;
x_196 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
lean_inc(x_7);
lean_inc(x_1);
x_197 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_196, x_7, x_8);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_5 = x_12;
x_6 = x_198;
x_8 = x_199;
goto _start;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
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
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_18);
x_205 = lean_ctor_get(x_186, 0);
lean_inc(x_205);
lean_dec(x_186);
x_206 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_205);
x_207 = l_Array_toList___rarg(x_206);
lean_dec(x_206);
x_208 = lean_array_push(x_182, x_207);
x_209 = lean_unsigned_to_nat(3u);
x_210 = l_Lean_Syntax_getArg(x_205, x_209);
lean_dec(x_205);
x_211 = lean_array_push(x_183, x_210);
if (lean_is_scalar(x_184)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_184;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_20);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_208);
lean_ctor_set(x_213, 1, x_212);
x_5 = x_12;
x_6 = x_213;
goto _start;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_186);
lean_dec(x_18);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_215 = x_20;
} else {
 lean_dec_ref(x_20);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_188, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_217 = x_188;
} else {
 lean_dec_ref(x_188);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Syntax_inhabited;
x_219 = lean_array_get(x_218, x_185, x_216);
x_220 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_219);
x_221 = l_Array_toList___rarg(x_220);
lean_dec(x_220);
x_222 = lean_array_push(x_182, x_221);
x_223 = lean_unsigned_to_nat(3u);
x_224 = l_Lean_Syntax_getArg(x_219, x_223);
x_225 = lean_array_push(x_183, x_224);
x_226 = l_Array_eraseIdx___rarg(x_185, x_216);
lean_dec(x_216);
if (lean_is_scalar(x_217)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_217;
}
lean_ctor_set(x_227, 0, x_219);
if (lean_is_scalar(x_215)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_215;
}
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_184)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_184;
}
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_222);
lean_ctor_set(x_230, 1, x_229);
x_5 = x_12;
x_6 = x_230;
goto _start;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_18);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_232 = x_20;
} else {
 lean_dec_ref(x_20);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_187, 0);
lean_inc(x_233);
lean_dec(x_187);
x_234 = l_Lean_Syntax_inhabited;
x_235 = lean_array_get(x_234, x_185, x_233);
x_236 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_235);
x_237 = l_Array_toList___rarg(x_236);
lean_dec(x_236);
x_238 = lean_array_push(x_182, x_237);
x_239 = lean_unsigned_to_nat(3u);
x_240 = l_Lean_Syntax_getArg(x_235, x_239);
lean_dec(x_235);
x_241 = lean_array_push(x_183, x_240);
x_242 = l_Array_eraseIdx___rarg(x_185, x_233);
lean_dec(x_233);
if (lean_is_scalar(x_232)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_232;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_186);
if (lean_is_scalar(x_184)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_184;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_238);
lean_ctor_set(x_245, 1, x_244);
x_5 = x_12;
x_6 = x_245;
goto _start;
}
}
}
}
else
{
lean_object* x_247; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_6);
lean_ctor_set(x_247, 1, x_8);
return x_247;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getIdAt(x_6, x_10);
lean_dec(x_6);
x_12 = l_Lean_Name_eraseMacroScopes(x_11);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l_Lean_Elab_Tactic_getRecFromUsing(x_1, x_2, x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lean_Syntax_isNone(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_dec(x_25);
lean_inc(x_17);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_26, 0, x_17);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_26);
lean_inc(x_3);
x_28 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_24, x_27, x_3, x_22);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
lean_ctor_set(x_21, 1, x_31);
lean_ctor_set(x_21, 0, x_19);
x_32 = l_Array_empty___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_get_size(x_29);
lean_inc(x_3);
lean_inc(x_35);
x_36 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_1, x_15, x_29, x_35, x_35, x_34, x_3, x_30);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l_Array_isEmpty___rarg(x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_36);
x_48 = l_Lean_Syntax_inhabited;
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get(x_48, x_45, x_49);
lean_dec(x_45);
x_51 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_52 = l_Lean_Elab_Tactic_throwError___rarg(x_50, x_51, x_3, x_41);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_47);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_47);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_dec(x_45);
lean_dec(x_3);
lean_ctor_set(x_36, 0, x_47);
return x_36;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
lean_dec(x_36);
x_62 = lean_ctor_get(x_37, 0);
lean_inc(x_62);
lean_dec(x_37);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
lean_dec(x_38);
x_64 = lean_ctor_get(x_39, 0);
lean_inc(x_64);
lean_dec(x_39);
x_65 = l_Array_isEmpty___rarg(x_64);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_63);
if (x_65 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l_Lean_Syntax_inhabited;
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get(x_67, x_64, x_68);
lean_dec(x_64);
x_70 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_71 = l_Lean_Elab_Tactic_throwError___rarg(x_69, x_70, x_3, x_61);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_64);
lean_dec(x_3);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_61);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_17);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_36);
if (x_80 == 0)
{
return x_36;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_36, 0);
x_82 = lean_ctor_get(x_36, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
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
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_28);
if (x_84 == 0)
{
return x_28;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_28, 0);
x_86 = lean_ctor_get(x_28, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_28);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_21, 0);
lean_inc(x_88);
lean_dec(x_21);
lean_inc(x_17);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_89, 0, x_17);
lean_inc(x_1);
x_90 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_90, 0, x_1);
lean_closure_set(x_90, 1, x_89);
lean_inc(x_3);
x_91 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_88, x_90, x_3, x_22);
lean_dec(x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_19);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Array_empty___closed__1;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_get_size(x_92);
lean_inc(x_3);
lean_inc(x_99);
x_100 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_1, x_15, x_92, x_99, x_99, x_98, x_3, x_93);
lean_dec(x_99);
lean_dec(x_92);
lean_dec(x_15);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
lean_dec(x_103);
x_109 = l_Array_isEmpty___rarg(x_108);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_17);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
if (x_109 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_105);
x_111 = l_Lean_Syntax_inhabited;
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_array_get(x_111, x_108, x_112);
lean_dec(x_108);
x_114 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_115 = l_Lean_Elab_Tactic_throwError___rarg(x_113, x_114, x_3, x_104);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
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
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_110);
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
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
else
{
lean_object* x_123; 
lean_dec(x_108);
lean_dec(x_3);
if (lean_is_scalar(x_105)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_105;
}
lean_ctor_set(x_123, 0, x_110);
lean_ctor_set(x_123, 1, x_104);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_17);
lean_dec(x_3);
x_124 = lean_ctor_get(x_100, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_100, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_126 = x_100;
} else {
 lean_dec_ref(x_100);
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
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_128 = lean_ctor_get(x_91, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_91, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_130 = x_91;
} else {
 lean_dec_ref(x_91);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_20);
if (x_132 == 0)
{
return x_20;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_20, 0);
x_134 = lean_ctor_get(x_20, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_20);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_136 = l_Array_empty___closed__1;
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_17);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_13, 0, x_137);
return x_13;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_13, 0);
x_139 = lean_ctor_get(x_13, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_13);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = l_Lean_Syntax_isNone(x_8);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_143 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_139);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
lean_inc(x_140);
x_148 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_148, 0, x_140);
lean_inc(x_1);
x_149 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_149, 0, x_1);
lean_closure_set(x_149, 1, x_148);
lean_inc(x_3);
x_150 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_146, x_149, x_3, x_145);
lean_dec(x_146);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_box(0);
if (lean_is_scalar(x_147)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_147;
}
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Array_empty___closed__1;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_get_size(x_151);
lean_inc(x_3);
lean_inc(x_158);
x_159 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_1, x_138, x_151, x_158, x_158, x_157, x_3, x_152);
lean_dec(x_158);
lean_dec(x_151);
lean_dec(x_138);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_164 = x_159;
} else {
 lean_dec_ref(x_159);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
lean_dec(x_161);
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
lean_dec(x_162);
x_168 = l_Array_isEmpty___rarg(x_167);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_140);
lean_ctor_set(x_169, 1, x_165);
lean_ctor_set(x_169, 2, x_166);
if (x_168 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_164);
x_170 = l_Lean_Syntax_inhabited;
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_array_get(x_170, x_167, x_171);
lean_dec(x_167);
x_173 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_174 = l_Lean_Elab_Tactic_throwError___rarg(x_172, x_173, x_3, x_163);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_169);
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_180 = x_174;
} else {
 lean_dec_ref(x_174);
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
lean_object* x_182; 
lean_dec(x_167);
lean_dec(x_3);
if (lean_is_scalar(x_164)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_164;
}
lean_ctor_set(x_182, 0, x_169);
lean_ctor_set(x_182, 1, x_163);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_140);
lean_dec(x_3);
x_183 = lean_ctor_get(x_159, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_159, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_185 = x_159;
} else {
 lean_dec_ref(x_159);
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
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_138);
lean_dec(x_3);
lean_dec(x_1);
x_187 = lean_ctor_get(x_150, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_150, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_189 = x_150;
} else {
 lean_dec_ref(x_150);
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
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_138);
lean_dec(x_3);
lean_dec(x_1);
x_191 = lean_ctor_get(x_143, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_143, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_193 = x_143;
} else {
 lean_dec_ref(x_143);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_195 = l_Array_empty___closed__1;
x_196 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_196, 0, x_140);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_139);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_13);
if (x_198 == 0)
{
return x_13;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_13, 0);
x_200 = lean_ctor_get(x_13, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_13);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; lean_object* x_203; 
lean_dec(x_6);
x_202 = 0;
x_203 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_1, x_2, x_8, x_202, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec(x_205);
lean_ctor_set(x_203, 0, x_206);
return x_203;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_203, 0);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_203);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_203);
if (x_211 == 0)
{
return x_203;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_203, 0);
x_213 = lean_ctor_get(x_203, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_203);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
lean_inc(x_1);
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
lean_inc(x_1);
x_13 = l_Lean_Elab_Tactic_ensureHasType(x_1, x_8, x_11, x_5, x_12);
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
x_18 = l_Lean_Elab_Tactic_collectMVars(x_1, x_14, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
lean_inc(x_19);
x_22 = l_List_append___rarg(x_3, x_19);
x_23 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_24 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_21, x_23, x_19, x_5, x_20);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
lean_inc(x_17);
x_24 = l_Lean_Elab_Tactic_evalTactic___main(x_17, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_6);
x_26 = l_Lean_Elab_Tactic_done(x_17, x_6, x_25);
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
lean_dec(x_17);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_18);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_37, 0, x_18);
lean_inc(x_18);
x_38 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1), 6, 3);
lean_closure_set(x_38, 0, x_17);
lean_closure_set(x_38, 1, x_18);
lean_closure_set(x_38, 2, x_5);
x_39 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
lean_inc(x_6);
x_40 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_18, x_39, x_6, x_7);
lean_dec(x_18);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_4 = x_11;
x_5 = x_41;
x_7 = x_42;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_6);
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
else
{
lean_object* x_48; 
lean_dec(x_6);
lean_dec(x_4);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_inc(x_17);
x_24 = l_Lean_Elab_Tactic_evalTactic___main(x_17, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_6);
x_26 = l_Lean_Elab_Tactic_done(x_17, x_6, x_25);
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
lean_dec(x_17);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_18);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_37, 0, x_18);
lean_inc(x_18);
x_38 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1), 6, 3);
lean_closure_set(x_38, 0, x_17);
lean_closure_set(x_38, 1, x_18);
lean_closure_set(x_38, 2, x_5);
x_39 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
lean_inc(x_6);
x_40 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_18, x_39, x_6, x_7);
lean_dec(x_18);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_4 = x_11;
x_5 = x_41;
x_7 = x_42;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_6);
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
else
{
lean_object* x_48; 
lean_dec(x_6);
lean_dec(x_4);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(x_9);
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
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_eq(x_7, x_8);
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_8);
x_11 = l_Nat_repr(x_8);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Nat_repr(x_7);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__10;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_4);
x_26 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_25, x_4, x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_4);
lean_inc(x_8);
x_28 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(x_2, x_3, x_8, x_8, x_10, x_4, x_27);
lean_dec(x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Tactic_setGoals(x_29, x_4, x_30);
lean_dec(x_4);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
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
lean_dec(x_8);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_8);
x_40 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_2, x_3, x_8, x_8, x_10, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Tactic_setGoals(x_41, x_4, x_42);
lean_dec(x_4);
return x_43;
}
else
{
uint8_t x_44; 
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
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_1);
x_48 = l_Array_toList___rarg(x_3);
x_49 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(x_48);
x_50 = l_Lean_Elab_Tactic_setGoals(x_49, x_4, x_5);
lean_dec(x_4);
return x_50;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_1, x_2, x_3, x_4);
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
lean_inc(x_1);
x_8 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_1);
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
lean_inc(x_1);
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_12);
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
lean_inc(x_1);
x_23 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_1, x_22, x_3, x_15);
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
x_27 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_1, x_26, x_24, x_3, x_25);
lean_dec(x_24);
lean_dec(x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__1), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Tactic_focusAux___rarg(x_1, x_8, x_2, x_3);
return x_9;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_fget(x_2, x_5);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_21, x_7, x_8);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_fget(x_4, x_6);
x_24 = l_Lean_Syntax_isMissing(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = l_Lean_Name_inhabited;
x_26 = lean_array_get(x_25, x_3, x_6);
x_27 = lean_array_get_size(x_2);
x_28 = lean_nat_dec_lt(x_5, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_33, x_7, x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_array_fget(x_2, x_5);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_name_eq(x_26, x_36);
lean_dec(x_26);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec(x_5);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_42, x_7, x_8);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_36);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_5, x_44);
lean_dec(x_5);
x_46 = lean_nat_add(x_6, x_44);
lean_dec(x_6);
x_5 = x_45;
x_6 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_6, x_48);
lean_dec(x_6);
x_6 = x_49;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_8, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_inc(x_1);
x_5 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_7);
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
lean_inc(x_1);
x_15 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_1, x_6, x_13, x_14, x_3, x_10);
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
lean_inc(x_1);
x_25 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_1, x_24, x_3, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_18, 2);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_26);
x_29 = x_26;
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(x_30, x_29);
x_32 = x_31;
lean_inc(x_28);
x_33 = l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(x_28, x_30, x_30);
lean_inc(x_3);
lean_inc(x_1);
x_34 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_1, x_26, x_19, x_28, x_3, x_27);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_1, x_33, x_32, x_3, x_35);
lean_dec(x_32);
lean_dec(x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__1), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Tactic_focusAux___rarg(x_1, x_8, x_2, x_3);
return x_9;
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
l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__10 = _init_l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__10);
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
