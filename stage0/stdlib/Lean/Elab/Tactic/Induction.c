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
lean_object* l_Lean_Elab_Tactic_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withRef___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(lean_object*);
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_15__isTermRHS___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_cases___elambda__1___closed__1;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
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
extern lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
extern lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(lean_object*);
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
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__4;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1), 4, 1);
lean_closure_set(x_13, 0, x_7);
x_14 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_evalGeneralizeAux(x_2, x_11, x_7, x_4, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_15, x_4, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_inc(x_4);
x_7 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Tactic_getFVarIds(x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_8, 9);
x_11 = l_Lean_Elab_replaceRef(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 9, x_11);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_5, x_13);
lean_dec(x_5);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 5, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_15);
x_18 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_17, x_2, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
x_21 = lean_ctor_get(x_8, 2);
x_22 = lean_ctor_get(x_8, 3);
x_23 = lean_ctor_get(x_8, 4);
x_24 = lean_ctor_get(x_8, 5);
x_25 = lean_ctor_get(x_8, 6);
x_26 = lean_ctor_get(x_8, 7);
x_27 = lean_ctor_get(x_8, 8);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_31 = lean_ctor_get(x_8, 9);
lean_inc(x_31);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_32 = l_Lean_Elab_replaceRef(x_1, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_24);
lean_ctor_set(x_33, 6, x_25);
lean_ctor_set(x_33, 7, x_26);
lean_ctor_set(x_33, 8, x_27);
lean_ctor_set(x_33, 9, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*10, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 1, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 2, x_30);
lean_ctor_set(x_2, 0, x_33);
lean_inc(x_5);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_5);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_5, x_35);
lean_dec(x_5);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_38 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_39 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 5, 3);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_34);
lean_closure_set(x_39, 2, x_37);
x_40 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_39, x_2, x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 7);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 8);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_41, sizeof(void*)*10);
x_53 = lean_ctor_get_uint8(x_41, sizeof(void*)*10 + 1);
x_54 = lean_ctor_get_uint8(x_41, sizeof(void*)*10 + 2);
x_55 = lean_ctor_get(x_41, 9);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 lean_ctor_release(x_41, 7);
 lean_ctor_release(x_41, 8);
 lean_ctor_release(x_41, 9);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Elab_replaceRef(x_1, x_55);
lean_dec(x_55);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 10, 3);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_44);
lean_ctor_set(x_58, 2, x_45);
lean_ctor_set(x_58, 3, x_46);
lean_ctor_set(x_58, 4, x_47);
lean_ctor_set(x_58, 5, x_48);
lean_ctor_set(x_58, 6, x_49);
lean_ctor_set(x_58, 7, x_50);
lean_ctor_set(x_58, 8, x_51);
lean_ctor_set(x_58, 9, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 2, x_54);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_42);
lean_inc(x_5);
x_60 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_60, 0, x_5);
x_61 = lean_unsigned_to_nat(1u);
x_62 = l_Lean_Syntax_getArg(x_5, x_61);
lean_dec(x_5);
x_63 = l_Lean_Syntax_getArgs(x_62);
lean_dec(x_62);
x_64 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_65 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 5, 3);
lean_closure_set(x_65, 0, x_64);
lean_closure_set(x_65, 1, x_60);
lean_closure_set(x_65, 2, x_63);
x_66 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_65, x_59, x_3);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec(x_2);
x_67 = l_Array_empty___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
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
lean_object* x_1; 
x_1 = lean_mk_string("major premise depends on variable being generalized");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
x_15 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_16 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = l_Lean_Expr_fvarId_x21(x_1);
x_26 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_23, x_25);
lean_dec(x_25);
x_27 = lean_array_get_size(x_23);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
if (x_26 == 0)
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
x_32 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_33 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
x_15 = l_Lean_mkThunk___closed__1;
x_16 = lean_name_eq(x_13, x_15);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 9);
x_21 = l_Lean_Elab_replaceRef(x_10, x_20);
lean_dec(x_20);
lean_ctor_set(x_17, 9, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
x_23 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_14);
x_25 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_24, x_22, x_5);
if (x_16 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = 0;
x_27 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_13, x_26, x_1);
if (x_27 == 0)
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Syntax_getArg(x_10, x_29);
lean_dec(x_10);
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_13);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_30, x_38, x_4, x_28);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_3 = x_12;
x_5 = x_40;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_dec(x_25);
x_3 = x_12;
x_5 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_25);
if (x_52 == 0)
{
return x_25;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_25, 0);
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_25);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_25, 1);
lean_inc(x_56);
lean_dec(x_25);
x_3 = x_12;
x_5 = x_56;
goto _start;
}
else
{
uint8_t x_58; 
lean_dec(x_12);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_25);
if (x_58 == 0)
{
return x_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
x_64 = lean_ctor_get(x_17, 2);
x_65 = lean_ctor_get(x_17, 3);
x_66 = lean_ctor_get(x_17, 4);
x_67 = lean_ctor_get(x_17, 5);
x_68 = lean_ctor_get(x_17, 6);
x_69 = lean_ctor_get(x_17, 7);
x_70 = lean_ctor_get(x_17, 8);
x_71 = lean_ctor_get_uint8(x_17, sizeof(void*)*10);
x_72 = lean_ctor_get_uint8(x_17, sizeof(void*)*10 + 1);
x_73 = lean_ctor_get_uint8(x_17, sizeof(void*)*10 + 2);
x_74 = lean_ctor_get(x_17, 9);
lean_inc(x_74);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
x_75 = l_Lean_Elab_replaceRef(x_10, x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_76, 0, x_62);
lean_ctor_set(x_76, 1, x_63);
lean_ctor_set(x_76, 2, x_64);
lean_ctor_set(x_76, 3, x_65);
lean_ctor_set(x_76, 4, x_66);
lean_ctor_set(x_76, 5, x_67);
lean_ctor_set(x_76, 6, x_68);
lean_ctor_set(x_76, 7, x_69);
lean_ctor_set(x_76, 8, x_70);
lean_ctor_set(x_76, 9, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*10, x_71);
lean_ctor_set_uint8(x_76, sizeof(void*)*10 + 1, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*10 + 2, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_18);
x_78 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_79, 0, x_78);
lean_closure_set(x_79, 1, x_14);
x_80 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_79, x_77, x_5);
if (x_16 == 0)
{
uint8_t x_81; uint8_t x_82; 
x_81 = 0;
x_82 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_13, x_81, x_1);
if (x_82 == 0)
{
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Syntax_getArg(x_10, x_84);
lean_dec(x_10);
x_86 = l_Lean_Name_toString___closed__1;
x_87 = l_Lean_Name_toStringWithSep___main(x_86, x_13);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_91 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_93 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_4);
x_94 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_85, x_93, x_4, x_83);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_3 = x_12;
x_5 = x_95;
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_12);
lean_dec(x_4);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_99 = x_94;
} else {
 lean_dec_ref(x_94);
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
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_103 = x_80;
} else {
 lean_dec_ref(x_80);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_80, 1);
lean_inc(x_105);
lean_dec(x_80);
x_3 = x_12;
x_5 = x_105;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_12);
lean_dec(x_4);
x_107 = lean_ctor_get(x_80, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_80, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_109 = x_80;
} else {
 lean_dec_ref(x_80);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_80, 1);
lean_inc(x_111);
lean_dec(x_80);
x_3 = x_12;
x_5 = x_111;
goto _start;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_12);
lean_dec(x_4);
x_113 = lean_ctor_get(x_80, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_80, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_115 = x_80;
} else {
 lean_dec_ref(x_80);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
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
x_14 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
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
x_34 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 8);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_17, sizeof(void*)*10);
x_31 = lean_ctor_get_uint8(x_17, sizeof(void*)*10 + 1);
x_32 = lean_ctor_get_uint8(x_17, sizeof(void*)*10 + 2);
x_33 = lean_ctor_get(x_17, 9);
lean_inc(x_33);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 lean_ctor_release(x_17, 9);
 x_34 = x_17;
} else {
 lean_dec_ref(x_17);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_18, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_18, 4);
lean_inc(x_36);
x_37 = lean_nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_dec(x_3);
x_38 = x_19;
goto block_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_58 = l_Lean_Elab_Tactic_throwError___rarg(x_57, x_3, x_19);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_38 = x_59;
goto block_56;
}
else
{
uint8_t x_60; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_58);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_56:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_18, 4);
lean_dec(x_40);
x_41 = lean_ctor_get(x_18, 3);
lean_dec(x_41);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_35, x_42);
lean_dec(x_35);
lean_ctor_set(x_18, 3, x_43);
if (lean_is_scalar(x_34)) {
 x_44 = lean_alloc_ctor(0, 10, 3);
} else {
 x_44 = x_34;
}
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_22);
lean_ctor_set(x_44, 2, x_23);
lean_ctor_set(x_44, 3, x_24);
lean_ctor_set(x_44, 4, x_25);
lean_ctor_set(x_44, 5, x_26);
lean_ctor_set(x_44, 6, x_27);
lean_ctor_set(x_44, 7, x_28);
lean_ctor_set(x_44, 8, x_29);
lean_ctor_set(x_44, 9, x_33);
lean_ctor_set_uint8(x_44, sizeof(void*)*10, x_30);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 1, x_31);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 2, x_32);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_21);
x_2 = x_20;
x_3 = x_45;
x_4 = x_38;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
x_49 = lean_ctor_get(x_18, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_35, x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_36);
if (lean_is_scalar(x_34)) {
 x_53 = lean_alloc_ctor(0, 10, 3);
} else {
 x_53 = x_34;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_22);
lean_ctor_set(x_53, 2, x_23);
lean_ctor_set(x_53, 3, x_24);
lean_ctor_set(x_53, 4, x_25);
lean_ctor_set(x_53, 5, x_26);
lean_ctor_set(x_53, 6, x_27);
lean_ctor_set(x_53, 7, x_28);
lean_ctor_set(x_53, 8, x_29);
lean_ctor_set(x_53, 9, x_33);
lean_ctor_set_uint8(x_53, sizeof(void*)*10, x_30);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 1, x_31);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 2, x_32);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_21);
x_2 = x_20;
x_3 = x_54;
x_4 = x_38;
goto _start;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_9);
if (x_64 == 0)
{
return x_9;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_9, 0);
x_66 = lean_ctor_get(x_9, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_9);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 1:
{
lean_object* x_68; 
lean_dec(x_8);
lean_inc(x_3);
x_68 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_76 = lean_ctor_get(x_3, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_ctor_get(x_3, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_76, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_76, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_76, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 8);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_76, sizeof(void*)*10);
x_90 = lean_ctor_get_uint8(x_76, sizeof(void*)*10 + 1);
x_91 = lean_ctor_get_uint8(x_76, sizeof(void*)*10 + 2);
x_92 = lean_ctor_get(x_76, 9);
lean_inc(x_92);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 lean_ctor_release(x_76, 5);
 lean_ctor_release(x_76, 6);
 lean_ctor_release(x_76, 7);
 lean_ctor_release(x_76, 8);
 lean_ctor_release(x_76, 9);
 x_93 = x_76;
} else {
 lean_dec_ref(x_76);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_77, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_77, 4);
lean_inc(x_95);
x_96 = lean_nat_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_dec(x_3);
x_97 = x_78;
goto block_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_117 = l_Lean_Elab_Tactic_throwError___rarg(x_116, x_3, x_78);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_97 = x_118;
goto block_115;
}
else
{
uint8_t x_119; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_117);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
block_115:
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_77);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_77, 4);
lean_dec(x_99);
x_100 = lean_ctor_get(x_77, 3);
lean_dec(x_100);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_94, x_101);
lean_dec(x_94);
lean_ctor_set(x_77, 3, x_102);
if (lean_is_scalar(x_93)) {
 x_103 = lean_alloc_ctor(0, 10, 3);
} else {
 x_103 = x_93;
}
lean_ctor_set(x_103, 0, x_77);
lean_ctor_set(x_103, 1, x_81);
lean_ctor_set(x_103, 2, x_82);
lean_ctor_set(x_103, 3, x_83);
lean_ctor_set(x_103, 4, x_84);
lean_ctor_set(x_103, 5, x_85);
lean_ctor_set(x_103, 6, x_86);
lean_ctor_set(x_103, 7, x_87);
lean_ctor_set(x_103, 8, x_88);
lean_ctor_set(x_103, 9, x_92);
lean_ctor_set_uint8(x_103, sizeof(void*)*10, x_89);
lean_ctor_set_uint8(x_103, sizeof(void*)*10 + 1, x_90);
lean_ctor_set_uint8(x_103, sizeof(void*)*10 + 2, x_91);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_80);
x_2 = x_79;
x_3 = x_104;
x_4 = x_97;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_77, 0);
x_107 = lean_ctor_get(x_77, 1);
x_108 = lean_ctor_get(x_77, 2);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_77);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_add(x_94, x_109);
lean_dec(x_94);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_110);
lean_ctor_set(x_111, 4, x_95);
if (lean_is_scalar(x_93)) {
 x_112 = lean_alloc_ctor(0, 10, 3);
} else {
 x_112 = x_93;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_81);
lean_ctor_set(x_112, 2, x_82);
lean_ctor_set(x_112, 3, x_83);
lean_ctor_set(x_112, 4, x_84);
lean_ctor_set(x_112, 5, x_85);
lean_ctor_set(x_112, 6, x_86);
lean_ctor_set(x_112, 7, x_87);
lean_ctor_set(x_112, 8, x_88);
lean_ctor_set(x_112, 9, x_92);
lean_ctor_set_uint8(x_112, sizeof(void*)*10, x_89);
lean_ctor_set_uint8(x_112, sizeof(void*)*10 + 1, x_90);
lean_ctor_set_uint8(x_112, sizeof(void*)*10 + 2, x_91);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_80);
x_2 = x_79;
x_3 = x_113;
x_4 = x_97;
goto _start;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_3);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_68);
if (x_123 == 0)
{
return x_68;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_68, 0);
x_125 = lean_ctor_get(x_68, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_68);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
case 2:
{
lean_object* x_127; 
lean_dec(x_8);
lean_inc(x_3);
x_127 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 0);
lean_dec(x_130);
x_131 = lean_box(0);
lean_ctor_set(x_127, 0, x_131);
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_135 = lean_ctor_get(x_3, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
lean_dec(x_127);
x_138 = lean_ctor_get(x_128, 0);
lean_inc(x_138);
lean_dec(x_128);
x_139 = lean_ctor_get(x_3, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 5);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 6);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 7);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 8);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_135, sizeof(void*)*10);
x_149 = lean_ctor_get_uint8(x_135, sizeof(void*)*10 + 1);
x_150 = lean_ctor_get_uint8(x_135, sizeof(void*)*10 + 2);
x_151 = lean_ctor_get(x_135, 9);
lean_inc(x_151);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 lean_ctor_release(x_135, 6);
 lean_ctor_release(x_135, 7);
 lean_ctor_release(x_135, 8);
 lean_ctor_release(x_135, 9);
 x_152 = x_135;
} else {
 lean_dec_ref(x_135);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_136, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_136, 4);
lean_inc(x_154);
x_155 = lean_nat_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_dec(x_3);
x_156 = x_137;
goto block_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_176 = l_Lean_Elab_Tactic_throwError___rarg(x_175, x_3, x_137);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_156 = x_177;
goto block_174;
}
else
{
uint8_t x_178; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_176);
if (x_178 == 0)
{
return x_176;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_176, 0);
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_176);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
block_174:
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_136);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_136, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_136, 3);
lean_dec(x_159);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_add(x_153, x_160);
lean_dec(x_153);
lean_ctor_set(x_136, 3, x_161);
if (lean_is_scalar(x_152)) {
 x_162 = lean_alloc_ctor(0, 10, 3);
} else {
 x_162 = x_152;
}
lean_ctor_set(x_162, 0, x_136);
lean_ctor_set(x_162, 1, x_140);
lean_ctor_set(x_162, 2, x_141);
lean_ctor_set(x_162, 3, x_142);
lean_ctor_set(x_162, 4, x_143);
lean_ctor_set(x_162, 5, x_144);
lean_ctor_set(x_162, 6, x_145);
lean_ctor_set(x_162, 7, x_146);
lean_ctor_set(x_162, 8, x_147);
lean_ctor_set(x_162, 9, x_151);
lean_ctor_set_uint8(x_162, sizeof(void*)*10, x_148);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 1, x_149);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 2, x_150);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_139);
x_2 = x_138;
x_3 = x_163;
x_4 = x_156;
goto _start;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_136, 0);
x_166 = lean_ctor_get(x_136, 1);
x_167 = lean_ctor_get(x_136, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_136);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_nat_add(x_153, x_168);
lean_dec(x_153);
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_166);
lean_ctor_set(x_170, 2, x_167);
lean_ctor_set(x_170, 3, x_169);
lean_ctor_set(x_170, 4, x_154);
if (lean_is_scalar(x_152)) {
 x_171 = lean_alloc_ctor(0, 10, 3);
} else {
 x_171 = x_152;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_140);
lean_ctor_set(x_171, 2, x_141);
lean_ctor_set(x_171, 3, x_142);
lean_ctor_set(x_171, 4, x_143);
lean_ctor_set(x_171, 5, x_144);
lean_ctor_set(x_171, 6, x_145);
lean_ctor_set(x_171, 7, x_146);
lean_ctor_set(x_171, 8, x_147);
lean_ctor_set(x_171, 9, x_151);
lean_ctor_set_uint8(x_171, sizeof(void*)*10, x_148);
lean_ctor_set_uint8(x_171, sizeof(void*)*10 + 1, x_149);
lean_ctor_set_uint8(x_171, sizeof(void*)*10 + 2, x_150);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_139);
x_2 = x_138;
x_3 = x_172;
x_4 = x_156;
goto _start;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_3);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_127);
if (x_182 == 0)
{
return x_127;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_127, 0);
x_184 = lean_ctor_get(x_127, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_127);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
case 3:
{
lean_object* x_186; 
lean_dec(x_8);
lean_inc(x_3);
x_186 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
lean_dec(x_3);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_186);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_186, 0);
lean_dec(x_189);
x_190 = lean_box(0);
lean_ctor_set(x_186, 0, x_190);
return x_186;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_dec(x_186);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_194 = lean_ctor_get(x_3, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_186, 1);
lean_inc(x_196);
lean_dec(x_186);
x_197 = lean_ctor_get(x_187, 0);
lean_inc(x_197);
lean_dec(x_187);
x_198 = lean_ctor_get(x_3, 1);
lean_inc(x_198);
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
x_204 = lean_ctor_get(x_194, 6);
lean_inc(x_204);
x_205 = lean_ctor_get(x_194, 7);
lean_inc(x_205);
x_206 = lean_ctor_get(x_194, 8);
lean_inc(x_206);
x_207 = lean_ctor_get_uint8(x_194, sizeof(void*)*10);
x_208 = lean_ctor_get_uint8(x_194, sizeof(void*)*10 + 1);
x_209 = lean_ctor_get_uint8(x_194, sizeof(void*)*10 + 2);
x_210 = lean_ctor_get(x_194, 9);
lean_inc(x_210);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 lean_ctor_release(x_194, 4);
 lean_ctor_release(x_194, 5);
 lean_ctor_release(x_194, 6);
 lean_ctor_release(x_194, 7);
 lean_ctor_release(x_194, 8);
 lean_ctor_release(x_194, 9);
 x_211 = x_194;
} else {
 lean_dec_ref(x_194);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_195, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_195, 4);
lean_inc(x_213);
x_214 = lean_nat_dec_eq(x_212, x_213);
if (x_214 == 0)
{
lean_dec(x_3);
x_215 = x_196;
goto block_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_235 = l_Lean_Elab_Tactic_throwError___rarg(x_234, x_3, x_196);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_215 = x_236;
goto block_233;
}
else
{
uint8_t x_237; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_235);
if (x_237 == 0)
{
return x_235;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_235, 0);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_235);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
block_233:
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_195);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_195, 4);
lean_dec(x_217);
x_218 = lean_ctor_get(x_195, 3);
lean_dec(x_218);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_nat_add(x_212, x_219);
lean_dec(x_212);
lean_ctor_set(x_195, 3, x_220);
if (lean_is_scalar(x_211)) {
 x_221 = lean_alloc_ctor(0, 10, 3);
} else {
 x_221 = x_211;
}
lean_ctor_set(x_221, 0, x_195);
lean_ctor_set(x_221, 1, x_199);
lean_ctor_set(x_221, 2, x_200);
lean_ctor_set(x_221, 3, x_201);
lean_ctor_set(x_221, 4, x_202);
lean_ctor_set(x_221, 5, x_203);
lean_ctor_set(x_221, 6, x_204);
lean_ctor_set(x_221, 7, x_205);
lean_ctor_set(x_221, 8, x_206);
lean_ctor_set(x_221, 9, x_210);
lean_ctor_set_uint8(x_221, sizeof(void*)*10, x_207);
lean_ctor_set_uint8(x_221, sizeof(void*)*10 + 1, x_208);
lean_ctor_set_uint8(x_221, sizeof(void*)*10 + 2, x_209);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_198);
x_2 = x_197;
x_3 = x_222;
x_4 = x_215;
goto _start;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_224 = lean_ctor_get(x_195, 0);
x_225 = lean_ctor_get(x_195, 1);
x_226 = lean_ctor_get(x_195, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_195);
x_227 = lean_unsigned_to_nat(1u);
x_228 = lean_nat_add(x_212, x_227);
lean_dec(x_212);
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_224);
lean_ctor_set(x_229, 1, x_225);
lean_ctor_set(x_229, 2, x_226);
lean_ctor_set(x_229, 3, x_228);
lean_ctor_set(x_229, 4, x_213);
if (lean_is_scalar(x_211)) {
 x_230 = lean_alloc_ctor(0, 10, 3);
} else {
 x_230 = x_211;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_199);
lean_ctor_set(x_230, 2, x_200);
lean_ctor_set(x_230, 3, x_201);
lean_ctor_set(x_230, 4, x_202);
lean_ctor_set(x_230, 5, x_203);
lean_ctor_set(x_230, 6, x_204);
lean_ctor_set(x_230, 7, x_205);
lean_ctor_set(x_230, 8, x_206);
lean_ctor_set(x_230, 9, x_210);
lean_ctor_set_uint8(x_230, sizeof(void*)*10, x_207);
lean_ctor_set_uint8(x_230, sizeof(void*)*10 + 1, x_208);
lean_ctor_set_uint8(x_230, sizeof(void*)*10 + 2, x_209);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_198);
x_2 = x_197;
x_3 = x_231;
x_4 = x_215;
goto _start;
}
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_3);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_186);
if (x_241 == 0)
{
return x_186;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_186, 0);
x_243 = lean_ctor_get(x_186, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_186);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
case 4:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_8, 0);
lean_inc(x_245);
lean_dec(x_8);
lean_inc(x_1);
x_246 = l_Lean_Name_append___main(x_245, x_1);
lean_dec(x_245);
x_247 = l_Lean_Elab_Tactic_getEnv___rarg(x_7);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
lean_inc(x_246);
x_250 = lean_environment_find(x_248, x_246);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
lean_dec(x_246);
lean_inc(x_3);
x_251 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
uint8_t x_253; 
lean_dec(x_3);
lean_dec(x_1);
x_253 = !lean_is_exclusive(x_251);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_251, 0);
lean_dec(x_254);
x_255 = lean_box(0);
lean_ctor_set(x_251, 0, x_255);
return x_251;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_251, 1);
lean_inc(x_256);
lean_dec(x_251);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; 
x_259 = lean_ctor_get(x_3, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_251, 1);
lean_inc(x_261);
lean_dec(x_251);
x_262 = lean_ctor_get(x_252, 0);
lean_inc(x_262);
lean_dec(x_252);
x_263 = lean_ctor_get(x_3, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_259, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_259, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_259, 4);
lean_inc(x_267);
x_268 = lean_ctor_get(x_259, 5);
lean_inc(x_268);
x_269 = lean_ctor_get(x_259, 6);
lean_inc(x_269);
x_270 = lean_ctor_get(x_259, 7);
lean_inc(x_270);
x_271 = lean_ctor_get(x_259, 8);
lean_inc(x_271);
x_272 = lean_ctor_get_uint8(x_259, sizeof(void*)*10);
x_273 = lean_ctor_get_uint8(x_259, sizeof(void*)*10 + 1);
x_274 = lean_ctor_get_uint8(x_259, sizeof(void*)*10 + 2);
x_275 = lean_ctor_get(x_259, 9);
lean_inc(x_275);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 lean_ctor_release(x_259, 5);
 lean_ctor_release(x_259, 6);
 lean_ctor_release(x_259, 7);
 lean_ctor_release(x_259, 8);
 lean_ctor_release(x_259, 9);
 x_276 = x_259;
} else {
 lean_dec_ref(x_259);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_260, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_260, 4);
lean_inc(x_278);
x_279 = lean_nat_dec_eq(x_277, x_278);
if (x_279 == 0)
{
lean_dec(x_3);
x_280 = x_261;
goto block_298;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_300 = l_Lean_Elab_Tactic_throwError___rarg(x_299, x_3, x_261);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec(x_300);
x_280 = x_301;
goto block_298;
}
else
{
uint8_t x_302; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_300);
if (x_302 == 0)
{
return x_300;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_300, 0);
x_304 = lean_ctor_get(x_300, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_300);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
block_298:
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_260);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_260, 4);
lean_dec(x_282);
x_283 = lean_ctor_get(x_260, 3);
lean_dec(x_283);
x_284 = lean_unsigned_to_nat(1u);
x_285 = lean_nat_add(x_277, x_284);
lean_dec(x_277);
lean_ctor_set(x_260, 3, x_285);
if (lean_is_scalar(x_276)) {
 x_286 = lean_alloc_ctor(0, 10, 3);
} else {
 x_286 = x_276;
}
lean_ctor_set(x_286, 0, x_260);
lean_ctor_set(x_286, 1, x_264);
lean_ctor_set(x_286, 2, x_265);
lean_ctor_set(x_286, 3, x_266);
lean_ctor_set(x_286, 4, x_267);
lean_ctor_set(x_286, 5, x_268);
lean_ctor_set(x_286, 6, x_269);
lean_ctor_set(x_286, 7, x_270);
lean_ctor_set(x_286, 8, x_271);
lean_ctor_set(x_286, 9, x_275);
lean_ctor_set_uint8(x_286, sizeof(void*)*10, x_272);
lean_ctor_set_uint8(x_286, sizeof(void*)*10 + 1, x_273);
lean_ctor_set_uint8(x_286, sizeof(void*)*10 + 2, x_274);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_263);
x_2 = x_262;
x_3 = x_287;
x_4 = x_280;
goto _start;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_289 = lean_ctor_get(x_260, 0);
x_290 = lean_ctor_get(x_260, 1);
x_291 = lean_ctor_get(x_260, 2);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_260);
x_292 = lean_unsigned_to_nat(1u);
x_293 = lean_nat_add(x_277, x_292);
lean_dec(x_277);
x_294 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_290);
lean_ctor_set(x_294, 2, x_291);
lean_ctor_set(x_294, 3, x_293);
lean_ctor_set(x_294, 4, x_278);
if (lean_is_scalar(x_276)) {
 x_295 = lean_alloc_ctor(0, 10, 3);
} else {
 x_295 = x_276;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_264);
lean_ctor_set(x_295, 2, x_265);
lean_ctor_set(x_295, 3, x_266);
lean_ctor_set(x_295, 4, x_267);
lean_ctor_set(x_295, 5, x_268);
lean_ctor_set(x_295, 6, x_269);
lean_ctor_set(x_295, 7, x_270);
lean_ctor_set(x_295, 8, x_271);
lean_ctor_set(x_295, 9, x_275);
lean_ctor_set_uint8(x_295, sizeof(void*)*10, x_272);
lean_ctor_set_uint8(x_295, sizeof(void*)*10 + 1, x_273);
lean_ctor_set_uint8(x_295, sizeof(void*)*10 + 2, x_274);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_263);
x_2 = x_262;
x_3 = x_296;
x_4 = x_280;
goto _start;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_3);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_251);
if (x_306 == 0)
{
return x_251;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_251, 0);
x_308 = lean_ctor_get(x_251, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_251);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_373; 
lean_dec(x_250);
x_310 = l_Lean_Elab_Tactic_save(x_249);
lean_inc(x_3);
x_373 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_249);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_box(0);
x_378 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_378, 0, x_246);
lean_closure_set(x_378, 1, x_377);
x_379 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_380 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_380, 0, x_378);
lean_closure_set(x_380, 1, x_379);
x_381 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_381, 0, x_380);
lean_inc(x_3);
x_382 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_376, x_381, x_3, x_375);
lean_dec(x_376);
if (lean_obj_tag(x_382) == 0)
{
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_382;
}
else
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_311 = x_383;
goto block_372;
}
}
else
{
lean_object* x_384; 
lean_dec(x_246);
x_384 = lean_ctor_get(x_373, 1);
lean_inc(x_384);
lean_dec(x_373);
x_311 = x_384;
goto block_372;
}
block_372:
{
lean_object* x_312; lean_object* x_313; 
x_312 = l_Lean_Elab_Tactic_restore(x_311, x_310);
lean_dec(x_310);
lean_inc(x_3);
x_313 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
if (lean_obj_tag(x_314) == 0)
{
uint8_t x_315; 
lean_dec(x_3);
lean_dec(x_1);
x_315 = !lean_is_exclusive(x_313);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_313, 0);
lean_dec(x_316);
x_317 = lean_box(0);
lean_ctor_set(x_313, 0, x_317);
return x_313;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_313, 1);
lean_inc(x_318);
lean_dec(x_313);
x_319 = lean_box(0);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; 
x_321 = lean_ctor_get(x_3, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_313, 1);
lean_inc(x_323);
lean_dec(x_313);
x_324 = lean_ctor_get(x_314, 0);
lean_inc(x_324);
lean_dec(x_314);
x_325 = lean_ctor_get(x_3, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_321, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_321, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_321, 3);
lean_inc(x_328);
x_329 = lean_ctor_get(x_321, 4);
lean_inc(x_329);
x_330 = lean_ctor_get(x_321, 5);
lean_inc(x_330);
x_331 = lean_ctor_get(x_321, 6);
lean_inc(x_331);
x_332 = lean_ctor_get(x_321, 7);
lean_inc(x_332);
x_333 = lean_ctor_get(x_321, 8);
lean_inc(x_333);
x_334 = lean_ctor_get_uint8(x_321, sizeof(void*)*10);
x_335 = lean_ctor_get_uint8(x_321, sizeof(void*)*10 + 1);
x_336 = lean_ctor_get_uint8(x_321, sizeof(void*)*10 + 2);
x_337 = lean_ctor_get(x_321, 9);
lean_inc(x_337);
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
 x_338 = x_321;
} else {
 lean_dec_ref(x_321);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_322, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_322, 4);
lean_inc(x_340);
x_341 = lean_nat_dec_eq(x_339, x_340);
if (x_341 == 0)
{
lean_dec(x_3);
x_342 = x_323;
goto block_360;
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_362 = l_Lean_Elab_Tactic_throwError___rarg(x_361, x_3, x_323);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
x_342 = x_363;
goto block_360;
}
else
{
uint8_t x_364; 
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_1);
x_364 = !lean_is_exclusive(x_362);
if (x_364 == 0)
{
return x_362;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_362, 0);
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_362);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
block_360:
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_322);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_344 = lean_ctor_get(x_322, 4);
lean_dec(x_344);
x_345 = lean_ctor_get(x_322, 3);
lean_dec(x_345);
x_346 = lean_unsigned_to_nat(1u);
x_347 = lean_nat_add(x_339, x_346);
lean_dec(x_339);
lean_ctor_set(x_322, 3, x_347);
if (lean_is_scalar(x_338)) {
 x_348 = lean_alloc_ctor(0, 10, 3);
} else {
 x_348 = x_338;
}
lean_ctor_set(x_348, 0, x_322);
lean_ctor_set(x_348, 1, x_326);
lean_ctor_set(x_348, 2, x_327);
lean_ctor_set(x_348, 3, x_328);
lean_ctor_set(x_348, 4, x_329);
lean_ctor_set(x_348, 5, x_330);
lean_ctor_set(x_348, 6, x_331);
lean_ctor_set(x_348, 7, x_332);
lean_ctor_set(x_348, 8, x_333);
lean_ctor_set(x_348, 9, x_337);
lean_ctor_set_uint8(x_348, sizeof(void*)*10, x_334);
lean_ctor_set_uint8(x_348, sizeof(void*)*10 + 1, x_335);
lean_ctor_set_uint8(x_348, sizeof(void*)*10 + 2, x_336);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_325);
x_2 = x_324;
x_3 = x_349;
x_4 = x_342;
goto _start;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_351 = lean_ctor_get(x_322, 0);
x_352 = lean_ctor_get(x_322, 1);
x_353 = lean_ctor_get(x_322, 2);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_322);
x_354 = lean_unsigned_to_nat(1u);
x_355 = lean_nat_add(x_339, x_354);
lean_dec(x_339);
x_356 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_355);
lean_ctor_set(x_356, 4, x_340);
if (lean_is_scalar(x_338)) {
 x_357 = lean_alloc_ctor(0, 10, 3);
} else {
 x_357 = x_338;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_326);
lean_ctor_set(x_357, 2, x_327);
lean_ctor_set(x_357, 3, x_328);
lean_ctor_set(x_357, 4, x_329);
lean_ctor_set(x_357, 5, x_330);
lean_ctor_set(x_357, 6, x_331);
lean_ctor_set(x_357, 7, x_332);
lean_ctor_set(x_357, 8, x_333);
lean_ctor_set(x_357, 9, x_337);
lean_ctor_set_uint8(x_357, sizeof(void*)*10, x_334);
lean_ctor_set_uint8(x_357, sizeof(void*)*10 + 1, x_335);
lean_ctor_set_uint8(x_357, sizeof(void*)*10 + 2, x_336);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_325);
x_2 = x_324;
x_3 = x_358;
x_4 = x_342;
goto _start;
}
}
}
}
else
{
uint8_t x_368; 
lean_dec(x_3);
lean_dec(x_1);
x_368 = !lean_is_exclusive(x_313);
if (x_368 == 0)
{
return x_313;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_313, 0);
x_370 = lean_ctor_get(x_313, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_313);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
}
}
case 5:
{
lean_object* x_385; 
lean_dec(x_8);
lean_inc(x_3);
x_385 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_obj_tag(x_386) == 0)
{
uint8_t x_387; 
lean_dec(x_3);
lean_dec(x_1);
x_387 = !lean_is_exclusive(x_385);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_ctor_get(x_385, 0);
lean_dec(x_388);
x_389 = lean_box(0);
lean_ctor_set(x_385, 0, x_389);
return x_385;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
lean_dec(x_385);
x_391 = lean_box(0);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; uint8_t x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_393 = lean_ctor_get(x_3, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_385, 1);
lean_inc(x_395);
lean_dec(x_385);
x_396 = lean_ctor_get(x_386, 0);
lean_inc(x_396);
lean_dec(x_386);
x_397 = lean_ctor_get(x_3, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_393, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_393, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_393, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_393, 4);
lean_inc(x_401);
x_402 = lean_ctor_get(x_393, 5);
lean_inc(x_402);
x_403 = lean_ctor_get(x_393, 6);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 7);
lean_inc(x_404);
x_405 = lean_ctor_get(x_393, 8);
lean_inc(x_405);
x_406 = lean_ctor_get_uint8(x_393, sizeof(void*)*10);
x_407 = lean_ctor_get_uint8(x_393, sizeof(void*)*10 + 1);
x_408 = lean_ctor_get_uint8(x_393, sizeof(void*)*10 + 2);
x_409 = lean_ctor_get(x_393, 9);
lean_inc(x_409);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 lean_ctor_release(x_393, 4);
 lean_ctor_release(x_393, 5);
 lean_ctor_release(x_393, 6);
 lean_ctor_release(x_393, 7);
 lean_ctor_release(x_393, 8);
 lean_ctor_release(x_393, 9);
 x_410 = x_393;
} else {
 lean_dec_ref(x_393);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_394, 3);
lean_inc(x_411);
x_412 = lean_ctor_get(x_394, 4);
lean_inc(x_412);
x_413 = lean_nat_dec_eq(x_411, x_412);
if (x_413 == 0)
{
lean_dec(x_3);
x_414 = x_395;
goto block_432;
}
else
{
lean_object* x_433; lean_object* x_434; 
x_433 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_434 = l_Lean_Elab_Tactic_throwError___rarg(x_433, x_3, x_395);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_414 = x_435;
goto block_432;
}
else
{
uint8_t x_436; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_394);
lean_dec(x_1);
x_436 = !lean_is_exclusive(x_434);
if (x_436 == 0)
{
return x_434;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_434, 0);
x_438 = lean_ctor_get(x_434, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_434);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
block_432:
{
uint8_t x_415; 
x_415 = !lean_is_exclusive(x_394);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_416 = lean_ctor_get(x_394, 4);
lean_dec(x_416);
x_417 = lean_ctor_get(x_394, 3);
lean_dec(x_417);
x_418 = lean_unsigned_to_nat(1u);
x_419 = lean_nat_add(x_411, x_418);
lean_dec(x_411);
lean_ctor_set(x_394, 3, x_419);
if (lean_is_scalar(x_410)) {
 x_420 = lean_alloc_ctor(0, 10, 3);
} else {
 x_420 = x_410;
}
lean_ctor_set(x_420, 0, x_394);
lean_ctor_set(x_420, 1, x_398);
lean_ctor_set(x_420, 2, x_399);
lean_ctor_set(x_420, 3, x_400);
lean_ctor_set(x_420, 4, x_401);
lean_ctor_set(x_420, 5, x_402);
lean_ctor_set(x_420, 6, x_403);
lean_ctor_set(x_420, 7, x_404);
lean_ctor_set(x_420, 8, x_405);
lean_ctor_set(x_420, 9, x_409);
lean_ctor_set_uint8(x_420, sizeof(void*)*10, x_406);
lean_ctor_set_uint8(x_420, sizeof(void*)*10 + 1, x_407);
lean_ctor_set_uint8(x_420, sizeof(void*)*10 + 2, x_408);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_397);
x_2 = x_396;
x_3 = x_421;
x_4 = x_414;
goto _start;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_394, 0);
x_424 = lean_ctor_get(x_394, 1);
x_425 = lean_ctor_get(x_394, 2);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_394);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_nat_add(x_411, x_426);
lean_dec(x_411);
x_428 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_428, 0, x_423);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_427);
lean_ctor_set(x_428, 4, x_412);
if (lean_is_scalar(x_410)) {
 x_429 = lean_alloc_ctor(0, 10, 3);
} else {
 x_429 = x_410;
}
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_398);
lean_ctor_set(x_429, 2, x_399);
lean_ctor_set(x_429, 3, x_400);
lean_ctor_set(x_429, 4, x_401);
lean_ctor_set(x_429, 5, x_402);
lean_ctor_set(x_429, 6, x_403);
lean_ctor_set(x_429, 7, x_404);
lean_ctor_set(x_429, 8, x_405);
lean_ctor_set(x_429, 9, x_409);
lean_ctor_set_uint8(x_429, sizeof(void*)*10, x_406);
lean_ctor_set_uint8(x_429, sizeof(void*)*10 + 1, x_407);
lean_ctor_set_uint8(x_429, sizeof(void*)*10 + 2, x_408);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_397);
x_2 = x_396;
x_3 = x_430;
x_4 = x_414;
goto _start;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_3);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_385);
if (x_440 == 0)
{
return x_385;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_385, 0);
x_442 = lean_ctor_get(x_385, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_385);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
case 6:
{
lean_object* x_444; 
lean_dec(x_8);
lean_inc(x_3);
x_444 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_obj_tag(x_445) == 0)
{
uint8_t x_446; 
lean_dec(x_3);
lean_dec(x_1);
x_446 = !lean_is_exclusive(x_444);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_444, 0);
lean_dec(x_447);
x_448 = lean_box(0);
lean_ctor_set(x_444, 0, x_448);
return x_444;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
lean_dec(x_444);
x_450 = lean_box(0);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; uint8_t x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; 
x_452 = lean_ctor_get(x_3, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_444, 1);
lean_inc(x_454);
lean_dec(x_444);
x_455 = lean_ctor_get(x_445, 0);
lean_inc(x_455);
lean_dec(x_445);
x_456 = lean_ctor_get(x_3, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_452, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_452, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_452, 3);
lean_inc(x_459);
x_460 = lean_ctor_get(x_452, 4);
lean_inc(x_460);
x_461 = lean_ctor_get(x_452, 5);
lean_inc(x_461);
x_462 = lean_ctor_get(x_452, 6);
lean_inc(x_462);
x_463 = lean_ctor_get(x_452, 7);
lean_inc(x_463);
x_464 = lean_ctor_get(x_452, 8);
lean_inc(x_464);
x_465 = lean_ctor_get_uint8(x_452, sizeof(void*)*10);
x_466 = lean_ctor_get_uint8(x_452, sizeof(void*)*10 + 1);
x_467 = lean_ctor_get_uint8(x_452, sizeof(void*)*10 + 2);
x_468 = lean_ctor_get(x_452, 9);
lean_inc(x_468);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 lean_ctor_release(x_452, 3);
 lean_ctor_release(x_452, 4);
 lean_ctor_release(x_452, 5);
 lean_ctor_release(x_452, 6);
 lean_ctor_release(x_452, 7);
 lean_ctor_release(x_452, 8);
 lean_ctor_release(x_452, 9);
 x_469 = x_452;
} else {
 lean_dec_ref(x_452);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_453, 3);
lean_inc(x_470);
x_471 = lean_ctor_get(x_453, 4);
lean_inc(x_471);
x_472 = lean_nat_dec_eq(x_470, x_471);
if (x_472 == 0)
{
lean_dec(x_3);
x_473 = x_454;
goto block_491;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_493 = l_Lean_Elab_Tactic_throwError___rarg(x_492, x_3, x_454);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_473 = x_494;
goto block_491;
}
else
{
uint8_t x_495; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_493);
if (x_495 == 0)
{
return x_493;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_493, 0);
x_497 = lean_ctor_get(x_493, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_493);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
block_491:
{
uint8_t x_474; 
x_474 = !lean_is_exclusive(x_453);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_475 = lean_ctor_get(x_453, 4);
lean_dec(x_475);
x_476 = lean_ctor_get(x_453, 3);
lean_dec(x_476);
x_477 = lean_unsigned_to_nat(1u);
x_478 = lean_nat_add(x_470, x_477);
lean_dec(x_470);
lean_ctor_set(x_453, 3, x_478);
if (lean_is_scalar(x_469)) {
 x_479 = lean_alloc_ctor(0, 10, 3);
} else {
 x_479 = x_469;
}
lean_ctor_set(x_479, 0, x_453);
lean_ctor_set(x_479, 1, x_457);
lean_ctor_set(x_479, 2, x_458);
lean_ctor_set(x_479, 3, x_459);
lean_ctor_set(x_479, 4, x_460);
lean_ctor_set(x_479, 5, x_461);
lean_ctor_set(x_479, 6, x_462);
lean_ctor_set(x_479, 7, x_463);
lean_ctor_set(x_479, 8, x_464);
lean_ctor_set(x_479, 9, x_468);
lean_ctor_set_uint8(x_479, sizeof(void*)*10, x_465);
lean_ctor_set_uint8(x_479, sizeof(void*)*10 + 1, x_466);
lean_ctor_set_uint8(x_479, sizeof(void*)*10 + 2, x_467);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_456);
x_2 = x_455;
x_3 = x_480;
x_4 = x_473;
goto _start;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_482 = lean_ctor_get(x_453, 0);
x_483 = lean_ctor_get(x_453, 1);
x_484 = lean_ctor_get(x_453, 2);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_453);
x_485 = lean_unsigned_to_nat(1u);
x_486 = lean_nat_add(x_470, x_485);
lean_dec(x_470);
x_487 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_487, 0, x_482);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_486);
lean_ctor_set(x_487, 4, x_471);
if (lean_is_scalar(x_469)) {
 x_488 = lean_alloc_ctor(0, 10, 3);
} else {
 x_488 = x_469;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_457);
lean_ctor_set(x_488, 2, x_458);
lean_ctor_set(x_488, 3, x_459);
lean_ctor_set(x_488, 4, x_460);
lean_ctor_set(x_488, 5, x_461);
lean_ctor_set(x_488, 6, x_462);
lean_ctor_set(x_488, 7, x_463);
lean_ctor_set(x_488, 8, x_464);
lean_ctor_set(x_488, 9, x_468);
lean_ctor_set_uint8(x_488, sizeof(void*)*10, x_465);
lean_ctor_set_uint8(x_488, sizeof(void*)*10 + 1, x_466);
lean_ctor_set_uint8(x_488, sizeof(void*)*10 + 2, x_467);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_456);
x_2 = x_455;
x_3 = x_489;
x_4 = x_473;
goto _start;
}
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_3);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_444);
if (x_499 == 0)
{
return x_444;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_444, 0);
x_501 = lean_ctor_get(x_444, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_444);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
case 7:
{
lean_object* x_503; 
lean_dec(x_8);
lean_inc(x_3);
x_503 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
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
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; uint8_t x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; 
x_511 = lean_ctor_get(x_3, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_503, 1);
lean_inc(x_513);
lean_dec(x_503);
x_514 = lean_ctor_get(x_504, 0);
lean_inc(x_514);
lean_dec(x_504);
x_515 = lean_ctor_get(x_3, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_511, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_511, 2);
lean_inc(x_517);
x_518 = lean_ctor_get(x_511, 3);
lean_inc(x_518);
x_519 = lean_ctor_get(x_511, 4);
lean_inc(x_519);
x_520 = lean_ctor_get(x_511, 5);
lean_inc(x_520);
x_521 = lean_ctor_get(x_511, 6);
lean_inc(x_521);
x_522 = lean_ctor_get(x_511, 7);
lean_inc(x_522);
x_523 = lean_ctor_get(x_511, 8);
lean_inc(x_523);
x_524 = lean_ctor_get_uint8(x_511, sizeof(void*)*10);
x_525 = lean_ctor_get_uint8(x_511, sizeof(void*)*10 + 1);
x_526 = lean_ctor_get_uint8(x_511, sizeof(void*)*10 + 2);
x_527 = lean_ctor_get(x_511, 9);
lean_inc(x_527);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 lean_ctor_release(x_511, 2);
 lean_ctor_release(x_511, 3);
 lean_ctor_release(x_511, 4);
 lean_ctor_release(x_511, 5);
 lean_ctor_release(x_511, 6);
 lean_ctor_release(x_511, 7);
 lean_ctor_release(x_511, 8);
 lean_ctor_release(x_511, 9);
 x_528 = x_511;
} else {
 lean_dec_ref(x_511);
 x_528 = lean_box(0);
}
x_529 = lean_ctor_get(x_512, 3);
lean_inc(x_529);
x_530 = lean_ctor_get(x_512, 4);
lean_inc(x_530);
x_531 = lean_nat_dec_eq(x_529, x_530);
if (x_531 == 0)
{
lean_dec(x_3);
x_532 = x_513;
goto block_550;
}
else
{
lean_object* x_551; lean_object* x_552; 
x_551 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_552 = l_Lean_Elab_Tactic_throwError___rarg(x_551, x_3, x_513);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; 
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
x_532 = x_553;
goto block_550;
}
else
{
uint8_t x_554; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_512);
lean_dec(x_1);
x_554 = !lean_is_exclusive(x_552);
if (x_554 == 0)
{
return x_552;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_552, 0);
x_556 = lean_ctor_get(x_552, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_552);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
block_550:
{
uint8_t x_533; 
x_533 = !lean_is_exclusive(x_512);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_534 = lean_ctor_get(x_512, 4);
lean_dec(x_534);
x_535 = lean_ctor_get(x_512, 3);
lean_dec(x_535);
x_536 = lean_unsigned_to_nat(1u);
x_537 = lean_nat_add(x_529, x_536);
lean_dec(x_529);
lean_ctor_set(x_512, 3, x_537);
if (lean_is_scalar(x_528)) {
 x_538 = lean_alloc_ctor(0, 10, 3);
} else {
 x_538 = x_528;
}
lean_ctor_set(x_538, 0, x_512);
lean_ctor_set(x_538, 1, x_516);
lean_ctor_set(x_538, 2, x_517);
lean_ctor_set(x_538, 3, x_518);
lean_ctor_set(x_538, 4, x_519);
lean_ctor_set(x_538, 5, x_520);
lean_ctor_set(x_538, 6, x_521);
lean_ctor_set(x_538, 7, x_522);
lean_ctor_set(x_538, 8, x_523);
lean_ctor_set(x_538, 9, x_527);
lean_ctor_set_uint8(x_538, sizeof(void*)*10, x_524);
lean_ctor_set_uint8(x_538, sizeof(void*)*10 + 1, x_525);
lean_ctor_set_uint8(x_538, sizeof(void*)*10 + 2, x_526);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_515);
x_2 = x_514;
x_3 = x_539;
x_4 = x_532;
goto _start;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_541 = lean_ctor_get(x_512, 0);
x_542 = lean_ctor_get(x_512, 1);
x_543 = lean_ctor_get(x_512, 2);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_512);
x_544 = lean_unsigned_to_nat(1u);
x_545 = lean_nat_add(x_529, x_544);
lean_dec(x_529);
x_546 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_546, 0, x_541);
lean_ctor_set(x_546, 1, x_542);
lean_ctor_set(x_546, 2, x_543);
lean_ctor_set(x_546, 3, x_545);
lean_ctor_set(x_546, 4, x_530);
if (lean_is_scalar(x_528)) {
 x_547 = lean_alloc_ctor(0, 10, 3);
} else {
 x_547 = x_528;
}
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_516);
lean_ctor_set(x_547, 2, x_517);
lean_ctor_set(x_547, 3, x_518);
lean_ctor_set(x_547, 4, x_519);
lean_ctor_set(x_547, 5, x_520);
lean_ctor_set(x_547, 6, x_521);
lean_ctor_set(x_547, 7, x_522);
lean_ctor_set(x_547, 8, x_523);
lean_ctor_set(x_547, 9, x_527);
lean_ctor_set_uint8(x_547, sizeof(void*)*10, x_524);
lean_ctor_set_uint8(x_547, sizeof(void*)*10 + 1, x_525);
lean_ctor_set_uint8(x_547, sizeof(void*)*10 + 2, x_526);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_515);
x_2 = x_514;
x_3 = x_548;
x_4 = x_532;
goto _start;
}
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_3);
lean_dec(x_1);
x_558 = !lean_is_exclusive(x_503);
if (x_558 == 0)
{
return x_503;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_503, 0);
x_560 = lean_ctor_get(x_503, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_503);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
case 8:
{
lean_object* x_562; 
lean_dec(x_8);
lean_inc(x_3);
x_562 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
if (lean_obj_tag(x_563) == 0)
{
uint8_t x_564; 
lean_dec(x_3);
lean_dec(x_1);
x_564 = !lean_is_exclusive(x_562);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_562, 0);
lean_dec(x_565);
x_566 = lean_box(0);
lean_ctor_set(x_562, 0, x_566);
return x_562;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_562, 1);
lean_inc(x_567);
lean_dec(x_562);
x_568 = lean_box(0);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; uint8_t x_584; uint8_t x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; lean_object* x_591; 
x_570 = lean_ctor_get(x_3, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_562, 1);
lean_inc(x_572);
lean_dec(x_562);
x_573 = lean_ctor_get(x_563, 0);
lean_inc(x_573);
lean_dec(x_563);
x_574 = lean_ctor_get(x_3, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_570, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_570, 2);
lean_inc(x_576);
x_577 = lean_ctor_get(x_570, 3);
lean_inc(x_577);
x_578 = lean_ctor_get(x_570, 4);
lean_inc(x_578);
x_579 = lean_ctor_get(x_570, 5);
lean_inc(x_579);
x_580 = lean_ctor_get(x_570, 6);
lean_inc(x_580);
x_581 = lean_ctor_get(x_570, 7);
lean_inc(x_581);
x_582 = lean_ctor_get(x_570, 8);
lean_inc(x_582);
x_583 = lean_ctor_get_uint8(x_570, sizeof(void*)*10);
x_584 = lean_ctor_get_uint8(x_570, sizeof(void*)*10 + 1);
x_585 = lean_ctor_get_uint8(x_570, sizeof(void*)*10 + 2);
x_586 = lean_ctor_get(x_570, 9);
lean_inc(x_586);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 lean_ctor_release(x_570, 2);
 lean_ctor_release(x_570, 3);
 lean_ctor_release(x_570, 4);
 lean_ctor_release(x_570, 5);
 lean_ctor_release(x_570, 6);
 lean_ctor_release(x_570, 7);
 lean_ctor_release(x_570, 8);
 lean_ctor_release(x_570, 9);
 x_587 = x_570;
} else {
 lean_dec_ref(x_570);
 x_587 = lean_box(0);
}
x_588 = lean_ctor_get(x_571, 3);
lean_inc(x_588);
x_589 = lean_ctor_get(x_571, 4);
lean_inc(x_589);
x_590 = lean_nat_dec_eq(x_588, x_589);
if (x_590 == 0)
{
lean_dec(x_3);
x_591 = x_572;
goto block_609;
}
else
{
lean_object* x_610; lean_object* x_611; 
x_610 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_611 = l_Lean_Elab_Tactic_throwError___rarg(x_610, x_3, x_572);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; 
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
lean_dec(x_611);
x_591 = x_612;
goto block_609;
}
else
{
uint8_t x_613; 
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_580);
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_571);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_611);
if (x_613 == 0)
{
return x_611;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_611, 0);
x_615 = lean_ctor_get(x_611, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_611);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
block_609:
{
uint8_t x_592; 
x_592 = !lean_is_exclusive(x_571);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_593 = lean_ctor_get(x_571, 4);
lean_dec(x_593);
x_594 = lean_ctor_get(x_571, 3);
lean_dec(x_594);
x_595 = lean_unsigned_to_nat(1u);
x_596 = lean_nat_add(x_588, x_595);
lean_dec(x_588);
lean_ctor_set(x_571, 3, x_596);
if (lean_is_scalar(x_587)) {
 x_597 = lean_alloc_ctor(0, 10, 3);
} else {
 x_597 = x_587;
}
lean_ctor_set(x_597, 0, x_571);
lean_ctor_set(x_597, 1, x_575);
lean_ctor_set(x_597, 2, x_576);
lean_ctor_set(x_597, 3, x_577);
lean_ctor_set(x_597, 4, x_578);
lean_ctor_set(x_597, 5, x_579);
lean_ctor_set(x_597, 6, x_580);
lean_ctor_set(x_597, 7, x_581);
lean_ctor_set(x_597, 8, x_582);
lean_ctor_set(x_597, 9, x_586);
lean_ctor_set_uint8(x_597, sizeof(void*)*10, x_583);
lean_ctor_set_uint8(x_597, sizeof(void*)*10 + 1, x_584);
lean_ctor_set_uint8(x_597, sizeof(void*)*10 + 2, x_585);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_574);
x_2 = x_573;
x_3 = x_598;
x_4 = x_591;
goto _start;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_600 = lean_ctor_get(x_571, 0);
x_601 = lean_ctor_get(x_571, 1);
x_602 = lean_ctor_get(x_571, 2);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_571);
x_603 = lean_unsigned_to_nat(1u);
x_604 = lean_nat_add(x_588, x_603);
lean_dec(x_588);
x_605 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_605, 0, x_600);
lean_ctor_set(x_605, 1, x_601);
lean_ctor_set(x_605, 2, x_602);
lean_ctor_set(x_605, 3, x_604);
lean_ctor_set(x_605, 4, x_589);
if (lean_is_scalar(x_587)) {
 x_606 = lean_alloc_ctor(0, 10, 3);
} else {
 x_606 = x_587;
}
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_575);
lean_ctor_set(x_606, 2, x_576);
lean_ctor_set(x_606, 3, x_577);
lean_ctor_set(x_606, 4, x_578);
lean_ctor_set(x_606, 5, x_579);
lean_ctor_set(x_606, 6, x_580);
lean_ctor_set(x_606, 7, x_581);
lean_ctor_set(x_606, 8, x_582);
lean_ctor_set(x_606, 9, x_586);
lean_ctor_set_uint8(x_606, sizeof(void*)*10, x_583);
lean_ctor_set_uint8(x_606, sizeof(void*)*10 + 1, x_584);
lean_ctor_set_uint8(x_606, sizeof(void*)*10 + 2, x_585);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_574);
x_2 = x_573;
x_3 = x_607;
x_4 = x_591;
goto _start;
}
}
}
}
else
{
uint8_t x_617; 
lean_dec(x_3);
lean_dec(x_1);
x_617 = !lean_is_exclusive(x_562);
if (x_617 == 0)
{
return x_562;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_562, 0);
x_619 = lean_ctor_get(x_562, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_562);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
case 9:
{
lean_object* x_621; 
lean_dec(x_8);
lean_inc(x_3);
x_621 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
if (lean_obj_tag(x_622) == 0)
{
uint8_t x_623; 
lean_dec(x_3);
lean_dec(x_1);
x_623 = !lean_is_exclusive(x_621);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; 
x_624 = lean_ctor_get(x_621, 0);
lean_dec(x_624);
x_625 = lean_box(0);
lean_ctor_set(x_621, 0, x_625);
return x_621;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_621, 1);
lean_inc(x_626);
lean_dec(x_621);
x_627 = lean_box(0);
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; uint8_t x_643; uint8_t x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; 
x_629 = lean_ctor_get(x_3, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_621, 1);
lean_inc(x_631);
lean_dec(x_621);
x_632 = lean_ctor_get(x_622, 0);
lean_inc(x_632);
lean_dec(x_622);
x_633 = lean_ctor_get(x_3, 1);
lean_inc(x_633);
x_634 = lean_ctor_get(x_629, 1);
lean_inc(x_634);
x_635 = lean_ctor_get(x_629, 2);
lean_inc(x_635);
x_636 = lean_ctor_get(x_629, 3);
lean_inc(x_636);
x_637 = lean_ctor_get(x_629, 4);
lean_inc(x_637);
x_638 = lean_ctor_get(x_629, 5);
lean_inc(x_638);
x_639 = lean_ctor_get(x_629, 6);
lean_inc(x_639);
x_640 = lean_ctor_get(x_629, 7);
lean_inc(x_640);
x_641 = lean_ctor_get(x_629, 8);
lean_inc(x_641);
x_642 = lean_ctor_get_uint8(x_629, sizeof(void*)*10);
x_643 = lean_ctor_get_uint8(x_629, sizeof(void*)*10 + 1);
x_644 = lean_ctor_get_uint8(x_629, sizeof(void*)*10 + 2);
x_645 = lean_ctor_get(x_629, 9);
lean_inc(x_645);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 lean_ctor_release(x_629, 2);
 lean_ctor_release(x_629, 3);
 lean_ctor_release(x_629, 4);
 lean_ctor_release(x_629, 5);
 lean_ctor_release(x_629, 6);
 lean_ctor_release(x_629, 7);
 lean_ctor_release(x_629, 8);
 lean_ctor_release(x_629, 9);
 x_646 = x_629;
} else {
 lean_dec_ref(x_629);
 x_646 = lean_box(0);
}
x_647 = lean_ctor_get(x_630, 3);
lean_inc(x_647);
x_648 = lean_ctor_get(x_630, 4);
lean_inc(x_648);
x_649 = lean_nat_dec_eq(x_647, x_648);
if (x_649 == 0)
{
lean_dec(x_3);
x_650 = x_631;
goto block_668;
}
else
{
lean_object* x_669; lean_object* x_670; 
x_669 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_670 = l_Lean_Elab_Tactic_throwError___rarg(x_669, x_3, x_631);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; 
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec(x_670);
x_650 = x_671;
goto block_668;
}
else
{
uint8_t x_672; 
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_638);
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_630);
lean_dec(x_1);
x_672 = !lean_is_exclusive(x_670);
if (x_672 == 0)
{
return x_670;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_670, 0);
x_674 = lean_ctor_get(x_670, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_670);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
block_668:
{
uint8_t x_651; 
x_651 = !lean_is_exclusive(x_630);
if (x_651 == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_652 = lean_ctor_get(x_630, 4);
lean_dec(x_652);
x_653 = lean_ctor_get(x_630, 3);
lean_dec(x_653);
x_654 = lean_unsigned_to_nat(1u);
x_655 = lean_nat_add(x_647, x_654);
lean_dec(x_647);
lean_ctor_set(x_630, 3, x_655);
if (lean_is_scalar(x_646)) {
 x_656 = lean_alloc_ctor(0, 10, 3);
} else {
 x_656 = x_646;
}
lean_ctor_set(x_656, 0, x_630);
lean_ctor_set(x_656, 1, x_634);
lean_ctor_set(x_656, 2, x_635);
lean_ctor_set(x_656, 3, x_636);
lean_ctor_set(x_656, 4, x_637);
lean_ctor_set(x_656, 5, x_638);
lean_ctor_set(x_656, 6, x_639);
lean_ctor_set(x_656, 7, x_640);
lean_ctor_set(x_656, 8, x_641);
lean_ctor_set(x_656, 9, x_645);
lean_ctor_set_uint8(x_656, sizeof(void*)*10, x_642);
lean_ctor_set_uint8(x_656, sizeof(void*)*10 + 1, x_643);
lean_ctor_set_uint8(x_656, sizeof(void*)*10 + 2, x_644);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_633);
x_2 = x_632;
x_3 = x_657;
x_4 = x_650;
goto _start;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_659 = lean_ctor_get(x_630, 0);
x_660 = lean_ctor_get(x_630, 1);
x_661 = lean_ctor_get(x_630, 2);
lean_inc(x_661);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_630);
x_662 = lean_unsigned_to_nat(1u);
x_663 = lean_nat_add(x_647, x_662);
lean_dec(x_647);
x_664 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_664, 0, x_659);
lean_ctor_set(x_664, 1, x_660);
lean_ctor_set(x_664, 2, x_661);
lean_ctor_set(x_664, 3, x_663);
lean_ctor_set(x_664, 4, x_648);
if (lean_is_scalar(x_646)) {
 x_665 = lean_alloc_ctor(0, 10, 3);
} else {
 x_665 = x_646;
}
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_634);
lean_ctor_set(x_665, 2, x_635);
lean_ctor_set(x_665, 3, x_636);
lean_ctor_set(x_665, 4, x_637);
lean_ctor_set(x_665, 5, x_638);
lean_ctor_set(x_665, 6, x_639);
lean_ctor_set(x_665, 7, x_640);
lean_ctor_set(x_665, 8, x_641);
lean_ctor_set(x_665, 9, x_645);
lean_ctor_set_uint8(x_665, sizeof(void*)*10, x_642);
lean_ctor_set_uint8(x_665, sizeof(void*)*10 + 1, x_643);
lean_ctor_set_uint8(x_665, sizeof(void*)*10 + 2, x_644);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_633);
x_2 = x_632;
x_3 = x_666;
x_4 = x_650;
goto _start;
}
}
}
}
else
{
uint8_t x_676; 
lean_dec(x_3);
lean_dec(x_1);
x_676 = !lean_is_exclusive(x_621);
if (x_676 == 0)
{
return x_621;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_621, 0);
x_678 = lean_ctor_get(x_621, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_621);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
case 10:
{
lean_object* x_680; 
lean_dec(x_8);
lean_inc(x_3);
x_680 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
if (lean_obj_tag(x_681) == 0)
{
uint8_t x_682; 
lean_dec(x_3);
lean_dec(x_1);
x_682 = !lean_is_exclusive(x_680);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_ctor_get(x_680, 0);
lean_dec(x_683);
x_684 = lean_box(0);
lean_ctor_set(x_680, 0, x_684);
return x_680;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_680, 1);
lean_inc(x_685);
lean_dec(x_680);
x_686 = lean_box(0);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_685);
return x_687;
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; uint8_t x_702; uint8_t x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; lean_object* x_709; 
x_688 = lean_ctor_get(x_3, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_680, 1);
lean_inc(x_690);
lean_dec(x_680);
x_691 = lean_ctor_get(x_681, 0);
lean_inc(x_691);
lean_dec(x_681);
x_692 = lean_ctor_get(x_3, 1);
lean_inc(x_692);
x_693 = lean_ctor_get(x_688, 1);
lean_inc(x_693);
x_694 = lean_ctor_get(x_688, 2);
lean_inc(x_694);
x_695 = lean_ctor_get(x_688, 3);
lean_inc(x_695);
x_696 = lean_ctor_get(x_688, 4);
lean_inc(x_696);
x_697 = lean_ctor_get(x_688, 5);
lean_inc(x_697);
x_698 = lean_ctor_get(x_688, 6);
lean_inc(x_698);
x_699 = lean_ctor_get(x_688, 7);
lean_inc(x_699);
x_700 = lean_ctor_get(x_688, 8);
lean_inc(x_700);
x_701 = lean_ctor_get_uint8(x_688, sizeof(void*)*10);
x_702 = lean_ctor_get_uint8(x_688, sizeof(void*)*10 + 1);
x_703 = lean_ctor_get_uint8(x_688, sizeof(void*)*10 + 2);
x_704 = lean_ctor_get(x_688, 9);
lean_inc(x_704);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 lean_ctor_release(x_688, 2);
 lean_ctor_release(x_688, 3);
 lean_ctor_release(x_688, 4);
 lean_ctor_release(x_688, 5);
 lean_ctor_release(x_688, 6);
 lean_ctor_release(x_688, 7);
 lean_ctor_release(x_688, 8);
 lean_ctor_release(x_688, 9);
 x_705 = x_688;
} else {
 lean_dec_ref(x_688);
 x_705 = lean_box(0);
}
x_706 = lean_ctor_get(x_689, 3);
lean_inc(x_706);
x_707 = lean_ctor_get(x_689, 4);
lean_inc(x_707);
x_708 = lean_nat_dec_eq(x_706, x_707);
if (x_708 == 0)
{
lean_dec(x_3);
x_709 = x_690;
goto block_727;
}
else
{
lean_object* x_728; lean_object* x_729; 
x_728 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_729 = l_Lean_Elab_Tactic_throwError___rarg(x_728, x_3, x_690);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; 
x_730 = lean_ctor_get(x_729, 1);
lean_inc(x_730);
lean_dec(x_729);
x_709 = x_730;
goto block_727;
}
else
{
uint8_t x_731; 
lean_dec(x_707);
lean_dec(x_706);
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_700);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_694);
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_689);
lean_dec(x_1);
x_731 = !lean_is_exclusive(x_729);
if (x_731 == 0)
{
return x_729;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_729, 0);
x_733 = lean_ctor_get(x_729, 1);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_729);
x_734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_734, 0, x_732);
lean_ctor_set(x_734, 1, x_733);
return x_734;
}
}
}
block_727:
{
uint8_t x_710; 
x_710 = !lean_is_exclusive(x_689);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_711 = lean_ctor_get(x_689, 4);
lean_dec(x_711);
x_712 = lean_ctor_get(x_689, 3);
lean_dec(x_712);
x_713 = lean_unsigned_to_nat(1u);
x_714 = lean_nat_add(x_706, x_713);
lean_dec(x_706);
lean_ctor_set(x_689, 3, x_714);
if (lean_is_scalar(x_705)) {
 x_715 = lean_alloc_ctor(0, 10, 3);
} else {
 x_715 = x_705;
}
lean_ctor_set(x_715, 0, x_689);
lean_ctor_set(x_715, 1, x_693);
lean_ctor_set(x_715, 2, x_694);
lean_ctor_set(x_715, 3, x_695);
lean_ctor_set(x_715, 4, x_696);
lean_ctor_set(x_715, 5, x_697);
lean_ctor_set(x_715, 6, x_698);
lean_ctor_set(x_715, 7, x_699);
lean_ctor_set(x_715, 8, x_700);
lean_ctor_set(x_715, 9, x_704);
lean_ctor_set_uint8(x_715, sizeof(void*)*10, x_701);
lean_ctor_set_uint8(x_715, sizeof(void*)*10 + 1, x_702);
lean_ctor_set_uint8(x_715, sizeof(void*)*10 + 2, x_703);
x_716 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_692);
x_2 = x_691;
x_3 = x_716;
x_4 = x_709;
goto _start;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_718 = lean_ctor_get(x_689, 0);
x_719 = lean_ctor_get(x_689, 1);
x_720 = lean_ctor_get(x_689, 2);
lean_inc(x_720);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_689);
x_721 = lean_unsigned_to_nat(1u);
x_722 = lean_nat_add(x_706, x_721);
lean_dec(x_706);
x_723 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_723, 0, x_718);
lean_ctor_set(x_723, 1, x_719);
lean_ctor_set(x_723, 2, x_720);
lean_ctor_set(x_723, 3, x_722);
lean_ctor_set(x_723, 4, x_707);
if (lean_is_scalar(x_705)) {
 x_724 = lean_alloc_ctor(0, 10, 3);
} else {
 x_724 = x_705;
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_693);
lean_ctor_set(x_724, 2, x_694);
lean_ctor_set(x_724, 3, x_695);
lean_ctor_set(x_724, 4, x_696);
lean_ctor_set(x_724, 5, x_697);
lean_ctor_set(x_724, 6, x_698);
lean_ctor_set(x_724, 7, x_699);
lean_ctor_set(x_724, 8, x_700);
lean_ctor_set(x_724, 9, x_704);
lean_ctor_set_uint8(x_724, sizeof(void*)*10, x_701);
lean_ctor_set_uint8(x_724, sizeof(void*)*10 + 1, x_702);
lean_ctor_set_uint8(x_724, sizeof(void*)*10 + 2, x_703);
x_725 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_692);
x_2 = x_691;
x_3 = x_725;
x_4 = x_709;
goto _start;
}
}
}
}
else
{
uint8_t x_735; 
lean_dec(x_3);
lean_dec(x_1);
x_735 = !lean_is_exclusive(x_680);
if (x_735 == 0)
{
return x_680;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_680, 0);
x_737 = lean_ctor_get(x_680, 1);
lean_inc(x_737);
lean_inc(x_736);
lean_dec(x_680);
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_736);
lean_ctor_set(x_738, 1, x_737);
return x_738;
}
}
}
case 11:
{
lean_object* x_739; 
lean_dec(x_8);
lean_inc(x_3);
x_739 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
if (lean_obj_tag(x_740) == 0)
{
uint8_t x_741; 
lean_dec(x_3);
lean_dec(x_1);
x_741 = !lean_is_exclusive(x_739);
if (x_741 == 0)
{
lean_object* x_742; lean_object* x_743; 
x_742 = lean_ctor_get(x_739, 0);
lean_dec(x_742);
x_743 = lean_box(0);
lean_ctor_set(x_739, 0, x_743);
return x_739;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_739, 1);
lean_inc(x_744);
lean_dec(x_739);
x_745 = lean_box(0);
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_744);
return x_746;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; uint8_t x_761; uint8_t x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; lean_object* x_768; 
x_747 = lean_ctor_get(x_3, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_739, 1);
lean_inc(x_749);
lean_dec(x_739);
x_750 = lean_ctor_get(x_740, 0);
lean_inc(x_750);
lean_dec(x_740);
x_751 = lean_ctor_get(x_3, 1);
lean_inc(x_751);
x_752 = lean_ctor_get(x_747, 1);
lean_inc(x_752);
x_753 = lean_ctor_get(x_747, 2);
lean_inc(x_753);
x_754 = lean_ctor_get(x_747, 3);
lean_inc(x_754);
x_755 = lean_ctor_get(x_747, 4);
lean_inc(x_755);
x_756 = lean_ctor_get(x_747, 5);
lean_inc(x_756);
x_757 = lean_ctor_get(x_747, 6);
lean_inc(x_757);
x_758 = lean_ctor_get(x_747, 7);
lean_inc(x_758);
x_759 = lean_ctor_get(x_747, 8);
lean_inc(x_759);
x_760 = lean_ctor_get_uint8(x_747, sizeof(void*)*10);
x_761 = lean_ctor_get_uint8(x_747, sizeof(void*)*10 + 1);
x_762 = lean_ctor_get_uint8(x_747, sizeof(void*)*10 + 2);
x_763 = lean_ctor_get(x_747, 9);
lean_inc(x_763);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 lean_ctor_release(x_747, 2);
 lean_ctor_release(x_747, 3);
 lean_ctor_release(x_747, 4);
 lean_ctor_release(x_747, 5);
 lean_ctor_release(x_747, 6);
 lean_ctor_release(x_747, 7);
 lean_ctor_release(x_747, 8);
 lean_ctor_release(x_747, 9);
 x_764 = x_747;
} else {
 lean_dec_ref(x_747);
 x_764 = lean_box(0);
}
x_765 = lean_ctor_get(x_748, 3);
lean_inc(x_765);
x_766 = lean_ctor_get(x_748, 4);
lean_inc(x_766);
x_767 = lean_nat_dec_eq(x_765, x_766);
if (x_767 == 0)
{
lean_dec(x_3);
x_768 = x_749;
goto block_786;
}
else
{
lean_object* x_787; lean_object* x_788; 
x_787 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_788 = l_Lean_Elab_Tactic_throwError___rarg(x_787, x_3, x_749);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; 
x_789 = lean_ctor_get(x_788, 1);
lean_inc(x_789);
lean_dec(x_788);
x_768 = x_789;
goto block_786;
}
else
{
uint8_t x_790; 
lean_dec(x_766);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_759);
lean_dec(x_758);
lean_dec(x_757);
lean_dec(x_756);
lean_dec(x_755);
lean_dec(x_754);
lean_dec(x_753);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_748);
lean_dec(x_1);
x_790 = !lean_is_exclusive(x_788);
if (x_790 == 0)
{
return x_788;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_788, 0);
x_792 = lean_ctor_get(x_788, 1);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_788);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
return x_793;
}
}
}
block_786:
{
uint8_t x_769; 
x_769 = !lean_is_exclusive(x_748);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_770 = lean_ctor_get(x_748, 4);
lean_dec(x_770);
x_771 = lean_ctor_get(x_748, 3);
lean_dec(x_771);
x_772 = lean_unsigned_to_nat(1u);
x_773 = lean_nat_add(x_765, x_772);
lean_dec(x_765);
lean_ctor_set(x_748, 3, x_773);
if (lean_is_scalar(x_764)) {
 x_774 = lean_alloc_ctor(0, 10, 3);
} else {
 x_774 = x_764;
}
lean_ctor_set(x_774, 0, x_748);
lean_ctor_set(x_774, 1, x_752);
lean_ctor_set(x_774, 2, x_753);
lean_ctor_set(x_774, 3, x_754);
lean_ctor_set(x_774, 4, x_755);
lean_ctor_set(x_774, 5, x_756);
lean_ctor_set(x_774, 6, x_757);
lean_ctor_set(x_774, 7, x_758);
lean_ctor_set(x_774, 8, x_759);
lean_ctor_set(x_774, 9, x_763);
lean_ctor_set_uint8(x_774, sizeof(void*)*10, x_760);
lean_ctor_set_uint8(x_774, sizeof(void*)*10 + 1, x_761);
lean_ctor_set_uint8(x_774, sizeof(void*)*10 + 2, x_762);
x_775 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_751);
x_2 = x_750;
x_3 = x_775;
x_4 = x_768;
goto _start;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_777 = lean_ctor_get(x_748, 0);
x_778 = lean_ctor_get(x_748, 1);
x_779 = lean_ctor_get(x_748, 2);
lean_inc(x_779);
lean_inc(x_778);
lean_inc(x_777);
lean_dec(x_748);
x_780 = lean_unsigned_to_nat(1u);
x_781 = lean_nat_add(x_765, x_780);
lean_dec(x_765);
x_782 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_782, 0, x_777);
lean_ctor_set(x_782, 1, x_778);
lean_ctor_set(x_782, 2, x_779);
lean_ctor_set(x_782, 3, x_781);
lean_ctor_set(x_782, 4, x_766);
if (lean_is_scalar(x_764)) {
 x_783 = lean_alloc_ctor(0, 10, 3);
} else {
 x_783 = x_764;
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_752);
lean_ctor_set(x_783, 2, x_753);
lean_ctor_set(x_783, 3, x_754);
lean_ctor_set(x_783, 4, x_755);
lean_ctor_set(x_783, 5, x_756);
lean_ctor_set(x_783, 6, x_757);
lean_ctor_set(x_783, 7, x_758);
lean_ctor_set(x_783, 8, x_759);
lean_ctor_set(x_783, 9, x_763);
lean_ctor_set_uint8(x_783, sizeof(void*)*10, x_760);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 1, x_761);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 2, x_762);
x_784 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_751);
x_2 = x_750;
x_3 = x_784;
x_4 = x_768;
goto _start;
}
}
}
}
else
{
uint8_t x_794; 
lean_dec(x_3);
lean_dec(x_1);
x_794 = !lean_is_exclusive(x_739);
if (x_794 == 0)
{
return x_739;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_739, 0);
x_796 = lean_ctor_get(x_739, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_739);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
}
}
}
default: 
{
lean_object* x_798; 
lean_dec(x_8);
lean_inc(x_3);
x_798 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; 
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
if (lean_obj_tag(x_799) == 0)
{
uint8_t x_800; 
lean_dec(x_3);
lean_dec(x_1);
x_800 = !lean_is_exclusive(x_798);
if (x_800 == 0)
{
lean_object* x_801; lean_object* x_802; 
x_801 = lean_ctor_get(x_798, 0);
lean_dec(x_801);
x_802 = lean_box(0);
lean_ctor_set(x_798, 0, x_802);
return x_798;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_798, 1);
lean_inc(x_803);
lean_dec(x_798);
x_804 = lean_box(0);
x_805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_803);
return x_805;
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint8_t x_819; uint8_t x_820; uint8_t x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; uint8_t x_826; lean_object* x_827; 
x_806 = lean_ctor_get(x_3, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_798, 1);
lean_inc(x_808);
lean_dec(x_798);
x_809 = lean_ctor_get(x_799, 0);
lean_inc(x_809);
lean_dec(x_799);
x_810 = lean_ctor_get(x_3, 1);
lean_inc(x_810);
x_811 = lean_ctor_get(x_806, 1);
lean_inc(x_811);
x_812 = lean_ctor_get(x_806, 2);
lean_inc(x_812);
x_813 = lean_ctor_get(x_806, 3);
lean_inc(x_813);
x_814 = lean_ctor_get(x_806, 4);
lean_inc(x_814);
x_815 = lean_ctor_get(x_806, 5);
lean_inc(x_815);
x_816 = lean_ctor_get(x_806, 6);
lean_inc(x_816);
x_817 = lean_ctor_get(x_806, 7);
lean_inc(x_817);
x_818 = lean_ctor_get(x_806, 8);
lean_inc(x_818);
x_819 = lean_ctor_get_uint8(x_806, sizeof(void*)*10);
x_820 = lean_ctor_get_uint8(x_806, sizeof(void*)*10 + 1);
x_821 = lean_ctor_get_uint8(x_806, sizeof(void*)*10 + 2);
x_822 = lean_ctor_get(x_806, 9);
lean_inc(x_822);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 lean_ctor_release(x_806, 2);
 lean_ctor_release(x_806, 3);
 lean_ctor_release(x_806, 4);
 lean_ctor_release(x_806, 5);
 lean_ctor_release(x_806, 6);
 lean_ctor_release(x_806, 7);
 lean_ctor_release(x_806, 8);
 lean_ctor_release(x_806, 9);
 x_823 = x_806;
} else {
 lean_dec_ref(x_806);
 x_823 = lean_box(0);
}
x_824 = lean_ctor_get(x_807, 3);
lean_inc(x_824);
x_825 = lean_ctor_get(x_807, 4);
lean_inc(x_825);
x_826 = lean_nat_dec_eq(x_824, x_825);
if (x_826 == 0)
{
lean_dec(x_3);
x_827 = x_808;
goto block_845;
}
else
{
lean_object* x_846; lean_object* x_847; 
x_846 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_847 = l_Lean_Elab_Tactic_throwError___rarg(x_846, x_3, x_808);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; 
x_848 = lean_ctor_get(x_847, 1);
lean_inc(x_848);
lean_dec(x_847);
x_827 = x_848;
goto block_845;
}
else
{
uint8_t x_849; 
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_818);
lean_dec(x_817);
lean_dec(x_816);
lean_dec(x_815);
lean_dec(x_814);
lean_dec(x_813);
lean_dec(x_812);
lean_dec(x_811);
lean_dec(x_810);
lean_dec(x_809);
lean_dec(x_807);
lean_dec(x_1);
x_849 = !lean_is_exclusive(x_847);
if (x_849 == 0)
{
return x_847;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_847, 0);
x_851 = lean_ctor_get(x_847, 1);
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_847);
x_852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_852, 0, x_850);
lean_ctor_set(x_852, 1, x_851);
return x_852;
}
}
}
block_845:
{
uint8_t x_828; 
x_828 = !lean_is_exclusive(x_807);
if (x_828 == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_829 = lean_ctor_get(x_807, 4);
lean_dec(x_829);
x_830 = lean_ctor_get(x_807, 3);
lean_dec(x_830);
x_831 = lean_unsigned_to_nat(1u);
x_832 = lean_nat_add(x_824, x_831);
lean_dec(x_824);
lean_ctor_set(x_807, 3, x_832);
if (lean_is_scalar(x_823)) {
 x_833 = lean_alloc_ctor(0, 10, 3);
} else {
 x_833 = x_823;
}
lean_ctor_set(x_833, 0, x_807);
lean_ctor_set(x_833, 1, x_811);
lean_ctor_set(x_833, 2, x_812);
lean_ctor_set(x_833, 3, x_813);
lean_ctor_set(x_833, 4, x_814);
lean_ctor_set(x_833, 5, x_815);
lean_ctor_set(x_833, 6, x_816);
lean_ctor_set(x_833, 7, x_817);
lean_ctor_set(x_833, 8, x_818);
lean_ctor_set(x_833, 9, x_822);
lean_ctor_set_uint8(x_833, sizeof(void*)*10, x_819);
lean_ctor_set_uint8(x_833, sizeof(void*)*10 + 1, x_820);
lean_ctor_set_uint8(x_833, sizeof(void*)*10 + 2, x_821);
x_834 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_810);
x_2 = x_809;
x_3 = x_834;
x_4 = x_827;
goto _start;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_836 = lean_ctor_get(x_807, 0);
x_837 = lean_ctor_get(x_807, 1);
x_838 = lean_ctor_get(x_807, 2);
lean_inc(x_838);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_807);
x_839 = lean_unsigned_to_nat(1u);
x_840 = lean_nat_add(x_824, x_839);
lean_dec(x_824);
x_841 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_841, 0, x_836);
lean_ctor_set(x_841, 1, x_837);
lean_ctor_set(x_841, 2, x_838);
lean_ctor_set(x_841, 3, x_840);
lean_ctor_set(x_841, 4, x_825);
if (lean_is_scalar(x_823)) {
 x_842 = lean_alloc_ctor(0, 10, 3);
} else {
 x_842 = x_823;
}
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_811);
lean_ctor_set(x_842, 2, x_812);
lean_ctor_set(x_842, 3, x_813);
lean_ctor_set(x_842, 4, x_814);
lean_ctor_set(x_842, 5, x_815);
lean_ctor_set(x_842, 6, x_816);
lean_ctor_set(x_842, 7, x_817);
lean_ctor_set(x_842, 8, x_818);
lean_ctor_set(x_842, 9, x_822);
lean_ctor_set_uint8(x_842, sizeof(void*)*10, x_819);
lean_ctor_set_uint8(x_842, sizeof(void*)*10 + 1, x_820);
lean_ctor_set_uint8(x_842, sizeof(void*)*10 + 2, x_821);
x_843 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_810);
x_2 = x_809;
x_3 = x_843;
x_4 = x_827;
goto _start;
}
}
}
}
else
{
uint8_t x_853; 
lean_dec(x_3);
lean_dec(x_1);
x_853 = !lean_is_exclusive(x_798);
if (x_853 == 0)
{
return x_798;
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_854 = lean_ctor_get(x_798, 0);
x_855 = lean_ctor_get(x_798, 1);
lean_inc(x_855);
lean_inc(x_854);
lean_dec(x_798);
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
return x_856;
}
}
}
}
}
else
{
uint8_t x_857; 
lean_dec(x_3);
lean_dec(x_1);
x_857 = !lean_is_exclusive(x_5);
if (x_857 == 0)
{
return x_5;
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_858 = lean_ctor_get(x_5, 0);
x_859 = lean_ctor_get(x_5, 1);
lean_inc(x_859);
lean_inc(x_858);
lean_dec(x_5);
x_860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_860, 1, x_859);
return x_860;
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
x_54 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
x_62 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
x_18 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_6);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_2);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_23 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_15, x_16, x_22, x_4, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_4);
lean_inc(x_15);
x_25 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_3, x_21, x_15, x_4, x_24);
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
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_dec(x_36);
x_37 = l_Array_isEmpty___rarg(x_35);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_33);
x_39 = l_List_redLength___main___rarg(x_15);
x_40 = lean_mk_empty_array_with_capacity(x_39);
lean_dec(x_39);
x_41 = l_List_toArrayAux___main___rarg(x_15, x_40);
lean_ctor_set(x_28, 1, x_41);
lean_ctor_set(x_28, 0, x_38);
if (x_37 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_25);
x_42 = l_Lean_Syntax_inhabited;
x_43 = lean_array_get(x_42, x_35, x_22);
lean_dec(x_35);
x_44 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_45 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_43, x_44, x_4, x_30);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_28);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_28);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_4);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_28, 0);
lean_inc(x_54);
lean_dec(x_28);
x_55 = l_Array_isEmpty___rarg(x_54);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_13);
lean_ctor_set(x_56, 1, x_32);
lean_ctor_set(x_56, 2, x_33);
x_57 = l_List_redLength___main___rarg(x_15);
x_58 = lean_mk_empty_array_with_capacity(x_57);
lean_dec(x_57);
x_59 = l_List_toArrayAux___main___rarg(x_15, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
if (x_55 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_25);
x_61 = l_Lean_Syntax_inhabited;
x_62 = lean_array_get(x_61, x_54, x_22);
lean_dec(x_54);
x_63 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_64 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_62, x_63, x_4, x_30);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_60);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_dec(x_54);
lean_dec(x_4);
lean_ctor_set(x_25, 0, x_60);
return x_25;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
lean_dec(x_25);
x_73 = lean_ctor_get(x_26, 0);
lean_inc(x_73);
lean_dec(x_26);
x_74 = lean_ctor_get(x_27, 0);
lean_inc(x_74);
lean_dec(x_27);
x_75 = lean_ctor_get(x_28, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_76 = x_28;
} else {
 lean_dec_ref(x_28);
 x_76 = lean_box(0);
}
x_77 = l_Array_isEmpty___rarg(x_75);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_13);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_74);
x_79 = l_List_redLength___main___rarg(x_15);
x_80 = lean_mk_empty_array_with_capacity(x_79);
lean_dec(x_79);
x_81 = l_List_toArrayAux___main___rarg(x_15, x_80);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_76;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
if (x_77 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = l_Lean_Syntax_inhabited;
x_84 = lean_array_get(x_83, x_75, x_22);
lean_dec(x_75);
x_85 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_86 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_84, x_85, x_4, x_72);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
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
lean_object* x_94; 
lean_dec(x_75);
lean_dec(x_4);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_82);
lean_ctor_set(x_94, 1, x_72);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_4);
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
else
{
uint8_t x_99; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_4);
x_99 = !lean_is_exclusive(x_23);
if (x_99 == 0)
{
return x_23;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_23, 0);
x_101 = lean_ctor_get(x_23, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_23);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_8);
lean_dec(x_4);
x_103 = l_Array_empty___closed__1;
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_13);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_6, 0, x_105);
return x_6;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_106 = lean_ctor_get(x_6, 0);
x_107 = lean_ctor_get(x_6, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_6);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_mkRecFor___closed__1;
x_111 = lean_name_mk_string(x_109, x_110);
x_112 = l_Lean_Syntax_isNone(x_2);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_106, 4);
lean_inc(x_113);
lean_dec(x_106);
x_114 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_2);
x_115 = lean_box(0);
lean_inc(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Array_empty___closed__1;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_121 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_113, x_114, x_120, x_4, x_107);
lean_dec(x_114);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_4);
lean_inc(x_113);
x_123 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_3, x_119, x_113, x_4, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = l_Array_isEmpty___rarg(x_131);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_111);
lean_ctor_set(x_134, 1, x_129);
lean_ctor_set(x_134, 2, x_130);
x_135 = l_List_redLength___main___rarg(x_113);
x_136 = lean_mk_empty_array_with_capacity(x_135);
lean_dec(x_135);
x_137 = l_List_toArrayAux___main___rarg(x_113, x_136);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_137);
if (x_133 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_128);
x_139 = l_Lean_Syntax_inhabited;
x_140 = lean_array_get(x_139, x_131, x_120);
lean_dec(x_131);
x_141 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_142 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_140, x_141, x_4, x_127);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_138);
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; 
lean_dec(x_131);
lean_dec(x_4);
if (lean_is_scalar(x_128)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_128;
}
lean_ctor_set(x_150, 0, x_138);
lean_ctor_set(x_150, 1, x_127);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_4);
x_151 = lean_ctor_get(x_123, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_123, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_153 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_dec(x_119);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_4);
x_155 = lean_ctor_get(x_121, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_157 = x_121;
} else {
 lean_dec_ref(x_121);
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
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_106);
lean_dec(x_4);
x_159 = l_Array_empty___closed__1;
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_111);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_107);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_6);
if (x_163 == 0)
{
return x_6;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_6, 0);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_6);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
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
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_22);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
if (x_51 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_41);
x_53 = l_Lean_Syntax_inhabited;
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get(x_53, x_50, x_54);
lean_dec(x_50);
x_56 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_57 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_55, x_56, x_3, x_46);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_52);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_52);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_3);
lean_ctor_set(x_41, 0, x_52);
return x_41;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_dec(x_41);
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
lean_dec(x_42);
x_68 = lean_ctor_get(x_43, 0);
lean_inc(x_68);
lean_dec(x_43);
x_69 = lean_ctor_get(x_44, 0);
lean_inc(x_69);
lean_dec(x_44);
x_70 = l_Array_isEmpty___rarg(x_69);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
if (x_70 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = l_Lean_Syntax_inhabited;
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_get(x_72, x_69, x_73);
lean_dec(x_69);
x_75 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_76 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_74, x_75, x_3, x_66);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_71);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_69);
lean_dec(x_3);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_66);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_22);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
return x_41;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_41, 0);
x_87 = lean_ctor_get(x_41, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_41);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_free_object(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_33);
if (x_89 == 0)
{
return x_33;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_33, 0);
x_91 = lean_ctor_get(x_33, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_33);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_26, 0);
lean_inc(x_93);
lean_dec(x_26);
lean_inc(x_22);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_94, 0, x_22);
x_95 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_95, 0, x_94);
lean_inc(x_3);
x_96 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_93, x_95, x_3, x_27);
lean_dec(x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_24);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Array_empty___closed__1;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_get_size(x_97);
lean_inc(x_3);
lean_inc(x_104);
x_105 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_20, x_97, x_104, x_104, x_103, x_3, x_98);
lean_dec(x_104);
lean_dec(x_97);
lean_dec(x_20);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
lean_dec(x_108);
x_114 = l_Array_isEmpty___rarg(x_113);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_22);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 2, x_112);
if (x_114 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_110);
x_116 = l_Lean_Syntax_inhabited;
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_array_get(x_116, x_113, x_117);
lean_dec(x_113);
x_119 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_120 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_118, x_119, x_3, x_109);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
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
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_115);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_115);
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
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
lean_object* x_128; 
lean_dec(x_113);
lean_dec(x_3);
if (lean_is_scalar(x_110)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_110;
}
lean_ctor_set(x_128, 0, x_115);
lean_ctor_set(x_128, 1, x_109);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_22);
lean_dec(x_3);
x_129 = lean_ctor_get(x_105, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_105, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_131 = x_105;
} else {
 lean_dec_ref(x_105);
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
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
x_133 = lean_ctor_get(x_96, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_96, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_135 = x_96;
} else {
 lean_dec_ref(x_96);
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
uint8_t x_137; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
x_137 = !lean_is_exclusive(x_25);
if (x_137 == 0)
{
return x_25;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_25, 0);
x_139 = lean_ctor_get(x_25, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_25);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_8);
x_141 = l_Array_empty___closed__1;
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_22);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_18, 0, x_142);
return x_18;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_18, 0);
x_144 = lean_ctor_get(x_18, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_18);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = l_Lean_Syntax_isNone(x_8);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_148 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_144);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
lean_inc(x_145);
x_153 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_153, 0, x_145);
x_154 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_154, 0, x_153);
lean_inc(x_3);
x_155 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_151, x_154, x_3, x_150);
lean_dec(x_151);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_152;
}
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Array_empty___closed__1;
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_get_size(x_156);
lean_inc(x_3);
lean_inc(x_163);
x_164 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_143, x_156, x_163, x_163, x_162, x_3, x_157);
lean_dec(x_163);
lean_dec(x_156);
lean_dec(x_143);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_ctor_get(x_167, 0);
lean_inc(x_172);
lean_dec(x_167);
x_173 = l_Array_isEmpty___rarg(x_172);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_145);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_171);
if (x_173 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_169);
x_175 = l_Lean_Syntax_inhabited;
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_array_get(x_175, x_172, x_176);
lean_dec(x_172);
x_178 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_179 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_177, x_178, x_3, x_168);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_174);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_174);
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
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
lean_object* x_187; 
lean_dec(x_172);
lean_dec(x_3);
if (lean_is_scalar(x_169)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_169;
}
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_168);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_145);
lean_dec(x_3);
x_188 = lean_ctor_get(x_164, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_164, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_190 = x_164;
} else {
 lean_dec_ref(x_164);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_152);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_3);
x_192 = lean_ctor_get(x_155, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_155, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_194 = x_155;
} else {
 lean_dec_ref(x_155);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_3);
x_196 = lean_ctor_get(x_148, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_148, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_198 = x_148;
} else {
 lean_dec_ref(x_148);
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
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_143);
lean_dec(x_3);
lean_dec(x_8);
x_200 = l_Array_empty___closed__1;
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_145);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_144);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_3);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_18);
if (x_203 == 0)
{
return x_18;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_18, 0);
x_205 = lean_ctor_get(x_18, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_18);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; lean_object* x_208; 
lean_dec(x_6);
x_207 = 0;
x_208 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_207, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec(x_210);
lean_ctor_set(x_208, 0, x_211);
return x_208;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_208, 0);
x_213 = lean_ctor_get(x_208, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_208);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_208);
if (x_216 == 0)
{
return x_208;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_208, 0);
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_208);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_220 = lean_ctor_get(x_11, 0);
x_221 = lean_ctor_get(x_11, 1);
x_222 = lean_ctor_get(x_11, 2);
x_223 = lean_ctor_get(x_11, 3);
x_224 = lean_ctor_get(x_11, 4);
x_225 = lean_ctor_get(x_11, 5);
x_226 = lean_ctor_get(x_11, 6);
x_227 = lean_ctor_get(x_11, 7);
x_228 = lean_ctor_get(x_11, 8);
x_229 = lean_ctor_get_uint8(x_11, sizeof(void*)*10);
x_230 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 1);
x_231 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 2);
x_232 = lean_ctor_get(x_11, 9);
lean_inc(x_232);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_11);
x_233 = l_Lean_Elab_replaceRef(x_1, x_232);
lean_dec(x_232);
x_234 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_234, 0, x_220);
lean_ctor_set(x_234, 1, x_221);
lean_ctor_set(x_234, 2, x_222);
lean_ctor_set(x_234, 3, x_223);
lean_ctor_set(x_234, 4, x_224);
lean_ctor_set(x_234, 5, x_225);
lean_ctor_set(x_234, 6, x_226);
lean_ctor_set(x_234, 7, x_227);
lean_ctor_set(x_234, 8, x_228);
lean_ctor_set(x_234, 9, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*10, x_229);
lean_ctor_set_uint8(x_234, sizeof(void*)*10 + 1, x_230);
lean_ctor_set_uint8(x_234, sizeof(void*)*10 + 2, x_231);
lean_ctor_set(x_3, 0, x_234);
if (x_9 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_unsigned_to_nat(1u);
x_236 = l_Lean_Syntax_getIdAt(x_6, x_235);
lean_dec(x_6);
x_237 = l_Lean_Name_eraseMacroScopes(x_236);
lean_dec(x_236);
lean_inc(x_3);
x_238 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_237, x_3, x_4);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = l_Lean_Syntax_isNone(x_8);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_241);
x_244 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_245 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_240);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
lean_inc(x_242);
x_250 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_250, 0, x_242);
x_251 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_251, 0, x_250);
lean_inc(x_3);
x_252 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_248, x_251, x_3, x_247);
lean_dec(x_248);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_249;
}
lean_ctor_set(x_256, 0, x_244);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Array_empty___closed__1;
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_array_get_size(x_253);
lean_inc(x_3);
lean_inc(x_260);
x_261 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_239, x_253, x_260, x_260, x_259, x_3, x_254);
lean_dec(x_260);
lean_dec(x_253);
lean_dec(x_239);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_266 = x_261;
} else {
 lean_dec_ref(x_261);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_262, 0);
lean_inc(x_267);
lean_dec(x_262);
x_268 = lean_ctor_get(x_263, 0);
lean_inc(x_268);
lean_dec(x_263);
x_269 = lean_ctor_get(x_264, 0);
lean_inc(x_269);
lean_dec(x_264);
x_270 = l_Array_isEmpty___rarg(x_269);
x_271 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_271, 0, x_242);
lean_ctor_set(x_271, 1, x_267);
lean_ctor_set(x_271, 2, x_268);
if (x_270 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_266);
x_272 = l_Lean_Syntax_inhabited;
x_273 = lean_unsigned_to_nat(0u);
x_274 = lean_array_get(x_272, x_269, x_273);
lean_dec(x_269);
x_275 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_276 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_274, x_275, x_3, x_265);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_271);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_271);
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_282 = x_276;
} else {
 lean_dec_ref(x_276);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
else
{
lean_object* x_284; 
lean_dec(x_269);
lean_dec(x_3);
if (lean_is_scalar(x_266)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_266;
}
lean_ctor_set(x_284, 0, x_271);
lean_ctor_set(x_284, 1, x_265);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_242);
lean_dec(x_3);
x_285 = lean_ctor_get(x_261, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_261, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_287 = x_261;
} else {
 lean_dec_ref(x_261);
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
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_249);
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_3);
x_289 = lean_ctor_get(x_252, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_252, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_291 = x_252;
} else {
 lean_dec_ref(x_252);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_3);
x_293 = lean_ctor_get(x_245, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_245, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_295 = x_245;
} else {
 lean_dec_ref(x_245);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_239);
lean_dec(x_3);
lean_dec(x_8);
x_297 = l_Array_empty___closed__1;
x_298 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_298, 0, x_242);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_297);
if (lean_is_scalar(x_241)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_241;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_240);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_3);
lean_dec(x_8);
x_300 = lean_ctor_get(x_238, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_238, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_302 = x_238;
} else {
 lean_dec_ref(x_238);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
uint8_t x_304; lean_object* x_305; 
lean_dec(x_6);
x_304 = 0;
x_305 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_304, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_308 = x_305;
} else {
 lean_dec_ref(x_305);
 x_308 = lean_box(0);
}
x_309 = lean_ctor_get(x_306, 0);
lean_inc(x_309);
lean_dec(x_306);
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_308;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_307);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_311 = lean_ctor_get(x_305, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_305, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_313 = x_305;
} else {
 lean_dec_ref(x_305);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; uint8_t x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_315 = lean_ctor_get(x_3, 0);
x_316 = lean_ctor_get(x_3, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_3);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_315, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 3);
lean_inc(x_320);
x_321 = lean_ctor_get(x_315, 4);
lean_inc(x_321);
x_322 = lean_ctor_get(x_315, 5);
lean_inc(x_322);
x_323 = lean_ctor_get(x_315, 6);
lean_inc(x_323);
x_324 = lean_ctor_get(x_315, 7);
lean_inc(x_324);
x_325 = lean_ctor_get(x_315, 8);
lean_inc(x_325);
x_326 = lean_ctor_get_uint8(x_315, sizeof(void*)*10);
x_327 = lean_ctor_get_uint8(x_315, sizeof(void*)*10 + 1);
x_328 = lean_ctor_get_uint8(x_315, sizeof(void*)*10 + 2);
x_329 = lean_ctor_get(x_315, 9);
lean_inc(x_329);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 lean_ctor_release(x_315, 2);
 lean_ctor_release(x_315, 3);
 lean_ctor_release(x_315, 4);
 lean_ctor_release(x_315, 5);
 lean_ctor_release(x_315, 6);
 lean_ctor_release(x_315, 7);
 lean_ctor_release(x_315, 8);
 lean_ctor_release(x_315, 9);
 x_330 = x_315;
} else {
 lean_dec_ref(x_315);
 x_330 = lean_box(0);
}
x_331 = l_Lean_Elab_replaceRef(x_1, x_329);
lean_dec(x_329);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(0, 10, 3);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_317);
lean_ctor_set(x_332, 1, x_318);
lean_ctor_set(x_332, 2, x_319);
lean_ctor_set(x_332, 3, x_320);
lean_ctor_set(x_332, 4, x_321);
lean_ctor_set(x_332, 5, x_322);
lean_ctor_set(x_332, 6, x_323);
lean_ctor_set(x_332, 7, x_324);
lean_ctor_set(x_332, 8, x_325);
lean_ctor_set(x_332, 9, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*10, x_326);
lean_ctor_set_uint8(x_332, sizeof(void*)*10 + 1, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*10 + 2, x_328);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_316);
if (x_9 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_unsigned_to_nat(1u);
x_335 = l_Lean_Syntax_getIdAt(x_6, x_334);
lean_dec(x_6);
x_336 = l_Lean_Name_eraseMacroScopes(x_335);
lean_dec(x_335);
lean_inc(x_333);
x_337 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_336, x_333, x_4);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = lean_ctor_get(x_338, 0);
lean_inc(x_341);
x_342 = l_Lean_Syntax_isNone(x_8);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_340);
x_343 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_333);
x_344 = l_Lean_Elab_Tactic_getMainGoal(x_333, x_339);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
lean_inc(x_341);
x_349 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_349, 0, x_341);
x_350 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_350, 0, x_349);
lean_inc(x_333);
x_351 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_347, x_350, x_333, x_346);
lean_dec(x_347);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_box(0);
if (lean_is_scalar(x_348)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_348;
}
lean_ctor_set(x_355, 0, x_343);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Array_empty___closed__1;
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_355);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_array_get_size(x_352);
lean_inc(x_333);
lean_inc(x_359);
x_360 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_338, x_352, x_359, x_359, x_358, x_333, x_353);
lean_dec(x_359);
lean_dec(x_352);
lean_dec(x_338);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_360, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_365 = x_360;
} else {
 lean_dec_ref(x_360);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_361, 0);
lean_inc(x_366);
lean_dec(x_361);
x_367 = lean_ctor_get(x_362, 0);
lean_inc(x_367);
lean_dec(x_362);
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
lean_dec(x_363);
x_369 = l_Array_isEmpty___rarg(x_368);
x_370 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_370, 0, x_341);
lean_ctor_set(x_370, 1, x_366);
lean_ctor_set(x_370, 2, x_367);
if (x_369 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_365);
x_371 = l_Lean_Syntax_inhabited;
x_372 = lean_unsigned_to_nat(0u);
x_373 = lean_array_get(x_371, x_368, x_372);
lean_dec(x_368);
x_374 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_375 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_373, x_374, x_333, x_364);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_370);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_370);
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_381 = x_375;
} else {
 lean_dec_ref(x_375);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
}
else
{
lean_object* x_383; 
lean_dec(x_368);
lean_dec(x_333);
if (lean_is_scalar(x_365)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_365;
}
lean_ctor_set(x_383, 0, x_370);
lean_ctor_set(x_383, 1, x_364);
return x_383;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_341);
lean_dec(x_333);
x_384 = lean_ctor_get(x_360, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_360, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_386 = x_360;
} else {
 lean_dec_ref(x_360);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_348);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_338);
lean_dec(x_333);
x_388 = lean_ctor_get(x_351, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_351, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_390 = x_351;
} else {
 lean_dec_ref(x_351);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_338);
lean_dec(x_333);
x_392 = lean_ctor_get(x_344, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_344, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_394 = x_344;
} else {
 lean_dec_ref(x_344);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_338);
lean_dec(x_333);
lean_dec(x_8);
x_396 = l_Array_empty___closed__1;
x_397 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_397, 0, x_341);
lean_ctor_set(x_397, 1, x_396);
lean_ctor_set(x_397, 2, x_396);
if (lean_is_scalar(x_340)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_340;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_339);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_333);
lean_dec(x_8);
x_399 = lean_ctor_get(x_337, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_337, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_401 = x_337;
} else {
 lean_dec_ref(x_337);
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
uint8_t x_403; lean_object* x_404; 
lean_dec(x_6);
x_403 = 0;
x_404 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_403, x_333, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_407 = x_404;
} else {
 lean_dec_ref(x_404);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
lean_dec(x_405);
if (lean_is_scalar(x_407)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_407;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_406);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_410 = lean_ctor_get(x_404, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_404, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_412 = x_404;
} else {
 lean_dec_ref(x_404);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
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
x_23 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = lean_box(0);
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_7);
x_10 = l_Nat_repr(x_7);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Nat_repr(x_6);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_3);
x_25 = l_Lean_Elab_Tactic_throwError___rarg(x_24, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_3);
lean_inc(x_7);
x_27 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(x_1, x_2, x_7, x_7, x_9, x_3, x_26);
lean_dec(x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Tactic_setGoals(x_28, x_3, x_29);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_3);
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
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_7);
x_39 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_1, x_2, x_7, x_7, x_9, x_3, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Tactic_setGoals(x_40, x_3, x_41);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_3);
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
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Array_toList___rarg(x_2);
x_48 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__3(x_47);
x_49 = l_Lean_Elab_Tactic_setGoals(x_48, x_3, x_4);
lean_dec(x_3);
return x_49;
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
x_3 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
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
x_34 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_26, x_19, x_28, x_3, x_27);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_33, x_32, x_3, x_35);
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
x_3 = l_Lean_Parser_Tactic_cases___elambda__1___closed__1;
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
