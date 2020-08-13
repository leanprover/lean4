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
lean_object* l_Lean_Elab_Tactic_withRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Meta_mkAuxName___closed__1;
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
lean_object* l_Lean_Elab_Term_trace(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace), 4, 2);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 10);
lean_dec(x_10);
lean_ctor_set(x_8, 10, x_1);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_5, x_12);
lean_dec(x_5);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 5, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_14);
x_17 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_16, x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
x_23 = lean_ctor_get(x_8, 5);
x_24 = lean_ctor_get(x_8, 6);
x_25 = lean_ctor_get(x_8, 7);
x_26 = lean_ctor_get(x_8, 8);
x_27 = lean_ctor_get(x_8, 9);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 1);
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 2);
lean_inc(x_27);
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
x_31 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
lean_ctor_set(x_31, 6, x_24);
lean_ctor_set(x_31, 7, x_25);
lean_ctor_set(x_31, 8, x_26);
lean_ctor_set(x_31, 9, x_27);
lean_ctor_set(x_31, 10, x_1);
lean_ctor_set_uint8(x_31, sizeof(void*)*11, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*11 + 1, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*11 + 2, x_30);
lean_ctor_set(x_2, 0, x_31);
lean_inc(x_5);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_5);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_5, x_33);
lean_dec(x_5);
x_35 = l_Lean_Syntax_getArgs(x_34);
lean_dec(x_34);
x_36 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 5, 3);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_32);
lean_closure_set(x_37, 2, x_35);
x_38 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_37, x_2, x_3);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
x_50 = lean_ctor_get(x_39, 9);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_39, sizeof(void*)*11);
x_52 = lean_ctor_get_uint8(x_39, sizeof(void*)*11 + 1);
x_53 = lean_ctor_get_uint8(x_39, sizeof(void*)*11 + 2);
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
 lean_ctor_release(x_39, 10);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 11, 3);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_42);
lean_ctor_set(x_55, 2, x_43);
lean_ctor_set(x_55, 3, x_44);
lean_ctor_set(x_55, 4, x_45);
lean_ctor_set(x_55, 5, x_46);
lean_ctor_set(x_55, 6, x_47);
lean_ctor_set(x_55, 7, x_48);
lean_ctor_set(x_55, 8, x_49);
lean_ctor_set(x_55, 9, x_50);
lean_ctor_set(x_55, 10, x_1);
lean_ctor_set_uint8(x_55, sizeof(void*)*11, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*11 + 1, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*11 + 2, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
lean_inc(x_5);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_57, 0, x_5);
x_58 = lean_unsigned_to_nat(1u);
x_59 = l_Lean_Syntax_getArg(x_5, x_58);
lean_dec(x_5);
x_60 = l_Lean_Syntax_getArgs(x_59);
lean_dec(x_59);
x_61 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_62 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1), 5, 3);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_57);
lean_closure_set(x_62, 2, x_60);
x_63 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_62, x_56, x_3);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_64 = l_Array_empty___closed__1;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
return x_65;
}
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
x_15 = l_Lean_Meta_mkAuxName___closed__1;
x_16 = lean_name_eq(x_13, x_15);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_17, 10);
lean_dec(x_20);
lean_inc(x_10);
lean_ctor_set(x_17, 10, x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
x_22 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace), 4, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_14);
x_24 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_23, x_21, x_5);
if (x_16 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = 0;
x_26 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_13, x_25, x_1);
if (x_26 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_10, x_28);
lean_dec(x_10);
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_13);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_4);
x_38 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_29, x_37, x_4, x_27);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_3 = x_12;
x_5 = x_39;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_dec(x_24);
x_3 = x_12;
x_5 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec(x_24);
x_3 = x_12;
x_5 = x_55;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_24, 0);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_24);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
x_63 = lean_ctor_get(x_17, 2);
x_64 = lean_ctor_get(x_17, 3);
x_65 = lean_ctor_get(x_17, 4);
x_66 = lean_ctor_get(x_17, 5);
x_67 = lean_ctor_get(x_17, 6);
x_68 = lean_ctor_get(x_17, 7);
x_69 = lean_ctor_get(x_17, 8);
x_70 = lean_ctor_get(x_17, 9);
x_71 = lean_ctor_get_uint8(x_17, sizeof(void*)*11);
x_72 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 1);
x_73 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
lean_inc(x_10);
x_74 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_62);
lean_ctor_set(x_74, 2, x_63);
lean_ctor_set(x_74, 3, x_64);
lean_ctor_set(x_74, 4, x_65);
lean_ctor_set(x_74, 5, x_66);
lean_ctor_set(x_74, 6, x_67);
lean_ctor_set(x_74, 7, x_68);
lean_ctor_set(x_74, 8, x_69);
lean_ctor_set(x_74, 9, x_70);
lean_ctor_set(x_74, 10, x_10);
lean_ctor_set_uint8(x_74, sizeof(void*)*11, x_71);
lean_ctor_set_uint8(x_74, sizeof(void*)*11 + 1, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*11 + 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_18);
x_76 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
x_77 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace), 4, 2);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_14);
x_78 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_77, x_75, x_5);
if (x_16 == 0)
{
uint8_t x_79; uint8_t x_80; 
x_79 = 0;
x_80 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_13, x_79, x_1);
if (x_80 == 0)
{
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Syntax_getArg(x_10, x_82);
lean_dec(x_10);
x_84 = l_Lean_Name_toString___closed__1;
x_85 = l_Lean_Name_toStringWithSep___main(x_84, x_13);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_91 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_4);
x_92 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_83, x_91, x_4, x_81);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_3 = x_12;
x_5 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_12);
lean_dec(x_4);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
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
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_99 = lean_ctor_get(x_78, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_101 = x_78;
} else {
 lean_dec_ref(x_78);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_78, 1);
lean_inc(x_103);
lean_dec(x_78);
x_3 = x_12;
x_5 = x_103;
goto _start;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_12);
lean_dec(x_4);
x_105 = lean_ctor_get(x_78, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_107 = x_78;
} else {
 lean_dec_ref(x_78);
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
else
{
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_78, 1);
lean_inc(x_109);
lean_dec(x_78);
x_3 = x_12;
x_5 = x_109;
goto _start;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_12);
lean_dec(x_4);
x_111 = lean_ctor_get(x_78, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_78, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_113 = x_78;
} else {
 lean_dec_ref(x_78);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
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
x_30 = lean_ctor_get(x_17, 9);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_17, sizeof(void*)*11);
x_32 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 1);
x_33 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 2);
x_34 = lean_ctor_get(x_17, 10);
lean_inc(x_34);
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
 lean_ctor_release(x_17, 10);
 x_35 = x_17;
} else {
 lean_dec_ref(x_17);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_18, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_18, 4);
lean_inc(x_37);
x_38 = lean_nat_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_3);
x_39 = x_19;
goto block_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_59 = l_Lean_Elab_Tactic_throwError___rarg(x_58, x_3, x_19);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_39 = x_60;
goto block_57;
}
else
{
uint8_t x_61; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
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
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
block_57:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_18, 4);
lean_dec(x_41);
x_42 = lean_ctor_get(x_18, 3);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_36, x_43);
lean_dec(x_36);
lean_ctor_set(x_18, 3, x_44);
if (lean_is_scalar(x_35)) {
 x_45 = lean_alloc_ctor(0, 11, 3);
} else {
 x_45 = x_35;
}
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_22);
lean_ctor_set(x_45, 2, x_23);
lean_ctor_set(x_45, 3, x_24);
lean_ctor_set(x_45, 4, x_25);
lean_ctor_set(x_45, 5, x_26);
lean_ctor_set(x_45, 6, x_27);
lean_ctor_set(x_45, 7, x_28);
lean_ctor_set(x_45, 8, x_29);
lean_ctor_set(x_45, 9, x_30);
lean_ctor_set(x_45, 10, x_34);
lean_ctor_set_uint8(x_45, sizeof(void*)*11, x_31);
lean_ctor_set_uint8(x_45, sizeof(void*)*11 + 1, x_32);
lean_ctor_set_uint8(x_45, sizeof(void*)*11 + 2, x_33);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_21);
x_2 = x_20;
x_3 = x_46;
x_4 = x_39;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
x_50 = lean_ctor_get(x_18, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_36, x_51);
lean_dec(x_36);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_37);
if (lean_is_scalar(x_35)) {
 x_54 = lean_alloc_ctor(0, 11, 3);
} else {
 x_54 = x_35;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_22);
lean_ctor_set(x_54, 2, x_23);
lean_ctor_set(x_54, 3, x_24);
lean_ctor_set(x_54, 4, x_25);
lean_ctor_set(x_54, 5, x_26);
lean_ctor_set(x_54, 6, x_27);
lean_ctor_set(x_54, 7, x_28);
lean_ctor_set(x_54, 8, x_29);
lean_ctor_set(x_54, 9, x_30);
lean_ctor_set(x_54, 10, x_34);
lean_ctor_set_uint8(x_54, sizeof(void*)*11, x_31);
lean_ctor_set_uint8(x_54, sizeof(void*)*11 + 1, x_32);
lean_ctor_set_uint8(x_54, sizeof(void*)*11 + 2, x_33);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_21);
x_2 = x_20;
x_3 = x_55;
x_4 = x_39;
goto _start;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
return x_9;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 1:
{
lean_object* x_69; 
lean_dec(x_8);
lean_inc(x_3);
x_69 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
lean_dec(x_70);
x_81 = lean_ctor_get(x_3, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_77, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_77, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 9);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_77, sizeof(void*)*11);
x_92 = lean_ctor_get_uint8(x_77, sizeof(void*)*11 + 1);
x_93 = lean_ctor_get_uint8(x_77, sizeof(void*)*11 + 2);
x_94 = lean_ctor_get(x_77, 10);
lean_inc(x_94);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 lean_ctor_release(x_77, 7);
 lean_ctor_release(x_77, 8);
 lean_ctor_release(x_77, 9);
 lean_ctor_release(x_77, 10);
 x_95 = x_77;
} else {
 lean_dec_ref(x_77);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_78, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_78, 4);
lean_inc(x_97);
x_98 = lean_nat_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_dec(x_3);
x_99 = x_79;
goto block_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_119 = l_Lean_Elab_Tactic_throwError___rarg(x_118, x_3, x_79);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_99 = x_120;
goto block_117;
}
else
{
uint8_t x_121; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
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
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
return x_119;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_119, 0);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_119);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
block_117:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_78);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_78, 4);
lean_dec(x_101);
x_102 = lean_ctor_get(x_78, 3);
lean_dec(x_102);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_96, x_103);
lean_dec(x_96);
lean_ctor_set(x_78, 3, x_104);
if (lean_is_scalar(x_95)) {
 x_105 = lean_alloc_ctor(0, 11, 3);
} else {
 x_105 = x_95;
}
lean_ctor_set(x_105, 0, x_78);
lean_ctor_set(x_105, 1, x_82);
lean_ctor_set(x_105, 2, x_83);
lean_ctor_set(x_105, 3, x_84);
lean_ctor_set(x_105, 4, x_85);
lean_ctor_set(x_105, 5, x_86);
lean_ctor_set(x_105, 6, x_87);
lean_ctor_set(x_105, 7, x_88);
lean_ctor_set(x_105, 8, x_89);
lean_ctor_set(x_105, 9, x_90);
lean_ctor_set(x_105, 10, x_94);
lean_ctor_set_uint8(x_105, sizeof(void*)*11, x_91);
lean_ctor_set_uint8(x_105, sizeof(void*)*11 + 1, x_92);
lean_ctor_set_uint8(x_105, sizeof(void*)*11 + 2, x_93);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_81);
x_2 = x_80;
x_3 = x_106;
x_4 = x_99;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_78, 0);
x_109 = lean_ctor_get(x_78, 1);
x_110 = lean_ctor_get(x_78, 2);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_78);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_96, x_111);
lean_dec(x_96);
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_112);
lean_ctor_set(x_113, 4, x_97);
if (lean_is_scalar(x_95)) {
 x_114 = lean_alloc_ctor(0, 11, 3);
} else {
 x_114 = x_95;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_82);
lean_ctor_set(x_114, 2, x_83);
lean_ctor_set(x_114, 3, x_84);
lean_ctor_set(x_114, 4, x_85);
lean_ctor_set(x_114, 5, x_86);
lean_ctor_set(x_114, 6, x_87);
lean_ctor_set(x_114, 7, x_88);
lean_ctor_set(x_114, 8, x_89);
lean_ctor_set(x_114, 9, x_90);
lean_ctor_set(x_114, 10, x_94);
lean_ctor_set_uint8(x_114, sizeof(void*)*11, x_91);
lean_ctor_set_uint8(x_114, sizeof(void*)*11 + 1, x_92);
lean_ctor_set_uint8(x_114, sizeof(void*)*11 + 2, x_93);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_81);
x_2 = x_80;
x_3 = x_115;
x_4 = x_99;
goto _start;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_69);
if (x_125 == 0)
{
return x_69;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_69, 0);
x_127 = lean_ctor_get(x_69, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_69);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 2:
{
lean_object* x_129; 
lean_dec(x_8);
lean_inc(x_3);
x_129 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
lean_dec(x_3);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
x_133 = lean_box(0);
lean_ctor_set(x_129, 0, x_133);
return x_129;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; 
x_137 = lean_ctor_get(x_3, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 1);
lean_inc(x_139);
lean_dec(x_129);
x_140 = lean_ctor_get(x_130, 0);
lean_inc(x_140);
lean_dec(x_130);
x_141 = lean_ctor_get(x_3, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_137, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_137, 5);
lean_inc(x_146);
x_147 = lean_ctor_get(x_137, 6);
lean_inc(x_147);
x_148 = lean_ctor_get(x_137, 7);
lean_inc(x_148);
x_149 = lean_ctor_get(x_137, 8);
lean_inc(x_149);
x_150 = lean_ctor_get(x_137, 9);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_137, sizeof(void*)*11);
x_152 = lean_ctor_get_uint8(x_137, sizeof(void*)*11 + 1);
x_153 = lean_ctor_get_uint8(x_137, sizeof(void*)*11 + 2);
x_154 = lean_ctor_get(x_137, 10);
lean_inc(x_154);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 lean_ctor_release(x_137, 5);
 lean_ctor_release(x_137, 6);
 lean_ctor_release(x_137, 7);
 lean_ctor_release(x_137, 8);
 lean_ctor_release(x_137, 9);
 lean_ctor_release(x_137, 10);
 x_155 = x_137;
} else {
 lean_dec_ref(x_137);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_138, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_138, 4);
lean_inc(x_157);
x_158 = lean_nat_dec_eq(x_156, x_157);
if (x_158 == 0)
{
lean_dec(x_3);
x_159 = x_139;
goto block_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_179 = l_Lean_Elab_Tactic_throwError___rarg(x_178, x_3, x_139);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_159 = x_180;
goto block_177;
}
else
{
uint8_t x_181; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
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
lean_dec(x_140);
lean_dec(x_138);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_179);
if (x_181 == 0)
{
return x_179;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_179, 0);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_179);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
block_177:
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_138);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_138, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_138, 3);
lean_dec(x_162);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_156, x_163);
lean_dec(x_156);
lean_ctor_set(x_138, 3, x_164);
if (lean_is_scalar(x_155)) {
 x_165 = lean_alloc_ctor(0, 11, 3);
} else {
 x_165 = x_155;
}
lean_ctor_set(x_165, 0, x_138);
lean_ctor_set(x_165, 1, x_142);
lean_ctor_set(x_165, 2, x_143);
lean_ctor_set(x_165, 3, x_144);
lean_ctor_set(x_165, 4, x_145);
lean_ctor_set(x_165, 5, x_146);
lean_ctor_set(x_165, 6, x_147);
lean_ctor_set(x_165, 7, x_148);
lean_ctor_set(x_165, 8, x_149);
lean_ctor_set(x_165, 9, x_150);
lean_ctor_set(x_165, 10, x_154);
lean_ctor_set_uint8(x_165, sizeof(void*)*11, x_151);
lean_ctor_set_uint8(x_165, sizeof(void*)*11 + 1, x_152);
lean_ctor_set_uint8(x_165, sizeof(void*)*11 + 2, x_153);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_141);
x_2 = x_140;
x_3 = x_166;
x_4 = x_159;
goto _start;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_168 = lean_ctor_get(x_138, 0);
x_169 = lean_ctor_get(x_138, 1);
x_170 = lean_ctor_get(x_138, 2);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_138);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_156, x_171);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_169);
lean_ctor_set(x_173, 2, x_170);
lean_ctor_set(x_173, 3, x_172);
lean_ctor_set(x_173, 4, x_157);
if (lean_is_scalar(x_155)) {
 x_174 = lean_alloc_ctor(0, 11, 3);
} else {
 x_174 = x_155;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_142);
lean_ctor_set(x_174, 2, x_143);
lean_ctor_set(x_174, 3, x_144);
lean_ctor_set(x_174, 4, x_145);
lean_ctor_set(x_174, 5, x_146);
lean_ctor_set(x_174, 6, x_147);
lean_ctor_set(x_174, 7, x_148);
lean_ctor_set(x_174, 8, x_149);
lean_ctor_set(x_174, 9, x_150);
lean_ctor_set(x_174, 10, x_154);
lean_ctor_set_uint8(x_174, sizeof(void*)*11, x_151);
lean_ctor_set_uint8(x_174, sizeof(void*)*11 + 1, x_152);
lean_ctor_set_uint8(x_174, sizeof(void*)*11 + 2, x_153);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_141);
x_2 = x_140;
x_3 = x_175;
x_4 = x_159;
goto _start;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_3);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_129);
if (x_185 == 0)
{
return x_129;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_129, 0);
x_187 = lean_ctor_get(x_129, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_129);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
case 3:
{
lean_object* x_189; 
lean_dec(x_8);
lean_inc(x_3);
x_189 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
lean_dec(x_3);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_189);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_189, 0);
lean_dec(x_192);
x_193 = lean_box(0);
lean_ctor_set(x_189, 0, x_193);
return x_189;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
lean_dec(x_189);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_197 = lean_ctor_get(x_3, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
lean_dec(x_189);
x_200 = lean_ctor_get(x_190, 0);
lean_inc(x_200);
lean_dec(x_190);
x_201 = lean_ctor_get(x_3, 1);
lean_inc(x_201);
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
x_207 = lean_ctor_get(x_197, 6);
lean_inc(x_207);
x_208 = lean_ctor_get(x_197, 7);
lean_inc(x_208);
x_209 = lean_ctor_get(x_197, 8);
lean_inc(x_209);
x_210 = lean_ctor_get(x_197, 9);
lean_inc(x_210);
x_211 = lean_ctor_get_uint8(x_197, sizeof(void*)*11);
x_212 = lean_ctor_get_uint8(x_197, sizeof(void*)*11 + 1);
x_213 = lean_ctor_get_uint8(x_197, sizeof(void*)*11 + 2);
x_214 = lean_ctor_get(x_197, 10);
lean_inc(x_214);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 lean_ctor_release(x_197, 4);
 lean_ctor_release(x_197, 5);
 lean_ctor_release(x_197, 6);
 lean_ctor_release(x_197, 7);
 lean_ctor_release(x_197, 8);
 lean_ctor_release(x_197, 9);
 lean_ctor_release(x_197, 10);
 x_215 = x_197;
} else {
 lean_dec_ref(x_197);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_198, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_198, 4);
lean_inc(x_217);
x_218 = lean_nat_dec_eq(x_216, x_217);
if (x_218 == 0)
{
lean_dec(x_3);
x_219 = x_199;
goto block_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_239 = l_Lean_Elab_Tactic_throwError___rarg(x_238, x_3, x_199);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_219 = x_240;
goto block_237;
}
else
{
uint8_t x_241; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
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
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_239);
if (x_241 == 0)
{
return x_239;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_239, 0);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_239);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
block_237:
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_198);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_221 = lean_ctor_get(x_198, 4);
lean_dec(x_221);
x_222 = lean_ctor_get(x_198, 3);
lean_dec(x_222);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_nat_add(x_216, x_223);
lean_dec(x_216);
lean_ctor_set(x_198, 3, x_224);
if (lean_is_scalar(x_215)) {
 x_225 = lean_alloc_ctor(0, 11, 3);
} else {
 x_225 = x_215;
}
lean_ctor_set(x_225, 0, x_198);
lean_ctor_set(x_225, 1, x_202);
lean_ctor_set(x_225, 2, x_203);
lean_ctor_set(x_225, 3, x_204);
lean_ctor_set(x_225, 4, x_205);
lean_ctor_set(x_225, 5, x_206);
lean_ctor_set(x_225, 6, x_207);
lean_ctor_set(x_225, 7, x_208);
lean_ctor_set(x_225, 8, x_209);
lean_ctor_set(x_225, 9, x_210);
lean_ctor_set(x_225, 10, x_214);
lean_ctor_set_uint8(x_225, sizeof(void*)*11, x_211);
lean_ctor_set_uint8(x_225, sizeof(void*)*11 + 1, x_212);
lean_ctor_set_uint8(x_225, sizeof(void*)*11 + 2, x_213);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_201);
x_2 = x_200;
x_3 = x_226;
x_4 = x_219;
goto _start;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_198, 0);
x_229 = lean_ctor_get(x_198, 1);
x_230 = lean_ctor_get(x_198, 2);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_198);
x_231 = lean_unsigned_to_nat(1u);
x_232 = lean_nat_add(x_216, x_231);
lean_dec(x_216);
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_228);
lean_ctor_set(x_233, 1, x_229);
lean_ctor_set(x_233, 2, x_230);
lean_ctor_set(x_233, 3, x_232);
lean_ctor_set(x_233, 4, x_217);
if (lean_is_scalar(x_215)) {
 x_234 = lean_alloc_ctor(0, 11, 3);
} else {
 x_234 = x_215;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_202);
lean_ctor_set(x_234, 2, x_203);
lean_ctor_set(x_234, 3, x_204);
lean_ctor_set(x_234, 4, x_205);
lean_ctor_set(x_234, 5, x_206);
lean_ctor_set(x_234, 6, x_207);
lean_ctor_set(x_234, 7, x_208);
lean_ctor_set(x_234, 8, x_209);
lean_ctor_set(x_234, 9, x_210);
lean_ctor_set(x_234, 10, x_214);
lean_ctor_set_uint8(x_234, sizeof(void*)*11, x_211);
lean_ctor_set_uint8(x_234, sizeof(void*)*11 + 1, x_212);
lean_ctor_set_uint8(x_234, sizeof(void*)*11 + 2, x_213);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_201);
x_2 = x_200;
x_3 = x_235;
x_4 = x_219;
goto _start;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_3);
lean_dec(x_1);
x_245 = !lean_is_exclusive(x_189);
if (x_245 == 0)
{
return x_189;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_189, 0);
x_247 = lean_ctor_get(x_189, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_189);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
case 4:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_8, 0);
lean_inc(x_249);
lean_dec(x_8);
lean_inc(x_1);
x_250 = l_Lean_Name_append___main(x_249, x_1);
lean_dec(x_249);
x_251 = l_Lean_Elab_Tactic_getEnv___rarg(x_7);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_250);
x_254 = lean_environment_find(x_252, x_250);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; 
lean_dec(x_250);
lean_inc(x_3);
x_255 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_253);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
lean_dec(x_3);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_255, 0);
lean_dec(x_258);
x_259 = lean_box(0);
lean_ctor_set(x_255, 0, x_259);
return x_255;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
lean_dec(x_255);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; 
x_263 = lean_ctor_get(x_3, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_255, 1);
lean_inc(x_265);
lean_dec(x_255);
x_266 = lean_ctor_get(x_256, 0);
lean_inc(x_266);
lean_dec(x_256);
x_267 = lean_ctor_get(x_3, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_263, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_263, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_263, 4);
lean_inc(x_271);
x_272 = lean_ctor_get(x_263, 5);
lean_inc(x_272);
x_273 = lean_ctor_get(x_263, 6);
lean_inc(x_273);
x_274 = lean_ctor_get(x_263, 7);
lean_inc(x_274);
x_275 = lean_ctor_get(x_263, 8);
lean_inc(x_275);
x_276 = lean_ctor_get(x_263, 9);
lean_inc(x_276);
x_277 = lean_ctor_get_uint8(x_263, sizeof(void*)*11);
x_278 = lean_ctor_get_uint8(x_263, sizeof(void*)*11 + 1);
x_279 = lean_ctor_get_uint8(x_263, sizeof(void*)*11 + 2);
x_280 = lean_ctor_get(x_263, 10);
lean_inc(x_280);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 lean_ctor_release(x_263, 3);
 lean_ctor_release(x_263, 4);
 lean_ctor_release(x_263, 5);
 lean_ctor_release(x_263, 6);
 lean_ctor_release(x_263, 7);
 lean_ctor_release(x_263, 8);
 lean_ctor_release(x_263, 9);
 lean_ctor_release(x_263, 10);
 x_281 = x_263;
} else {
 lean_dec_ref(x_263);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_264, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_264, 4);
lean_inc(x_283);
x_284 = lean_nat_dec_eq(x_282, x_283);
if (x_284 == 0)
{
lean_dec(x_3);
x_285 = x_265;
goto block_303;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_305 = l_Lean_Elab_Tactic_throwError___rarg(x_304, x_3, x_265);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_285 = x_306;
goto block_303;
}
else
{
uint8_t x_307; 
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
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
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_305);
if (x_307 == 0)
{
return x_305;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_305, 0);
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_305);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
block_303:
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_264);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_264, 4);
lean_dec(x_287);
x_288 = lean_ctor_get(x_264, 3);
lean_dec(x_288);
x_289 = lean_unsigned_to_nat(1u);
x_290 = lean_nat_add(x_282, x_289);
lean_dec(x_282);
lean_ctor_set(x_264, 3, x_290);
if (lean_is_scalar(x_281)) {
 x_291 = lean_alloc_ctor(0, 11, 3);
} else {
 x_291 = x_281;
}
lean_ctor_set(x_291, 0, x_264);
lean_ctor_set(x_291, 1, x_268);
lean_ctor_set(x_291, 2, x_269);
lean_ctor_set(x_291, 3, x_270);
lean_ctor_set(x_291, 4, x_271);
lean_ctor_set(x_291, 5, x_272);
lean_ctor_set(x_291, 6, x_273);
lean_ctor_set(x_291, 7, x_274);
lean_ctor_set(x_291, 8, x_275);
lean_ctor_set(x_291, 9, x_276);
lean_ctor_set(x_291, 10, x_280);
lean_ctor_set_uint8(x_291, sizeof(void*)*11, x_277);
lean_ctor_set_uint8(x_291, sizeof(void*)*11 + 1, x_278);
lean_ctor_set_uint8(x_291, sizeof(void*)*11 + 2, x_279);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_267);
x_2 = x_266;
x_3 = x_292;
x_4 = x_285;
goto _start;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_294 = lean_ctor_get(x_264, 0);
x_295 = lean_ctor_get(x_264, 1);
x_296 = lean_ctor_get(x_264, 2);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_264);
x_297 = lean_unsigned_to_nat(1u);
x_298 = lean_nat_add(x_282, x_297);
lean_dec(x_282);
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_294);
lean_ctor_set(x_299, 1, x_295);
lean_ctor_set(x_299, 2, x_296);
lean_ctor_set(x_299, 3, x_298);
lean_ctor_set(x_299, 4, x_283);
if (lean_is_scalar(x_281)) {
 x_300 = lean_alloc_ctor(0, 11, 3);
} else {
 x_300 = x_281;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_268);
lean_ctor_set(x_300, 2, x_269);
lean_ctor_set(x_300, 3, x_270);
lean_ctor_set(x_300, 4, x_271);
lean_ctor_set(x_300, 5, x_272);
lean_ctor_set(x_300, 6, x_273);
lean_ctor_set(x_300, 7, x_274);
lean_ctor_set(x_300, 8, x_275);
lean_ctor_set(x_300, 9, x_276);
lean_ctor_set(x_300, 10, x_280);
lean_ctor_set_uint8(x_300, sizeof(void*)*11, x_277);
lean_ctor_set_uint8(x_300, sizeof(void*)*11 + 1, x_278);
lean_ctor_set_uint8(x_300, sizeof(void*)*11 + 2, x_279);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_267);
x_2 = x_266;
x_3 = x_301;
x_4 = x_285;
goto _start;
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_3);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_255);
if (x_311 == 0)
{
return x_255;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_255, 0);
x_313 = lean_ctor_get(x_255, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_255);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_379; 
lean_dec(x_254);
x_315 = l_Lean_Elab_Tactic_save(x_253);
lean_inc(x_3);
x_379 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_253);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_box(0);
x_384 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_384, 0, x_250);
lean_closure_set(x_384, 1, x_383);
x_385 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_386 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_386, 0, x_384);
lean_closure_set(x_386, 1, x_385);
x_387 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_387, 0, x_386);
lean_inc(x_3);
x_388 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_382, x_387, x_3, x_381);
lean_dec(x_382);
if (lean_obj_tag(x_388) == 0)
{
lean_dec(x_315);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
x_316 = x_389;
goto block_378;
}
}
else
{
lean_object* x_390; 
lean_dec(x_250);
x_390 = lean_ctor_get(x_379, 1);
lean_inc(x_390);
lean_dec(x_379);
x_316 = x_390;
goto block_378;
}
block_378:
{
lean_object* x_317; lean_object* x_318; 
x_317 = l_Lean_Elab_Tactic_restore(x_316, x_315);
lean_dec(x_315);
lean_inc(x_3);
x_318 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; 
lean_dec(x_3);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_318);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_318, 0);
lean_dec(x_321);
x_322 = lean_box(0);
lean_ctor_set(x_318, 0, x_322);
return x_318;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_dec(x_318);
x_324 = lean_box(0);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; uint8_t x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; 
x_326 = lean_ctor_get(x_3, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_318, 1);
lean_inc(x_328);
lean_dec(x_318);
x_329 = lean_ctor_get(x_319, 0);
lean_inc(x_329);
lean_dec(x_319);
x_330 = lean_ctor_get(x_3, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_326, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_326, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_326, 4);
lean_inc(x_334);
x_335 = lean_ctor_get(x_326, 5);
lean_inc(x_335);
x_336 = lean_ctor_get(x_326, 6);
lean_inc(x_336);
x_337 = lean_ctor_get(x_326, 7);
lean_inc(x_337);
x_338 = lean_ctor_get(x_326, 8);
lean_inc(x_338);
x_339 = lean_ctor_get(x_326, 9);
lean_inc(x_339);
x_340 = lean_ctor_get_uint8(x_326, sizeof(void*)*11);
x_341 = lean_ctor_get_uint8(x_326, sizeof(void*)*11 + 1);
x_342 = lean_ctor_get_uint8(x_326, sizeof(void*)*11 + 2);
x_343 = lean_ctor_get(x_326, 10);
lean_inc(x_343);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 lean_ctor_release(x_326, 5);
 lean_ctor_release(x_326, 6);
 lean_ctor_release(x_326, 7);
 lean_ctor_release(x_326, 8);
 lean_ctor_release(x_326, 9);
 lean_ctor_release(x_326, 10);
 x_344 = x_326;
} else {
 lean_dec_ref(x_326);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_327, 3);
lean_inc(x_345);
x_346 = lean_ctor_get(x_327, 4);
lean_inc(x_346);
x_347 = lean_nat_dec_eq(x_345, x_346);
if (x_347 == 0)
{
lean_dec(x_3);
x_348 = x_328;
goto block_366;
}
else
{
lean_object* x_367; lean_object* x_368; 
x_367 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_368 = l_Lean_Elab_Tactic_throwError___rarg(x_367, x_3, x_328);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_348 = x_369;
goto block_366;
}
else
{
uint8_t x_370; 
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
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
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_1);
x_370 = !lean_is_exclusive(x_368);
if (x_370 == 0)
{
return x_368;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_368, 0);
x_372 = lean_ctor_get(x_368, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_368);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
block_366:
{
uint8_t x_349; 
x_349 = !lean_is_exclusive(x_327);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_350 = lean_ctor_get(x_327, 4);
lean_dec(x_350);
x_351 = lean_ctor_get(x_327, 3);
lean_dec(x_351);
x_352 = lean_unsigned_to_nat(1u);
x_353 = lean_nat_add(x_345, x_352);
lean_dec(x_345);
lean_ctor_set(x_327, 3, x_353);
if (lean_is_scalar(x_344)) {
 x_354 = lean_alloc_ctor(0, 11, 3);
} else {
 x_354 = x_344;
}
lean_ctor_set(x_354, 0, x_327);
lean_ctor_set(x_354, 1, x_331);
lean_ctor_set(x_354, 2, x_332);
lean_ctor_set(x_354, 3, x_333);
lean_ctor_set(x_354, 4, x_334);
lean_ctor_set(x_354, 5, x_335);
lean_ctor_set(x_354, 6, x_336);
lean_ctor_set(x_354, 7, x_337);
lean_ctor_set(x_354, 8, x_338);
lean_ctor_set(x_354, 9, x_339);
lean_ctor_set(x_354, 10, x_343);
lean_ctor_set_uint8(x_354, sizeof(void*)*11, x_340);
lean_ctor_set_uint8(x_354, sizeof(void*)*11 + 1, x_341);
lean_ctor_set_uint8(x_354, sizeof(void*)*11 + 2, x_342);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_330);
x_2 = x_329;
x_3 = x_355;
x_4 = x_348;
goto _start;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_357 = lean_ctor_get(x_327, 0);
x_358 = lean_ctor_get(x_327, 1);
x_359 = lean_ctor_get(x_327, 2);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_327);
x_360 = lean_unsigned_to_nat(1u);
x_361 = lean_nat_add(x_345, x_360);
lean_dec(x_345);
x_362 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_362, 0, x_357);
lean_ctor_set(x_362, 1, x_358);
lean_ctor_set(x_362, 2, x_359);
lean_ctor_set(x_362, 3, x_361);
lean_ctor_set(x_362, 4, x_346);
if (lean_is_scalar(x_344)) {
 x_363 = lean_alloc_ctor(0, 11, 3);
} else {
 x_363 = x_344;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_331);
lean_ctor_set(x_363, 2, x_332);
lean_ctor_set(x_363, 3, x_333);
lean_ctor_set(x_363, 4, x_334);
lean_ctor_set(x_363, 5, x_335);
lean_ctor_set(x_363, 6, x_336);
lean_ctor_set(x_363, 7, x_337);
lean_ctor_set(x_363, 8, x_338);
lean_ctor_set(x_363, 9, x_339);
lean_ctor_set(x_363, 10, x_343);
lean_ctor_set_uint8(x_363, sizeof(void*)*11, x_340);
lean_ctor_set_uint8(x_363, sizeof(void*)*11 + 1, x_341);
lean_ctor_set_uint8(x_363, sizeof(void*)*11 + 2, x_342);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_330);
x_2 = x_329;
x_3 = x_364;
x_4 = x_348;
goto _start;
}
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_3);
lean_dec(x_1);
x_374 = !lean_is_exclusive(x_318);
if (x_374 == 0)
{
return x_318;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_318, 0);
x_376 = lean_ctor_get(x_318, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_318);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
}
}
case 5:
{
lean_object* x_391; 
lean_dec(x_8);
lean_inc(x_3);
x_391 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
uint8_t x_393; 
lean_dec(x_3);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_391);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_391, 0);
lean_dec(x_394);
x_395 = lean_box(0);
lean_ctor_set(x_391, 0, x_395);
return x_391;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_391, 1);
lean_inc(x_396);
lean_dec(x_391);
x_397 = lean_box(0);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
x_399 = lean_ctor_get(x_3, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_391, 1);
lean_inc(x_401);
lean_dec(x_391);
x_402 = lean_ctor_get(x_392, 0);
lean_inc(x_402);
lean_dec(x_392);
x_403 = lean_ctor_get(x_3, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_399, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_399, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_399, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_399, 4);
lean_inc(x_407);
x_408 = lean_ctor_get(x_399, 5);
lean_inc(x_408);
x_409 = lean_ctor_get(x_399, 6);
lean_inc(x_409);
x_410 = lean_ctor_get(x_399, 7);
lean_inc(x_410);
x_411 = lean_ctor_get(x_399, 8);
lean_inc(x_411);
x_412 = lean_ctor_get(x_399, 9);
lean_inc(x_412);
x_413 = lean_ctor_get_uint8(x_399, sizeof(void*)*11);
x_414 = lean_ctor_get_uint8(x_399, sizeof(void*)*11 + 1);
x_415 = lean_ctor_get_uint8(x_399, sizeof(void*)*11 + 2);
x_416 = lean_ctor_get(x_399, 10);
lean_inc(x_416);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 lean_ctor_release(x_399, 3);
 lean_ctor_release(x_399, 4);
 lean_ctor_release(x_399, 5);
 lean_ctor_release(x_399, 6);
 lean_ctor_release(x_399, 7);
 lean_ctor_release(x_399, 8);
 lean_ctor_release(x_399, 9);
 lean_ctor_release(x_399, 10);
 x_417 = x_399;
} else {
 lean_dec_ref(x_399);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_400, 3);
lean_inc(x_418);
x_419 = lean_ctor_get(x_400, 4);
lean_inc(x_419);
x_420 = lean_nat_dec_eq(x_418, x_419);
if (x_420 == 0)
{
lean_dec(x_3);
x_421 = x_401;
goto block_439;
}
else
{
lean_object* x_440; lean_object* x_441; 
x_440 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_441 = l_Lean_Elab_Tactic_throwError___rarg(x_440, x_3, x_401);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; 
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec(x_441);
x_421 = x_442;
goto block_439;
}
else
{
uint8_t x_443; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
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
lean_dec(x_402);
lean_dec(x_400);
lean_dec(x_1);
x_443 = !lean_is_exclusive(x_441);
if (x_443 == 0)
{
return x_441;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_441, 0);
x_445 = lean_ctor_get(x_441, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_441);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
block_439:
{
uint8_t x_422; 
x_422 = !lean_is_exclusive(x_400);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_423 = lean_ctor_get(x_400, 4);
lean_dec(x_423);
x_424 = lean_ctor_get(x_400, 3);
lean_dec(x_424);
x_425 = lean_unsigned_to_nat(1u);
x_426 = lean_nat_add(x_418, x_425);
lean_dec(x_418);
lean_ctor_set(x_400, 3, x_426);
if (lean_is_scalar(x_417)) {
 x_427 = lean_alloc_ctor(0, 11, 3);
} else {
 x_427 = x_417;
}
lean_ctor_set(x_427, 0, x_400);
lean_ctor_set(x_427, 1, x_404);
lean_ctor_set(x_427, 2, x_405);
lean_ctor_set(x_427, 3, x_406);
lean_ctor_set(x_427, 4, x_407);
lean_ctor_set(x_427, 5, x_408);
lean_ctor_set(x_427, 6, x_409);
lean_ctor_set(x_427, 7, x_410);
lean_ctor_set(x_427, 8, x_411);
lean_ctor_set(x_427, 9, x_412);
lean_ctor_set(x_427, 10, x_416);
lean_ctor_set_uint8(x_427, sizeof(void*)*11, x_413);
lean_ctor_set_uint8(x_427, sizeof(void*)*11 + 1, x_414);
lean_ctor_set_uint8(x_427, sizeof(void*)*11 + 2, x_415);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_403);
x_2 = x_402;
x_3 = x_428;
x_4 = x_421;
goto _start;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_430 = lean_ctor_get(x_400, 0);
x_431 = lean_ctor_get(x_400, 1);
x_432 = lean_ctor_get(x_400, 2);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_400);
x_433 = lean_unsigned_to_nat(1u);
x_434 = lean_nat_add(x_418, x_433);
lean_dec(x_418);
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_432);
lean_ctor_set(x_435, 3, x_434);
lean_ctor_set(x_435, 4, x_419);
if (lean_is_scalar(x_417)) {
 x_436 = lean_alloc_ctor(0, 11, 3);
} else {
 x_436 = x_417;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_404);
lean_ctor_set(x_436, 2, x_405);
lean_ctor_set(x_436, 3, x_406);
lean_ctor_set(x_436, 4, x_407);
lean_ctor_set(x_436, 5, x_408);
lean_ctor_set(x_436, 6, x_409);
lean_ctor_set(x_436, 7, x_410);
lean_ctor_set(x_436, 8, x_411);
lean_ctor_set(x_436, 9, x_412);
lean_ctor_set(x_436, 10, x_416);
lean_ctor_set_uint8(x_436, sizeof(void*)*11, x_413);
lean_ctor_set_uint8(x_436, sizeof(void*)*11 + 1, x_414);
lean_ctor_set_uint8(x_436, sizeof(void*)*11 + 2, x_415);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_403);
x_2 = x_402;
x_3 = x_437;
x_4 = x_421;
goto _start;
}
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_3);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_391);
if (x_447 == 0)
{
return x_391;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_391, 0);
x_449 = lean_ctor_get(x_391, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_391);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
case 6:
{
lean_object* x_451; 
lean_dec(x_8);
lean_inc(x_3);
x_451 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
if (lean_obj_tag(x_452) == 0)
{
uint8_t x_453; 
lean_dec(x_3);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_451);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; 
x_454 = lean_ctor_get(x_451, 0);
lean_dec(x_454);
x_455 = lean_box(0);
lean_ctor_set(x_451, 0, x_455);
return x_451;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
lean_dec(x_451);
x_457 = lean_box(0);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; uint8_t x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; 
x_459 = lean_ctor_get(x_3, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_451, 1);
lean_inc(x_461);
lean_dec(x_451);
x_462 = lean_ctor_get(x_452, 0);
lean_inc(x_462);
lean_dec(x_452);
x_463 = lean_ctor_get(x_3, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_459, 2);
lean_inc(x_465);
x_466 = lean_ctor_get(x_459, 3);
lean_inc(x_466);
x_467 = lean_ctor_get(x_459, 4);
lean_inc(x_467);
x_468 = lean_ctor_get(x_459, 5);
lean_inc(x_468);
x_469 = lean_ctor_get(x_459, 6);
lean_inc(x_469);
x_470 = lean_ctor_get(x_459, 7);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 8);
lean_inc(x_471);
x_472 = lean_ctor_get(x_459, 9);
lean_inc(x_472);
x_473 = lean_ctor_get_uint8(x_459, sizeof(void*)*11);
x_474 = lean_ctor_get_uint8(x_459, sizeof(void*)*11 + 1);
x_475 = lean_ctor_get_uint8(x_459, sizeof(void*)*11 + 2);
x_476 = lean_ctor_get(x_459, 10);
lean_inc(x_476);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 lean_ctor_release(x_459, 4);
 lean_ctor_release(x_459, 5);
 lean_ctor_release(x_459, 6);
 lean_ctor_release(x_459, 7);
 lean_ctor_release(x_459, 8);
 lean_ctor_release(x_459, 9);
 lean_ctor_release(x_459, 10);
 x_477 = x_459;
} else {
 lean_dec_ref(x_459);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_460, 3);
lean_inc(x_478);
x_479 = lean_ctor_get(x_460, 4);
lean_inc(x_479);
x_480 = lean_nat_dec_eq(x_478, x_479);
if (x_480 == 0)
{
lean_dec(x_3);
x_481 = x_461;
goto block_499;
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_501 = l_Lean_Elab_Tactic_throwError___rarg(x_500, x_3, x_461);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
lean_dec(x_501);
x_481 = x_502;
goto block_499;
}
else
{
uint8_t x_503; 
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
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
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_1);
x_503 = !lean_is_exclusive(x_501);
if (x_503 == 0)
{
return x_501;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_501, 0);
x_505 = lean_ctor_get(x_501, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_501);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
block_499:
{
uint8_t x_482; 
x_482 = !lean_is_exclusive(x_460);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_483 = lean_ctor_get(x_460, 4);
lean_dec(x_483);
x_484 = lean_ctor_get(x_460, 3);
lean_dec(x_484);
x_485 = lean_unsigned_to_nat(1u);
x_486 = lean_nat_add(x_478, x_485);
lean_dec(x_478);
lean_ctor_set(x_460, 3, x_486);
if (lean_is_scalar(x_477)) {
 x_487 = lean_alloc_ctor(0, 11, 3);
} else {
 x_487 = x_477;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_464);
lean_ctor_set(x_487, 2, x_465);
lean_ctor_set(x_487, 3, x_466);
lean_ctor_set(x_487, 4, x_467);
lean_ctor_set(x_487, 5, x_468);
lean_ctor_set(x_487, 6, x_469);
lean_ctor_set(x_487, 7, x_470);
lean_ctor_set(x_487, 8, x_471);
lean_ctor_set(x_487, 9, x_472);
lean_ctor_set(x_487, 10, x_476);
lean_ctor_set_uint8(x_487, sizeof(void*)*11, x_473);
lean_ctor_set_uint8(x_487, sizeof(void*)*11 + 1, x_474);
lean_ctor_set_uint8(x_487, sizeof(void*)*11 + 2, x_475);
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_463);
x_2 = x_462;
x_3 = x_488;
x_4 = x_481;
goto _start;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_490 = lean_ctor_get(x_460, 0);
x_491 = lean_ctor_get(x_460, 1);
x_492 = lean_ctor_get(x_460, 2);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_460);
x_493 = lean_unsigned_to_nat(1u);
x_494 = lean_nat_add(x_478, x_493);
lean_dec(x_478);
x_495 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_495, 0, x_490);
lean_ctor_set(x_495, 1, x_491);
lean_ctor_set(x_495, 2, x_492);
lean_ctor_set(x_495, 3, x_494);
lean_ctor_set(x_495, 4, x_479);
if (lean_is_scalar(x_477)) {
 x_496 = lean_alloc_ctor(0, 11, 3);
} else {
 x_496 = x_477;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_464);
lean_ctor_set(x_496, 2, x_465);
lean_ctor_set(x_496, 3, x_466);
lean_ctor_set(x_496, 4, x_467);
lean_ctor_set(x_496, 5, x_468);
lean_ctor_set(x_496, 6, x_469);
lean_ctor_set(x_496, 7, x_470);
lean_ctor_set(x_496, 8, x_471);
lean_ctor_set(x_496, 9, x_472);
lean_ctor_set(x_496, 10, x_476);
lean_ctor_set_uint8(x_496, sizeof(void*)*11, x_473);
lean_ctor_set_uint8(x_496, sizeof(void*)*11 + 1, x_474);
lean_ctor_set_uint8(x_496, sizeof(void*)*11 + 2, x_475);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_463);
x_2 = x_462;
x_3 = x_497;
x_4 = x_481;
goto _start;
}
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_3);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_451);
if (x_507 == 0)
{
return x_451;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_451, 0);
x_509 = lean_ctor_get(x_451, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_451);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
case 7:
{
lean_object* x_511; 
lean_dec(x_8);
lean_inc(x_3);
x_511 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
if (lean_obj_tag(x_512) == 0)
{
uint8_t x_513; 
lean_dec(x_3);
lean_dec(x_1);
x_513 = !lean_is_exclusive(x_511);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; 
x_514 = lean_ctor_get(x_511, 0);
lean_dec(x_514);
x_515 = lean_box(0);
lean_ctor_set(x_511, 0, x_515);
return x_511;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_511, 1);
lean_inc(x_516);
lean_dec(x_511);
x_517 = lean_box(0);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; uint8_t x_534; uint8_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
x_519 = lean_ctor_get(x_3, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_511, 1);
lean_inc(x_521);
lean_dec(x_511);
x_522 = lean_ctor_get(x_512, 0);
lean_inc(x_522);
lean_dec(x_512);
x_523 = lean_ctor_get(x_3, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_519, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_519, 2);
lean_inc(x_525);
x_526 = lean_ctor_get(x_519, 3);
lean_inc(x_526);
x_527 = lean_ctor_get(x_519, 4);
lean_inc(x_527);
x_528 = lean_ctor_get(x_519, 5);
lean_inc(x_528);
x_529 = lean_ctor_get(x_519, 6);
lean_inc(x_529);
x_530 = lean_ctor_get(x_519, 7);
lean_inc(x_530);
x_531 = lean_ctor_get(x_519, 8);
lean_inc(x_531);
x_532 = lean_ctor_get(x_519, 9);
lean_inc(x_532);
x_533 = lean_ctor_get_uint8(x_519, sizeof(void*)*11);
x_534 = lean_ctor_get_uint8(x_519, sizeof(void*)*11 + 1);
x_535 = lean_ctor_get_uint8(x_519, sizeof(void*)*11 + 2);
x_536 = lean_ctor_get(x_519, 10);
lean_inc(x_536);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 lean_ctor_release(x_519, 2);
 lean_ctor_release(x_519, 3);
 lean_ctor_release(x_519, 4);
 lean_ctor_release(x_519, 5);
 lean_ctor_release(x_519, 6);
 lean_ctor_release(x_519, 7);
 lean_ctor_release(x_519, 8);
 lean_ctor_release(x_519, 9);
 lean_ctor_release(x_519, 10);
 x_537 = x_519;
} else {
 lean_dec_ref(x_519);
 x_537 = lean_box(0);
}
x_538 = lean_ctor_get(x_520, 3);
lean_inc(x_538);
x_539 = lean_ctor_get(x_520, 4);
lean_inc(x_539);
x_540 = lean_nat_dec_eq(x_538, x_539);
if (x_540 == 0)
{
lean_dec(x_3);
x_541 = x_521;
goto block_559;
}
else
{
lean_object* x_560; lean_object* x_561; 
x_560 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_561 = l_Lean_Elab_Tactic_throwError___rarg(x_560, x_3, x_521);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; 
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
lean_dec(x_561);
x_541 = x_562;
goto block_559;
}
else
{
uint8_t x_563; 
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
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
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_561);
if (x_563 == 0)
{
return x_561;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_561, 0);
x_565 = lean_ctor_get(x_561, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_561);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
block_559:
{
uint8_t x_542; 
x_542 = !lean_is_exclusive(x_520);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_543 = lean_ctor_get(x_520, 4);
lean_dec(x_543);
x_544 = lean_ctor_get(x_520, 3);
lean_dec(x_544);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_538, x_545);
lean_dec(x_538);
lean_ctor_set(x_520, 3, x_546);
if (lean_is_scalar(x_537)) {
 x_547 = lean_alloc_ctor(0, 11, 3);
} else {
 x_547 = x_537;
}
lean_ctor_set(x_547, 0, x_520);
lean_ctor_set(x_547, 1, x_524);
lean_ctor_set(x_547, 2, x_525);
lean_ctor_set(x_547, 3, x_526);
lean_ctor_set(x_547, 4, x_527);
lean_ctor_set(x_547, 5, x_528);
lean_ctor_set(x_547, 6, x_529);
lean_ctor_set(x_547, 7, x_530);
lean_ctor_set(x_547, 8, x_531);
lean_ctor_set(x_547, 9, x_532);
lean_ctor_set(x_547, 10, x_536);
lean_ctor_set_uint8(x_547, sizeof(void*)*11, x_533);
lean_ctor_set_uint8(x_547, sizeof(void*)*11 + 1, x_534);
lean_ctor_set_uint8(x_547, sizeof(void*)*11 + 2, x_535);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_523);
x_2 = x_522;
x_3 = x_548;
x_4 = x_541;
goto _start;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_550 = lean_ctor_get(x_520, 0);
x_551 = lean_ctor_get(x_520, 1);
x_552 = lean_ctor_get(x_520, 2);
lean_inc(x_552);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_520);
x_553 = lean_unsigned_to_nat(1u);
x_554 = lean_nat_add(x_538, x_553);
lean_dec(x_538);
x_555 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_555, 0, x_550);
lean_ctor_set(x_555, 1, x_551);
lean_ctor_set(x_555, 2, x_552);
lean_ctor_set(x_555, 3, x_554);
lean_ctor_set(x_555, 4, x_539);
if (lean_is_scalar(x_537)) {
 x_556 = lean_alloc_ctor(0, 11, 3);
} else {
 x_556 = x_537;
}
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_524);
lean_ctor_set(x_556, 2, x_525);
lean_ctor_set(x_556, 3, x_526);
lean_ctor_set(x_556, 4, x_527);
lean_ctor_set(x_556, 5, x_528);
lean_ctor_set(x_556, 6, x_529);
lean_ctor_set(x_556, 7, x_530);
lean_ctor_set(x_556, 8, x_531);
lean_ctor_set(x_556, 9, x_532);
lean_ctor_set(x_556, 10, x_536);
lean_ctor_set_uint8(x_556, sizeof(void*)*11, x_533);
lean_ctor_set_uint8(x_556, sizeof(void*)*11 + 1, x_534);
lean_ctor_set_uint8(x_556, sizeof(void*)*11 + 2, x_535);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_523);
x_2 = x_522;
x_3 = x_557;
x_4 = x_541;
goto _start;
}
}
}
}
else
{
uint8_t x_567; 
lean_dec(x_3);
lean_dec(x_1);
x_567 = !lean_is_exclusive(x_511);
if (x_567 == 0)
{
return x_511;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_568 = lean_ctor_get(x_511, 0);
x_569 = lean_ctor_get(x_511, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_511);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
return x_570;
}
}
}
case 8:
{
lean_object* x_571; 
lean_dec(x_8);
lean_inc(x_3);
x_571 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
if (lean_obj_tag(x_572) == 0)
{
uint8_t x_573; 
lean_dec(x_3);
lean_dec(x_1);
x_573 = !lean_is_exclusive(x_571);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_571, 0);
lean_dec(x_574);
x_575 = lean_box(0);
lean_ctor_set(x_571, 0, x_575);
return x_571;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
lean_dec(x_571);
x_577 = lean_box(0);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; uint8_t x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; 
x_579 = lean_ctor_get(x_3, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_571, 1);
lean_inc(x_581);
lean_dec(x_571);
x_582 = lean_ctor_get(x_572, 0);
lean_inc(x_582);
lean_dec(x_572);
x_583 = lean_ctor_get(x_3, 1);
lean_inc(x_583);
x_584 = lean_ctor_get(x_579, 1);
lean_inc(x_584);
x_585 = lean_ctor_get(x_579, 2);
lean_inc(x_585);
x_586 = lean_ctor_get(x_579, 3);
lean_inc(x_586);
x_587 = lean_ctor_get(x_579, 4);
lean_inc(x_587);
x_588 = lean_ctor_get(x_579, 5);
lean_inc(x_588);
x_589 = lean_ctor_get(x_579, 6);
lean_inc(x_589);
x_590 = lean_ctor_get(x_579, 7);
lean_inc(x_590);
x_591 = lean_ctor_get(x_579, 8);
lean_inc(x_591);
x_592 = lean_ctor_get(x_579, 9);
lean_inc(x_592);
x_593 = lean_ctor_get_uint8(x_579, sizeof(void*)*11);
x_594 = lean_ctor_get_uint8(x_579, sizeof(void*)*11 + 1);
x_595 = lean_ctor_get_uint8(x_579, sizeof(void*)*11 + 2);
x_596 = lean_ctor_get(x_579, 10);
lean_inc(x_596);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 lean_ctor_release(x_579, 2);
 lean_ctor_release(x_579, 3);
 lean_ctor_release(x_579, 4);
 lean_ctor_release(x_579, 5);
 lean_ctor_release(x_579, 6);
 lean_ctor_release(x_579, 7);
 lean_ctor_release(x_579, 8);
 lean_ctor_release(x_579, 9);
 lean_ctor_release(x_579, 10);
 x_597 = x_579;
} else {
 lean_dec_ref(x_579);
 x_597 = lean_box(0);
}
x_598 = lean_ctor_get(x_580, 3);
lean_inc(x_598);
x_599 = lean_ctor_get(x_580, 4);
lean_inc(x_599);
x_600 = lean_nat_dec_eq(x_598, x_599);
if (x_600 == 0)
{
lean_dec(x_3);
x_601 = x_581;
goto block_619;
}
else
{
lean_object* x_620; lean_object* x_621; 
x_620 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_621 = l_Lean_Elab_Tactic_throwError___rarg(x_620, x_3, x_581);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; 
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_601 = x_622;
goto block_619;
}
else
{
uint8_t x_623; 
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
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
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_1);
x_623 = !lean_is_exclusive(x_621);
if (x_623 == 0)
{
return x_621;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_621, 0);
x_625 = lean_ctor_get(x_621, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_621);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
block_619:
{
uint8_t x_602; 
x_602 = !lean_is_exclusive(x_580);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_603 = lean_ctor_get(x_580, 4);
lean_dec(x_603);
x_604 = lean_ctor_get(x_580, 3);
lean_dec(x_604);
x_605 = lean_unsigned_to_nat(1u);
x_606 = lean_nat_add(x_598, x_605);
lean_dec(x_598);
lean_ctor_set(x_580, 3, x_606);
if (lean_is_scalar(x_597)) {
 x_607 = lean_alloc_ctor(0, 11, 3);
} else {
 x_607 = x_597;
}
lean_ctor_set(x_607, 0, x_580);
lean_ctor_set(x_607, 1, x_584);
lean_ctor_set(x_607, 2, x_585);
lean_ctor_set(x_607, 3, x_586);
lean_ctor_set(x_607, 4, x_587);
lean_ctor_set(x_607, 5, x_588);
lean_ctor_set(x_607, 6, x_589);
lean_ctor_set(x_607, 7, x_590);
lean_ctor_set(x_607, 8, x_591);
lean_ctor_set(x_607, 9, x_592);
lean_ctor_set(x_607, 10, x_596);
lean_ctor_set_uint8(x_607, sizeof(void*)*11, x_593);
lean_ctor_set_uint8(x_607, sizeof(void*)*11 + 1, x_594);
lean_ctor_set_uint8(x_607, sizeof(void*)*11 + 2, x_595);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_583);
x_2 = x_582;
x_3 = x_608;
x_4 = x_601;
goto _start;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_610 = lean_ctor_get(x_580, 0);
x_611 = lean_ctor_get(x_580, 1);
x_612 = lean_ctor_get(x_580, 2);
lean_inc(x_612);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_580);
x_613 = lean_unsigned_to_nat(1u);
x_614 = lean_nat_add(x_598, x_613);
lean_dec(x_598);
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_610);
lean_ctor_set(x_615, 1, x_611);
lean_ctor_set(x_615, 2, x_612);
lean_ctor_set(x_615, 3, x_614);
lean_ctor_set(x_615, 4, x_599);
if (lean_is_scalar(x_597)) {
 x_616 = lean_alloc_ctor(0, 11, 3);
} else {
 x_616 = x_597;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_584);
lean_ctor_set(x_616, 2, x_585);
lean_ctor_set(x_616, 3, x_586);
lean_ctor_set(x_616, 4, x_587);
lean_ctor_set(x_616, 5, x_588);
lean_ctor_set(x_616, 6, x_589);
lean_ctor_set(x_616, 7, x_590);
lean_ctor_set(x_616, 8, x_591);
lean_ctor_set(x_616, 9, x_592);
lean_ctor_set(x_616, 10, x_596);
lean_ctor_set_uint8(x_616, sizeof(void*)*11, x_593);
lean_ctor_set_uint8(x_616, sizeof(void*)*11 + 1, x_594);
lean_ctor_set_uint8(x_616, sizeof(void*)*11 + 2, x_595);
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_583);
x_2 = x_582;
x_3 = x_617;
x_4 = x_601;
goto _start;
}
}
}
}
else
{
uint8_t x_627; 
lean_dec(x_3);
lean_dec(x_1);
x_627 = !lean_is_exclusive(x_571);
if (x_627 == 0)
{
return x_571;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_571, 0);
x_629 = lean_ctor_get(x_571, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_571);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
case 9:
{
lean_object* x_631; 
lean_dec(x_8);
lean_inc(x_3);
x_631 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
if (lean_obj_tag(x_632) == 0)
{
uint8_t x_633; 
lean_dec(x_3);
lean_dec(x_1);
x_633 = !lean_is_exclusive(x_631);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; 
x_634 = lean_ctor_get(x_631, 0);
lean_dec(x_634);
x_635 = lean_box(0);
lean_ctor_set(x_631, 0, x_635);
return x_631;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_631, 1);
lean_inc(x_636);
lean_dec(x_631);
x_637 = lean_box(0);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; uint8_t x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; lean_object* x_661; 
x_639 = lean_ctor_get(x_3, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_631, 1);
lean_inc(x_641);
lean_dec(x_631);
x_642 = lean_ctor_get(x_632, 0);
lean_inc(x_642);
lean_dec(x_632);
x_643 = lean_ctor_get(x_3, 1);
lean_inc(x_643);
x_644 = lean_ctor_get(x_639, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_639, 2);
lean_inc(x_645);
x_646 = lean_ctor_get(x_639, 3);
lean_inc(x_646);
x_647 = lean_ctor_get(x_639, 4);
lean_inc(x_647);
x_648 = lean_ctor_get(x_639, 5);
lean_inc(x_648);
x_649 = lean_ctor_get(x_639, 6);
lean_inc(x_649);
x_650 = lean_ctor_get(x_639, 7);
lean_inc(x_650);
x_651 = lean_ctor_get(x_639, 8);
lean_inc(x_651);
x_652 = lean_ctor_get(x_639, 9);
lean_inc(x_652);
x_653 = lean_ctor_get_uint8(x_639, sizeof(void*)*11);
x_654 = lean_ctor_get_uint8(x_639, sizeof(void*)*11 + 1);
x_655 = lean_ctor_get_uint8(x_639, sizeof(void*)*11 + 2);
x_656 = lean_ctor_get(x_639, 10);
lean_inc(x_656);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 lean_ctor_release(x_639, 2);
 lean_ctor_release(x_639, 3);
 lean_ctor_release(x_639, 4);
 lean_ctor_release(x_639, 5);
 lean_ctor_release(x_639, 6);
 lean_ctor_release(x_639, 7);
 lean_ctor_release(x_639, 8);
 lean_ctor_release(x_639, 9);
 lean_ctor_release(x_639, 10);
 x_657 = x_639;
} else {
 lean_dec_ref(x_639);
 x_657 = lean_box(0);
}
x_658 = lean_ctor_get(x_640, 3);
lean_inc(x_658);
x_659 = lean_ctor_get(x_640, 4);
lean_inc(x_659);
x_660 = lean_nat_dec_eq(x_658, x_659);
if (x_660 == 0)
{
lean_dec(x_3);
x_661 = x_641;
goto block_679;
}
else
{
lean_object* x_680; lean_object* x_681; 
x_680 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_681 = l_Lean_Elab_Tactic_throwError___rarg(x_680, x_3, x_641);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; 
x_682 = lean_ctor_get(x_681, 1);
lean_inc(x_682);
lean_dec(x_681);
x_661 = x_682;
goto block_679;
}
else
{
uint8_t x_683; 
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
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
lean_dec(x_642);
lean_dec(x_640);
lean_dec(x_1);
x_683 = !lean_is_exclusive(x_681);
if (x_683 == 0)
{
return x_681;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = lean_ctor_get(x_681, 0);
x_685 = lean_ctor_get(x_681, 1);
lean_inc(x_685);
lean_inc(x_684);
lean_dec(x_681);
x_686 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_686, 0, x_684);
lean_ctor_set(x_686, 1, x_685);
return x_686;
}
}
}
block_679:
{
uint8_t x_662; 
x_662 = !lean_is_exclusive(x_640);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_663 = lean_ctor_get(x_640, 4);
lean_dec(x_663);
x_664 = lean_ctor_get(x_640, 3);
lean_dec(x_664);
x_665 = lean_unsigned_to_nat(1u);
x_666 = lean_nat_add(x_658, x_665);
lean_dec(x_658);
lean_ctor_set(x_640, 3, x_666);
if (lean_is_scalar(x_657)) {
 x_667 = lean_alloc_ctor(0, 11, 3);
} else {
 x_667 = x_657;
}
lean_ctor_set(x_667, 0, x_640);
lean_ctor_set(x_667, 1, x_644);
lean_ctor_set(x_667, 2, x_645);
lean_ctor_set(x_667, 3, x_646);
lean_ctor_set(x_667, 4, x_647);
lean_ctor_set(x_667, 5, x_648);
lean_ctor_set(x_667, 6, x_649);
lean_ctor_set(x_667, 7, x_650);
lean_ctor_set(x_667, 8, x_651);
lean_ctor_set(x_667, 9, x_652);
lean_ctor_set(x_667, 10, x_656);
lean_ctor_set_uint8(x_667, sizeof(void*)*11, x_653);
lean_ctor_set_uint8(x_667, sizeof(void*)*11 + 1, x_654);
lean_ctor_set_uint8(x_667, sizeof(void*)*11 + 2, x_655);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_643);
x_2 = x_642;
x_3 = x_668;
x_4 = x_661;
goto _start;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_670 = lean_ctor_get(x_640, 0);
x_671 = lean_ctor_get(x_640, 1);
x_672 = lean_ctor_get(x_640, 2);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_640);
x_673 = lean_unsigned_to_nat(1u);
x_674 = lean_nat_add(x_658, x_673);
lean_dec(x_658);
x_675 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_675, 0, x_670);
lean_ctor_set(x_675, 1, x_671);
lean_ctor_set(x_675, 2, x_672);
lean_ctor_set(x_675, 3, x_674);
lean_ctor_set(x_675, 4, x_659);
if (lean_is_scalar(x_657)) {
 x_676 = lean_alloc_ctor(0, 11, 3);
} else {
 x_676 = x_657;
}
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_644);
lean_ctor_set(x_676, 2, x_645);
lean_ctor_set(x_676, 3, x_646);
lean_ctor_set(x_676, 4, x_647);
lean_ctor_set(x_676, 5, x_648);
lean_ctor_set(x_676, 6, x_649);
lean_ctor_set(x_676, 7, x_650);
lean_ctor_set(x_676, 8, x_651);
lean_ctor_set(x_676, 9, x_652);
lean_ctor_set(x_676, 10, x_656);
lean_ctor_set_uint8(x_676, sizeof(void*)*11, x_653);
lean_ctor_set_uint8(x_676, sizeof(void*)*11 + 1, x_654);
lean_ctor_set_uint8(x_676, sizeof(void*)*11 + 2, x_655);
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_643);
x_2 = x_642;
x_3 = x_677;
x_4 = x_661;
goto _start;
}
}
}
}
else
{
uint8_t x_687; 
lean_dec(x_3);
lean_dec(x_1);
x_687 = !lean_is_exclusive(x_631);
if (x_687 == 0)
{
return x_631;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_631, 0);
x_689 = lean_ctor_get(x_631, 1);
lean_inc(x_689);
lean_inc(x_688);
lean_dec(x_631);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set(x_690, 1, x_689);
return x_690;
}
}
}
case 10:
{
lean_object* x_691; 
lean_dec(x_8);
lean_inc(x_3);
x_691 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
if (lean_obj_tag(x_692) == 0)
{
uint8_t x_693; 
lean_dec(x_3);
lean_dec(x_1);
x_693 = !lean_is_exclusive(x_691);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_691, 0);
lean_dec(x_694);
x_695 = lean_box(0);
lean_ctor_set(x_691, 0, x_695);
return x_691;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_691, 1);
lean_inc(x_696);
lean_dec(x_691);
x_697 = lean_box(0);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; uint8_t x_714; uint8_t x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; lean_object* x_721; 
x_699 = lean_ctor_get(x_3, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_691, 1);
lean_inc(x_701);
lean_dec(x_691);
x_702 = lean_ctor_get(x_692, 0);
lean_inc(x_702);
lean_dec(x_692);
x_703 = lean_ctor_get(x_3, 1);
lean_inc(x_703);
x_704 = lean_ctor_get(x_699, 1);
lean_inc(x_704);
x_705 = lean_ctor_get(x_699, 2);
lean_inc(x_705);
x_706 = lean_ctor_get(x_699, 3);
lean_inc(x_706);
x_707 = lean_ctor_get(x_699, 4);
lean_inc(x_707);
x_708 = lean_ctor_get(x_699, 5);
lean_inc(x_708);
x_709 = lean_ctor_get(x_699, 6);
lean_inc(x_709);
x_710 = lean_ctor_get(x_699, 7);
lean_inc(x_710);
x_711 = lean_ctor_get(x_699, 8);
lean_inc(x_711);
x_712 = lean_ctor_get(x_699, 9);
lean_inc(x_712);
x_713 = lean_ctor_get_uint8(x_699, sizeof(void*)*11);
x_714 = lean_ctor_get_uint8(x_699, sizeof(void*)*11 + 1);
x_715 = lean_ctor_get_uint8(x_699, sizeof(void*)*11 + 2);
x_716 = lean_ctor_get(x_699, 10);
lean_inc(x_716);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 lean_ctor_release(x_699, 2);
 lean_ctor_release(x_699, 3);
 lean_ctor_release(x_699, 4);
 lean_ctor_release(x_699, 5);
 lean_ctor_release(x_699, 6);
 lean_ctor_release(x_699, 7);
 lean_ctor_release(x_699, 8);
 lean_ctor_release(x_699, 9);
 lean_ctor_release(x_699, 10);
 x_717 = x_699;
} else {
 lean_dec_ref(x_699);
 x_717 = lean_box(0);
}
x_718 = lean_ctor_get(x_700, 3);
lean_inc(x_718);
x_719 = lean_ctor_get(x_700, 4);
lean_inc(x_719);
x_720 = lean_nat_dec_eq(x_718, x_719);
if (x_720 == 0)
{
lean_dec(x_3);
x_721 = x_701;
goto block_739;
}
else
{
lean_object* x_740; lean_object* x_741; 
x_740 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_741 = l_Lean_Elab_Tactic_throwError___rarg(x_740, x_3, x_701);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; 
x_742 = lean_ctor_get(x_741, 1);
lean_inc(x_742);
lean_dec(x_741);
x_721 = x_742;
goto block_739;
}
else
{
uint8_t x_743; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_717);
lean_dec(x_716);
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
lean_dec(x_702);
lean_dec(x_700);
lean_dec(x_1);
x_743 = !lean_is_exclusive(x_741);
if (x_743 == 0)
{
return x_741;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_741, 0);
x_745 = lean_ctor_get(x_741, 1);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_741);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
return x_746;
}
}
}
block_739:
{
uint8_t x_722; 
x_722 = !lean_is_exclusive(x_700);
if (x_722 == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_723 = lean_ctor_get(x_700, 4);
lean_dec(x_723);
x_724 = lean_ctor_get(x_700, 3);
lean_dec(x_724);
x_725 = lean_unsigned_to_nat(1u);
x_726 = lean_nat_add(x_718, x_725);
lean_dec(x_718);
lean_ctor_set(x_700, 3, x_726);
if (lean_is_scalar(x_717)) {
 x_727 = lean_alloc_ctor(0, 11, 3);
} else {
 x_727 = x_717;
}
lean_ctor_set(x_727, 0, x_700);
lean_ctor_set(x_727, 1, x_704);
lean_ctor_set(x_727, 2, x_705);
lean_ctor_set(x_727, 3, x_706);
lean_ctor_set(x_727, 4, x_707);
lean_ctor_set(x_727, 5, x_708);
lean_ctor_set(x_727, 6, x_709);
lean_ctor_set(x_727, 7, x_710);
lean_ctor_set(x_727, 8, x_711);
lean_ctor_set(x_727, 9, x_712);
lean_ctor_set(x_727, 10, x_716);
lean_ctor_set_uint8(x_727, sizeof(void*)*11, x_713);
lean_ctor_set_uint8(x_727, sizeof(void*)*11 + 1, x_714);
lean_ctor_set_uint8(x_727, sizeof(void*)*11 + 2, x_715);
x_728 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_703);
x_2 = x_702;
x_3 = x_728;
x_4 = x_721;
goto _start;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_730 = lean_ctor_get(x_700, 0);
x_731 = lean_ctor_get(x_700, 1);
x_732 = lean_ctor_get(x_700, 2);
lean_inc(x_732);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_700);
x_733 = lean_unsigned_to_nat(1u);
x_734 = lean_nat_add(x_718, x_733);
lean_dec(x_718);
x_735 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_735, 0, x_730);
lean_ctor_set(x_735, 1, x_731);
lean_ctor_set(x_735, 2, x_732);
lean_ctor_set(x_735, 3, x_734);
lean_ctor_set(x_735, 4, x_719);
if (lean_is_scalar(x_717)) {
 x_736 = lean_alloc_ctor(0, 11, 3);
} else {
 x_736 = x_717;
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_704);
lean_ctor_set(x_736, 2, x_705);
lean_ctor_set(x_736, 3, x_706);
lean_ctor_set(x_736, 4, x_707);
lean_ctor_set(x_736, 5, x_708);
lean_ctor_set(x_736, 6, x_709);
lean_ctor_set(x_736, 7, x_710);
lean_ctor_set(x_736, 8, x_711);
lean_ctor_set(x_736, 9, x_712);
lean_ctor_set(x_736, 10, x_716);
lean_ctor_set_uint8(x_736, sizeof(void*)*11, x_713);
lean_ctor_set_uint8(x_736, sizeof(void*)*11 + 1, x_714);
lean_ctor_set_uint8(x_736, sizeof(void*)*11 + 2, x_715);
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_703);
x_2 = x_702;
x_3 = x_737;
x_4 = x_721;
goto _start;
}
}
}
}
else
{
uint8_t x_747; 
lean_dec(x_3);
lean_dec(x_1);
x_747 = !lean_is_exclusive(x_691);
if (x_747 == 0)
{
return x_691;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_691, 0);
x_749 = lean_ctor_get(x_691, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_691);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set(x_750, 1, x_749);
return x_750;
}
}
}
case 11:
{
lean_object* x_751; 
lean_dec(x_8);
lean_inc(x_3);
x_751 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
if (lean_obj_tag(x_752) == 0)
{
uint8_t x_753; 
lean_dec(x_3);
lean_dec(x_1);
x_753 = !lean_is_exclusive(x_751);
if (x_753 == 0)
{
lean_object* x_754; lean_object* x_755; 
x_754 = lean_ctor_get(x_751, 0);
lean_dec(x_754);
x_755 = lean_box(0);
lean_ctor_set(x_751, 0, x_755);
return x_751;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_751, 1);
lean_inc(x_756);
lean_dec(x_751);
x_757 = lean_box(0);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; uint8_t x_773; uint8_t x_774; uint8_t x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; lean_object* x_781; 
x_759 = lean_ctor_get(x_3, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_751, 1);
lean_inc(x_761);
lean_dec(x_751);
x_762 = lean_ctor_get(x_752, 0);
lean_inc(x_762);
lean_dec(x_752);
x_763 = lean_ctor_get(x_3, 1);
lean_inc(x_763);
x_764 = lean_ctor_get(x_759, 1);
lean_inc(x_764);
x_765 = lean_ctor_get(x_759, 2);
lean_inc(x_765);
x_766 = lean_ctor_get(x_759, 3);
lean_inc(x_766);
x_767 = lean_ctor_get(x_759, 4);
lean_inc(x_767);
x_768 = lean_ctor_get(x_759, 5);
lean_inc(x_768);
x_769 = lean_ctor_get(x_759, 6);
lean_inc(x_769);
x_770 = lean_ctor_get(x_759, 7);
lean_inc(x_770);
x_771 = lean_ctor_get(x_759, 8);
lean_inc(x_771);
x_772 = lean_ctor_get(x_759, 9);
lean_inc(x_772);
x_773 = lean_ctor_get_uint8(x_759, sizeof(void*)*11);
x_774 = lean_ctor_get_uint8(x_759, sizeof(void*)*11 + 1);
x_775 = lean_ctor_get_uint8(x_759, sizeof(void*)*11 + 2);
x_776 = lean_ctor_get(x_759, 10);
lean_inc(x_776);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 lean_ctor_release(x_759, 2);
 lean_ctor_release(x_759, 3);
 lean_ctor_release(x_759, 4);
 lean_ctor_release(x_759, 5);
 lean_ctor_release(x_759, 6);
 lean_ctor_release(x_759, 7);
 lean_ctor_release(x_759, 8);
 lean_ctor_release(x_759, 9);
 lean_ctor_release(x_759, 10);
 x_777 = x_759;
} else {
 lean_dec_ref(x_759);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_760, 3);
lean_inc(x_778);
x_779 = lean_ctor_get(x_760, 4);
lean_inc(x_779);
x_780 = lean_nat_dec_eq(x_778, x_779);
if (x_780 == 0)
{
lean_dec(x_3);
x_781 = x_761;
goto block_799;
}
else
{
lean_object* x_800; lean_object* x_801; 
x_800 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_801 = l_Lean_Elab_Tactic_throwError___rarg(x_800, x_3, x_761);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; 
x_802 = lean_ctor_get(x_801, 1);
lean_inc(x_802);
lean_dec(x_801);
x_781 = x_802;
goto block_799;
}
else
{
uint8_t x_803; 
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_776);
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
lean_dec(x_762);
lean_dec(x_760);
lean_dec(x_1);
x_803 = !lean_is_exclusive(x_801);
if (x_803 == 0)
{
return x_801;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_801, 0);
x_805 = lean_ctor_get(x_801, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_801);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
block_799:
{
uint8_t x_782; 
x_782 = !lean_is_exclusive(x_760);
if (x_782 == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_783 = lean_ctor_get(x_760, 4);
lean_dec(x_783);
x_784 = lean_ctor_get(x_760, 3);
lean_dec(x_784);
x_785 = lean_unsigned_to_nat(1u);
x_786 = lean_nat_add(x_778, x_785);
lean_dec(x_778);
lean_ctor_set(x_760, 3, x_786);
if (lean_is_scalar(x_777)) {
 x_787 = lean_alloc_ctor(0, 11, 3);
} else {
 x_787 = x_777;
}
lean_ctor_set(x_787, 0, x_760);
lean_ctor_set(x_787, 1, x_764);
lean_ctor_set(x_787, 2, x_765);
lean_ctor_set(x_787, 3, x_766);
lean_ctor_set(x_787, 4, x_767);
lean_ctor_set(x_787, 5, x_768);
lean_ctor_set(x_787, 6, x_769);
lean_ctor_set(x_787, 7, x_770);
lean_ctor_set(x_787, 8, x_771);
lean_ctor_set(x_787, 9, x_772);
lean_ctor_set(x_787, 10, x_776);
lean_ctor_set_uint8(x_787, sizeof(void*)*11, x_773);
lean_ctor_set_uint8(x_787, sizeof(void*)*11 + 1, x_774);
lean_ctor_set_uint8(x_787, sizeof(void*)*11 + 2, x_775);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_763);
x_2 = x_762;
x_3 = x_788;
x_4 = x_781;
goto _start;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_790 = lean_ctor_get(x_760, 0);
x_791 = lean_ctor_get(x_760, 1);
x_792 = lean_ctor_get(x_760, 2);
lean_inc(x_792);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_760);
x_793 = lean_unsigned_to_nat(1u);
x_794 = lean_nat_add(x_778, x_793);
lean_dec(x_778);
x_795 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_795, 0, x_790);
lean_ctor_set(x_795, 1, x_791);
lean_ctor_set(x_795, 2, x_792);
lean_ctor_set(x_795, 3, x_794);
lean_ctor_set(x_795, 4, x_779);
if (lean_is_scalar(x_777)) {
 x_796 = lean_alloc_ctor(0, 11, 3);
} else {
 x_796 = x_777;
}
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_764);
lean_ctor_set(x_796, 2, x_765);
lean_ctor_set(x_796, 3, x_766);
lean_ctor_set(x_796, 4, x_767);
lean_ctor_set(x_796, 5, x_768);
lean_ctor_set(x_796, 6, x_769);
lean_ctor_set(x_796, 7, x_770);
lean_ctor_set(x_796, 8, x_771);
lean_ctor_set(x_796, 9, x_772);
lean_ctor_set(x_796, 10, x_776);
lean_ctor_set_uint8(x_796, sizeof(void*)*11, x_773);
lean_ctor_set_uint8(x_796, sizeof(void*)*11 + 1, x_774);
lean_ctor_set_uint8(x_796, sizeof(void*)*11 + 2, x_775);
x_797 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_763);
x_2 = x_762;
x_3 = x_797;
x_4 = x_781;
goto _start;
}
}
}
}
else
{
uint8_t x_807; 
lean_dec(x_3);
lean_dec(x_1);
x_807 = !lean_is_exclusive(x_751);
if (x_807 == 0)
{
return x_751;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_751, 0);
x_809 = lean_ctor_get(x_751, 1);
lean_inc(x_809);
lean_inc(x_808);
lean_dec(x_751);
x_810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_810, 0, x_808);
lean_ctor_set(x_810, 1, x_809);
return x_810;
}
}
}
default: 
{
lean_object* x_811; 
lean_dec(x_8);
lean_inc(x_3);
x_811 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_6, x_3, x_7);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
if (lean_obj_tag(x_812) == 0)
{
uint8_t x_813; 
lean_dec(x_3);
lean_dec(x_1);
x_813 = !lean_is_exclusive(x_811);
if (x_813 == 0)
{
lean_object* x_814; lean_object* x_815; 
x_814 = lean_ctor_get(x_811, 0);
lean_dec(x_814);
x_815 = lean_box(0);
lean_ctor_set(x_811, 0, x_815);
return x_811;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_811, 1);
lean_inc(x_816);
lean_dec(x_811);
x_817 = lean_box(0);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; uint8_t x_833; uint8_t x_834; uint8_t x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; uint8_t x_840; lean_object* x_841; 
x_819 = lean_ctor_get(x_3, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_811, 1);
lean_inc(x_821);
lean_dec(x_811);
x_822 = lean_ctor_get(x_812, 0);
lean_inc(x_822);
lean_dec(x_812);
x_823 = lean_ctor_get(x_3, 1);
lean_inc(x_823);
x_824 = lean_ctor_get(x_819, 1);
lean_inc(x_824);
x_825 = lean_ctor_get(x_819, 2);
lean_inc(x_825);
x_826 = lean_ctor_get(x_819, 3);
lean_inc(x_826);
x_827 = lean_ctor_get(x_819, 4);
lean_inc(x_827);
x_828 = lean_ctor_get(x_819, 5);
lean_inc(x_828);
x_829 = lean_ctor_get(x_819, 6);
lean_inc(x_829);
x_830 = lean_ctor_get(x_819, 7);
lean_inc(x_830);
x_831 = lean_ctor_get(x_819, 8);
lean_inc(x_831);
x_832 = lean_ctor_get(x_819, 9);
lean_inc(x_832);
x_833 = lean_ctor_get_uint8(x_819, sizeof(void*)*11);
x_834 = lean_ctor_get_uint8(x_819, sizeof(void*)*11 + 1);
x_835 = lean_ctor_get_uint8(x_819, sizeof(void*)*11 + 2);
x_836 = lean_ctor_get(x_819, 10);
lean_inc(x_836);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 lean_ctor_release(x_819, 2);
 lean_ctor_release(x_819, 3);
 lean_ctor_release(x_819, 4);
 lean_ctor_release(x_819, 5);
 lean_ctor_release(x_819, 6);
 lean_ctor_release(x_819, 7);
 lean_ctor_release(x_819, 8);
 lean_ctor_release(x_819, 9);
 lean_ctor_release(x_819, 10);
 x_837 = x_819;
} else {
 lean_dec_ref(x_819);
 x_837 = lean_box(0);
}
x_838 = lean_ctor_get(x_820, 3);
lean_inc(x_838);
x_839 = lean_ctor_get(x_820, 4);
lean_inc(x_839);
x_840 = lean_nat_dec_eq(x_838, x_839);
if (x_840 == 0)
{
lean_dec(x_3);
x_841 = x_821;
goto block_859;
}
else
{
lean_object* x_860; lean_object* x_861; 
x_860 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_861 = l_Lean_Elab_Tactic_throwError___rarg(x_860, x_3, x_821);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_861, 1);
lean_inc(x_862);
lean_dec(x_861);
x_841 = x_862;
goto block_859;
}
else
{
uint8_t x_863; 
lean_dec(x_839);
lean_dec(x_838);
lean_dec(x_837);
lean_dec(x_836);
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
lean_dec(x_822);
lean_dec(x_820);
lean_dec(x_1);
x_863 = !lean_is_exclusive(x_861);
if (x_863 == 0)
{
return x_861;
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_864 = lean_ctor_get(x_861, 0);
x_865 = lean_ctor_get(x_861, 1);
lean_inc(x_865);
lean_inc(x_864);
lean_dec(x_861);
x_866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_866, 0, x_864);
lean_ctor_set(x_866, 1, x_865);
return x_866;
}
}
}
block_859:
{
uint8_t x_842; 
x_842 = !lean_is_exclusive(x_820);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_843 = lean_ctor_get(x_820, 4);
lean_dec(x_843);
x_844 = lean_ctor_get(x_820, 3);
lean_dec(x_844);
x_845 = lean_unsigned_to_nat(1u);
x_846 = lean_nat_add(x_838, x_845);
lean_dec(x_838);
lean_ctor_set(x_820, 3, x_846);
if (lean_is_scalar(x_837)) {
 x_847 = lean_alloc_ctor(0, 11, 3);
} else {
 x_847 = x_837;
}
lean_ctor_set(x_847, 0, x_820);
lean_ctor_set(x_847, 1, x_824);
lean_ctor_set(x_847, 2, x_825);
lean_ctor_set(x_847, 3, x_826);
lean_ctor_set(x_847, 4, x_827);
lean_ctor_set(x_847, 5, x_828);
lean_ctor_set(x_847, 6, x_829);
lean_ctor_set(x_847, 7, x_830);
lean_ctor_set(x_847, 8, x_831);
lean_ctor_set(x_847, 9, x_832);
lean_ctor_set(x_847, 10, x_836);
lean_ctor_set_uint8(x_847, sizeof(void*)*11, x_833);
lean_ctor_set_uint8(x_847, sizeof(void*)*11 + 1, x_834);
lean_ctor_set_uint8(x_847, sizeof(void*)*11 + 2, x_835);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_847);
lean_ctor_set(x_848, 1, x_823);
x_2 = x_822;
x_3 = x_848;
x_4 = x_841;
goto _start;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_850 = lean_ctor_get(x_820, 0);
x_851 = lean_ctor_get(x_820, 1);
x_852 = lean_ctor_get(x_820, 2);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_820);
x_853 = lean_unsigned_to_nat(1u);
x_854 = lean_nat_add(x_838, x_853);
lean_dec(x_838);
x_855 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_855, 0, x_850);
lean_ctor_set(x_855, 1, x_851);
lean_ctor_set(x_855, 2, x_852);
lean_ctor_set(x_855, 3, x_854);
lean_ctor_set(x_855, 4, x_839);
if (lean_is_scalar(x_837)) {
 x_856 = lean_alloc_ctor(0, 11, 3);
} else {
 x_856 = x_837;
}
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_824);
lean_ctor_set(x_856, 2, x_825);
lean_ctor_set(x_856, 3, x_826);
lean_ctor_set(x_856, 4, x_827);
lean_ctor_set(x_856, 5, x_828);
lean_ctor_set(x_856, 6, x_829);
lean_ctor_set(x_856, 7, x_830);
lean_ctor_set(x_856, 8, x_831);
lean_ctor_set(x_856, 9, x_832);
lean_ctor_set(x_856, 10, x_836);
lean_ctor_set_uint8(x_856, sizeof(void*)*11, x_833);
lean_ctor_set_uint8(x_856, sizeof(void*)*11 + 1, x_834);
lean_ctor_set_uint8(x_856, sizeof(void*)*11 + 2, x_835);
x_857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_823);
x_2 = x_822;
x_3 = x_857;
x_4 = x_841;
goto _start;
}
}
}
}
else
{
uint8_t x_867; 
lean_dec(x_3);
lean_dec(x_1);
x_867 = !lean_is_exclusive(x_811);
if (x_867 == 0)
{
return x_811;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_811, 0);
x_869 = lean_ctor_get(x_811, 1);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_811);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
return x_870;
}
}
}
}
}
else
{
uint8_t x_871; 
lean_dec(x_3);
lean_dec(x_1);
x_871 = !lean_is_exclusive(x_5);
if (x_871 == 0)
{
return x_5;
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_5, 0);
x_873 = lean_ctor_get(x_5, 1);
lean_inc(x_873);
lean_inc(x_872);
lean_dec(x_5);
x_874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_873);
return x_874;
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
x_8 = l_Lean_Meta_mkAuxName___closed__1;
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
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 10);
lean_dec(x_13);
lean_ctor_set(x_11, 10, x_1);
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getIdAt(x_6, x_14);
lean_dec(x_6);
x_16 = l_Lean_Name_eraseMacroScopes(x_15);
lean_dec(x_15);
lean_inc(x_3);
x_17 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_16, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = l_Lean_Syntax_isNone(x_8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_17);
x_23 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_24 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_dec(x_29);
lean_inc(x_21);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_30, 0, x_21);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_31, 0, x_30);
lean_inc(x_3);
x_32 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_28, x_31, x_3, x_26);
lean_dec(x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
lean_ctor_set(x_25, 1, x_35);
lean_ctor_set(x_25, 0, x_23);
x_36 = l_Array_empty___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_get_size(x_33);
lean_inc(x_3);
lean_inc(x_39);
x_40 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_19, x_33, x_39, x_39, x_38, x_3, x_34);
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_19);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_40, 1);
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = l_Array_isEmpty___rarg(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
if (x_50 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_40);
x_52 = l_Lean_Syntax_inhabited;
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get(x_52, x_49, x_53);
lean_dec(x_49);
x_55 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_56 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_54, x_55, x_3, x_45);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_51);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_51);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_49);
lean_dec(x_3);
lean_ctor_set(x_40, 0, x_51);
return x_40;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_ctor_get(x_41, 0);
lean_inc(x_66);
lean_dec(x_41);
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
lean_dec(x_42);
x_68 = lean_ctor_get(x_43, 0);
lean_inc(x_68);
lean_dec(x_43);
x_69 = l_Array_isEmpty___rarg(x_68);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_67);
if (x_69 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = l_Lean_Syntax_inhabited;
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get(x_71, x_68, x_72);
lean_dec(x_68);
x_74 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_75 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_73, x_74, x_3, x_65);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_70);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
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
else
{
lean_object* x_83; 
lean_dec(x_68);
lean_dec(x_3);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_65);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_21);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_40);
if (x_84 == 0)
{
return x_40;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_40, 0);
x_86 = lean_ctor_get(x_40, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_40);
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
lean_free_object(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_32);
if (x_88 == 0)
{
return x_32;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_32, 0);
x_90 = lean_ctor_get(x_32, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_32);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_25, 0);
lean_inc(x_92);
lean_dec(x_25);
lean_inc(x_21);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_93, 0, x_21);
x_94 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_94, 0, x_93);
lean_inc(x_3);
x_95 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_92, x_94, x_3, x_26);
lean_dec(x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_23);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Array_empty___closed__1;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_array_get_size(x_96);
lean_inc(x_3);
lean_inc(x_103);
x_104 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_19, x_96, x_103, x_103, x_102, x_3, x_97);
lean_dec(x_103);
lean_dec(x_96);
lean_dec(x_19);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_109 = x_104;
} else {
 lean_dec_ref(x_104);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = l_Array_isEmpty___rarg(x_112);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_21);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_114, 2, x_111);
if (x_113 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_109);
x_115 = l_Lean_Syntax_inhabited;
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_array_get(x_115, x_112, x_116);
lean_dec(x_112);
x_118 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_119 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_117, x_118, x_3, x_108);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
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
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_114);
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_125 = x_119;
} else {
 lean_dec_ref(x_119);
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
lean_object* x_127; 
lean_dec(x_112);
lean_dec(x_3);
if (lean_is_scalar(x_109)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_109;
}
lean_ctor_set(x_127, 0, x_114);
lean_ctor_set(x_127, 1, x_108);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_21);
lean_dec(x_3);
x_128 = lean_ctor_get(x_104, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_104, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_130 = x_104;
} else {
 lean_dec_ref(x_104);
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
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
x_132 = lean_ctor_get(x_95, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_95, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_134 = x_95;
} else {
 lean_dec_ref(x_95);
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
}
else
{
uint8_t x_136; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_24);
if (x_136 == 0)
{
return x_24;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_24, 0);
x_138 = lean_ctor_get(x_24, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_24);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_8);
x_140 = l_Array_empty___closed__1;
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_21);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_17, 0, x_141);
return x_17;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_17, 0);
x_143 = lean_ctor_get(x_17, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_17);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = l_Lean_Syntax_isNone(x_8);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_147 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_143);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
lean_inc(x_144);
x_152 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_153, 0, x_152);
lean_inc(x_3);
x_154 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_150, x_153, x_3, x_149);
lean_dec(x_150);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_151;
}
lean_ctor_set(x_158, 0, x_146);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Array_empty___closed__1;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_array_get_size(x_155);
lean_inc(x_3);
lean_inc(x_162);
x_163 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_142, x_155, x_162, x_162, x_161, x_3, x_156);
lean_dec(x_162);
lean_dec(x_155);
lean_dec(x_142);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_168 = x_163;
} else {
 lean_dec_ref(x_163);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
lean_dec(x_166);
x_172 = l_Array_isEmpty___rarg(x_171);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_144);
lean_ctor_set(x_173, 1, x_169);
lean_ctor_set(x_173, 2, x_170);
if (x_172 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_168);
x_174 = l_Lean_Syntax_inhabited;
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_array_get(x_174, x_171, x_175);
lean_dec(x_171);
x_177 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_178 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_176, x_177, x_3, x_167);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_173);
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_184 = x_178;
} else {
 lean_dec_ref(x_178);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; 
lean_dec(x_171);
lean_dec(x_3);
if (lean_is_scalar(x_168)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_168;
}
lean_ctor_set(x_186, 0, x_173);
lean_ctor_set(x_186, 1, x_167);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_144);
lean_dec(x_3);
x_187 = lean_ctor_get(x_163, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_163, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_189 = x_163;
} else {
 lean_dec_ref(x_163);
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
lean_dec(x_151);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_3);
x_191 = lean_ctor_get(x_154, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_154, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_193 = x_154;
} else {
 lean_dec_ref(x_154);
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
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_3);
x_195 = lean_ctor_get(x_147, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_147, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_197 = x_147;
} else {
 lean_dec_ref(x_147);
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
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_142);
lean_dec(x_3);
lean_dec(x_8);
x_199 = l_Array_empty___closed__1;
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_144);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_143);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_3);
lean_dec(x_8);
x_202 = !lean_is_exclusive(x_17);
if (x_202 == 0)
{
return x_17;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_17, 0);
x_204 = lean_ctor_get(x_17, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_17);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; lean_object* x_207; 
lean_dec(x_6);
x_206 = 0;
x_207 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_206, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec(x_209);
lean_ctor_set(x_207, 0, x_210);
return x_207;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_207, 0);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_207);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_207);
if (x_215 == 0)
{
return x_207;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_207, 0);
x_217 = lean_ctor_get(x_207, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_207);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; 
x_219 = lean_ctor_get(x_11, 0);
x_220 = lean_ctor_get(x_11, 1);
x_221 = lean_ctor_get(x_11, 2);
x_222 = lean_ctor_get(x_11, 3);
x_223 = lean_ctor_get(x_11, 4);
x_224 = lean_ctor_get(x_11, 5);
x_225 = lean_ctor_get(x_11, 6);
x_226 = lean_ctor_get(x_11, 7);
x_227 = lean_ctor_get(x_11, 8);
x_228 = lean_ctor_get(x_11, 9);
x_229 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
x_230 = lean_ctor_get_uint8(x_11, sizeof(void*)*11 + 1);
x_231 = lean_ctor_get_uint8(x_11, sizeof(void*)*11 + 2);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_11);
x_232 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_232, 0, x_219);
lean_ctor_set(x_232, 1, x_220);
lean_ctor_set(x_232, 2, x_221);
lean_ctor_set(x_232, 3, x_222);
lean_ctor_set(x_232, 4, x_223);
lean_ctor_set(x_232, 5, x_224);
lean_ctor_set(x_232, 6, x_225);
lean_ctor_set(x_232, 7, x_226);
lean_ctor_set(x_232, 8, x_227);
lean_ctor_set(x_232, 9, x_228);
lean_ctor_set(x_232, 10, x_1);
lean_ctor_set_uint8(x_232, sizeof(void*)*11, x_229);
lean_ctor_set_uint8(x_232, sizeof(void*)*11 + 1, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*11 + 2, x_231);
lean_ctor_set(x_3, 0, x_232);
if (x_9 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_unsigned_to_nat(1u);
x_234 = l_Lean_Syntax_getIdAt(x_6, x_233);
lean_dec(x_6);
x_235 = l_Lean_Name_eraseMacroScopes(x_234);
lean_dec(x_234);
lean_inc(x_3);
x_236 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_235, x_3, x_4);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
x_241 = l_Lean_Syntax_isNone(x_8);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_239);
x_242 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_243 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_238);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
lean_inc(x_240);
x_248 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_248, 0, x_240);
x_249 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_249, 0, x_248);
lean_inc(x_3);
x_250 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_246, x_249, x_3, x_245);
lean_dec(x_246);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_box(0);
if (lean_is_scalar(x_247)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_247;
}
lean_ctor_set(x_254, 0, x_242);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Array_empty___closed__1;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_array_get_size(x_251);
lean_inc(x_3);
lean_inc(x_258);
x_259 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_237, x_251, x_258, x_258, x_257, x_3, x_252);
lean_dec(x_258);
lean_dec(x_251);
lean_dec(x_237);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_264 = x_259;
} else {
 lean_dec_ref(x_259);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_260, 0);
lean_inc(x_265);
lean_dec(x_260);
x_266 = lean_ctor_get(x_261, 0);
lean_inc(x_266);
lean_dec(x_261);
x_267 = lean_ctor_get(x_262, 0);
lean_inc(x_267);
lean_dec(x_262);
x_268 = l_Array_isEmpty___rarg(x_267);
x_269 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_269, 0, x_240);
lean_ctor_set(x_269, 1, x_265);
lean_ctor_set(x_269, 2, x_266);
if (x_268 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_264);
x_270 = l_Lean_Syntax_inhabited;
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_array_get(x_270, x_267, x_271);
lean_dec(x_267);
x_273 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_274 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_272, x_273, x_3, x_263);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_269);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_269);
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
else
{
lean_object* x_282; 
lean_dec(x_267);
lean_dec(x_3);
if (lean_is_scalar(x_264)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_264;
}
lean_ctor_set(x_282, 0, x_269);
lean_ctor_set(x_282, 1, x_263);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_240);
lean_dec(x_3);
x_283 = lean_ctor_get(x_259, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_259, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_285 = x_259;
} else {
 lean_dec_ref(x_259);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_247);
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_3);
x_287 = lean_ctor_get(x_250, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_3);
x_291 = lean_ctor_get(x_243, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_243, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_293 = x_243;
} else {
 lean_dec_ref(x_243);
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
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_237);
lean_dec(x_3);
lean_dec(x_8);
x_295 = l_Array_empty___closed__1;
x_296 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_296, 0, x_240);
lean_ctor_set(x_296, 1, x_295);
lean_ctor_set(x_296, 2, x_295);
if (lean_is_scalar(x_239)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_239;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_238);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_3);
lean_dec(x_8);
x_298 = lean_ctor_get(x_236, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_236, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_300 = x_236;
} else {
 lean_dec_ref(x_236);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
else
{
uint8_t x_302; lean_object* x_303; 
lean_dec(x_6);
x_302 = 0;
x_303 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_302, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_304, 0);
lean_inc(x_307);
lean_dec(x_304);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_303, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_303, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_311 = x_303;
} else {
 lean_dec_ref(x_303);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_313 = lean_ctor_get(x_3, 0);
x_314 = lean_ctor_get(x_3, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_3);
x_315 = lean_ctor_get(x_313, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_313, 2);
lean_inc(x_317);
x_318 = lean_ctor_get(x_313, 3);
lean_inc(x_318);
x_319 = lean_ctor_get(x_313, 4);
lean_inc(x_319);
x_320 = lean_ctor_get(x_313, 5);
lean_inc(x_320);
x_321 = lean_ctor_get(x_313, 6);
lean_inc(x_321);
x_322 = lean_ctor_get(x_313, 7);
lean_inc(x_322);
x_323 = lean_ctor_get(x_313, 8);
lean_inc(x_323);
x_324 = lean_ctor_get(x_313, 9);
lean_inc(x_324);
x_325 = lean_ctor_get_uint8(x_313, sizeof(void*)*11);
x_326 = lean_ctor_get_uint8(x_313, sizeof(void*)*11 + 1);
x_327 = lean_ctor_get_uint8(x_313, sizeof(void*)*11 + 2);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 lean_ctor_release(x_313, 3);
 lean_ctor_release(x_313, 4);
 lean_ctor_release(x_313, 5);
 lean_ctor_release(x_313, 6);
 lean_ctor_release(x_313, 7);
 lean_ctor_release(x_313, 8);
 lean_ctor_release(x_313, 9);
 lean_ctor_release(x_313, 10);
 x_328 = x_313;
} else {
 lean_dec_ref(x_313);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 11, 3);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_315);
lean_ctor_set(x_329, 1, x_316);
lean_ctor_set(x_329, 2, x_317);
lean_ctor_set(x_329, 3, x_318);
lean_ctor_set(x_329, 4, x_319);
lean_ctor_set(x_329, 5, x_320);
lean_ctor_set(x_329, 6, x_321);
lean_ctor_set(x_329, 7, x_322);
lean_ctor_set(x_329, 8, x_323);
lean_ctor_set(x_329, 9, x_324);
lean_ctor_set(x_329, 10, x_1);
lean_ctor_set_uint8(x_329, sizeof(void*)*11, x_325);
lean_ctor_set_uint8(x_329, sizeof(void*)*11 + 1, x_326);
lean_ctor_set_uint8(x_329, sizeof(void*)*11 + 2, x_327);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_314);
if (x_9 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_unsigned_to_nat(1u);
x_332 = l_Lean_Syntax_getIdAt(x_6, x_331);
lean_dec(x_6);
x_333 = l_Lean_Name_eraseMacroScopes(x_332);
lean_dec(x_332);
lean_inc(x_330);
x_334 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_333, x_330, x_4);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_335, 0);
lean_inc(x_338);
x_339 = l_Lean_Syntax_isNone(x_8);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_337);
x_340 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_330);
x_341 = l_Lean_Elab_Tactic_getMainGoal(x_330, x_336);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
lean_inc(x_338);
x_346 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_346, 0, x_338);
x_347 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_347, 0, x_346);
lean_inc(x_330);
x_348 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_344, x_347, x_330, x_343);
lean_dec(x_344);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_box(0);
if (lean_is_scalar(x_345)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_345;
}
lean_ctor_set(x_352, 0, x_340);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Array_empty___closed__1;
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_array_get_size(x_349);
lean_inc(x_330);
lean_inc(x_356);
x_357 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_335, x_349, x_356, x_356, x_355, x_330, x_350);
lean_dec(x_356);
lean_dec(x_349);
lean_dec(x_335);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_357, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_362 = x_357;
} else {
 lean_dec_ref(x_357);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_358, 0);
lean_inc(x_363);
lean_dec(x_358);
x_364 = lean_ctor_get(x_359, 0);
lean_inc(x_364);
lean_dec(x_359);
x_365 = lean_ctor_get(x_360, 0);
lean_inc(x_365);
lean_dec(x_360);
x_366 = l_Array_isEmpty___rarg(x_365);
x_367 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_367, 0, x_338);
lean_ctor_set(x_367, 1, x_363);
lean_ctor_set(x_367, 2, x_364);
if (x_366 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_362);
x_368 = l_Lean_Syntax_inhabited;
x_369 = lean_unsigned_to_nat(0u);
x_370 = lean_array_get(x_368, x_365, x_369);
lean_dec(x_365);
x_371 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_372 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_370, x_371, x_330, x_361);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_367);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_367);
x_376 = lean_ctor_get(x_372, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_372, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_378 = x_372;
} else {
 lean_dec_ref(x_372);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_object* x_380; 
lean_dec(x_365);
lean_dec(x_330);
if (lean_is_scalar(x_362)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_362;
}
lean_ctor_set(x_380, 0, x_367);
lean_ctor_set(x_380, 1, x_361);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_338);
lean_dec(x_330);
x_381 = lean_ctor_get(x_357, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_357, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_383 = x_357;
} else {
 lean_dec_ref(x_357);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_345);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_335);
lean_dec(x_330);
x_385 = lean_ctor_get(x_348, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_348, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_387 = x_348;
} else {
 lean_dec_ref(x_348);
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
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_335);
lean_dec(x_330);
x_389 = lean_ctor_get(x_341, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_341, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_391 = x_341;
} else {
 lean_dec_ref(x_341);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_335);
lean_dec(x_330);
lean_dec(x_8);
x_393 = l_Array_empty___closed__1;
x_394 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_394, 0, x_338);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set(x_394, 2, x_393);
if (lean_is_scalar(x_337)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_337;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_336);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_330);
lean_dec(x_8);
x_396 = lean_ctor_get(x_334, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_334, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_398 = x_334;
} else {
 lean_dec_ref(x_334);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
else
{
uint8_t x_400; lean_object* x_401; 
lean_dec(x_6);
x_400 = 0;
x_401 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_8, x_400, x_330, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
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
x_405 = lean_ctor_get(x_402, 0);
lean_inc(x_405);
lean_dec(x_402);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_409 = x_401;
} else {
 lean_dec_ref(x_401);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
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
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRef___rarg), 4, 2);
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
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRef___rarg), 4, 2);
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
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 4, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__1), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Tactic_focusAux___rarg(x_8, x_2, x_3);
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
