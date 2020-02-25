// Lean compiler output
// Module: Init.Lean.Elab.Tactic.Induction
// Imports: Init.Lean.Meta.RecursorInfo Init.Lean.Meta.Tactic.Induction Init.Lean.Elab.Tactic.ElabTerm Init.Lean.Elab.Tactic.Generalize
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
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__5;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4;
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_restore(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1;
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__9;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__3;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Init_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames___boxed(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__2;
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__6;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__2;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__3(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
uint8_t l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__5;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3;
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__3;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__7;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_save(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__1;
lean_object* l_Lean_Meta_generalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__7;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
lean_object* l_Lean_Elab_Tactic_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__4;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__8;
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__8;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__4;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__10;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1;
lean_object* l_Lean_Meta_getParamNames(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__2;
lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_10__getAltRHS___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Tactic_underscoreFn___closed__4;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generalize");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_local_ctx_find_from_user_name(x_3, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
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
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getLCtx___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_2);
x_14 = l_Lean_Elab_Tactic_evalGeneralizeAux(x_2, x_3, x_12, x_8, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1), 5, 2);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_2);
x_17 = l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_2, x_18, x_5, x_15);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_5);
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2), 6, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
x_12 = l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_1, x_13, x_4, x_5);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1;
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(x_8, x_7, x_3, x_4);
return x_9;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_trace), 5, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed), 4, 1);
lean_closure_set(x_10, 0, x_5);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_1, x_11, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Array_empty___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise depends on variable being generalized");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Array_contains___at___private_Init_Lean_Class_1__checkOutParam___main___spec__1(x_7, x_9);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_3);
lean_dec(x_8);
lean_dec(x_7);
x_15 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_16 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = l_Lean_Expr_fvarId_x21(x_1);
x_25 = l_Array_contains___at___private_Init_Lean_Class_1__checkOutParam___main___spec__1(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_26 = lean_array_get_size(x_22);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
lean_dec(x_22);
x_31 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_32 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(x_1, x_3, x_4);
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
x_16 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed), 5, 2);
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(x_5, x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_10__getAltRHS___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Induction_10__getAltRHS(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_1, x_2, x_5);
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
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkAlt");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
x_2 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor name '");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(x_10);
lean_inc(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_12);
lean_inc(x_4);
x_15 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_14, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Parser_Tactic_underscoreFn___closed__4;
x_18 = lean_name_eq(x_11, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = 0;
x_20 = l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_11, x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_10, x_21);
lean_dec(x_10);
x_23 = l_Lean_Name_toString___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_11);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_Term_mkConst___closed__4;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_4);
x_31 = l_Lean_Elab_Tactic_throwError___rarg(x_22, x_30, x_4, x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_3, x_33);
lean_dec(x_3);
x_3 = x_34;
x_5 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_3, x_40);
lean_dec(x_3);
x_3 = x_41;
x_5 = x_16;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_10);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_3 = x_44;
x_5 = x_16;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_2, x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(x_1, x_2, x_3, x_4);
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
x_14 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
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
x_33 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_100 = lean_ctor_get(x_4, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 4);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_nat_dec_eq(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
x_20 = x_18;
goto block_99;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_106 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_105, x_4, x_18);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_20 = x_107;
goto block_99;
}
else
{
uint8_t x_108; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
return x_106;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_106, 0);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_106);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
block_99:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_22, 3);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
lean_ctor_set(x_22, 3, x_30);
x_31 = 0;
x_32 = 0;
lean_ctor_set_uint32(x_21, sizeof(void*)*10, x_31);
lean_ctor_set_uint8(x_21, sizeof(void*)*10 + 7, x_32);
x_3 = x_19;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
x_36 = lean_ctor_get(x_22, 2);
x_37 = lean_ctor_get(x_22, 3);
x_38 = lean_ctor_get(x_22, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_37, x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_38);
x_42 = 0;
x_43 = 0;
lean_ctor_set(x_21, 0, x_41);
lean_ctor_set_uint32(x_21, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_21, sizeof(void*)*10 + 7, x_43);
x_3 = x_19;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint32_t x_66; uint8_t x_67; lean_object* x_68; 
x_45 = lean_ctor_get(x_21, 1);
x_46 = lean_ctor_get(x_21, 2);
x_47 = lean_ctor_get(x_21, 3);
x_48 = lean_ctor_get(x_21, 4);
x_49 = lean_ctor_get(x_21, 5);
x_50 = lean_ctor_get(x_21, 6);
x_51 = lean_ctor_get(x_21, 7);
x_52 = lean_ctor_get(x_21, 8);
x_53 = lean_ctor_get(x_21, 9);
x_54 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 4);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 5);
x_56 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 6);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_57 = lean_ctor_get(x_22, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_22, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_22, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_22, 4);
lean_inc(x_61);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 x_62 = x_22;
} else {
 lean_dec_ref(x_22);
 x_62 = lean_box(0);
}
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_60, x_63);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_58);
lean_ctor_set(x_65, 2, x_59);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 4, x_61);
x_66 = 0;
x_67 = 0;
x_68 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_45);
lean_ctor_set(x_68, 2, x_46);
lean_ctor_set(x_68, 3, x_47);
lean_ctor_set(x_68, 4, x_48);
lean_ctor_set(x_68, 5, x_49);
lean_ctor_set(x_68, 6, x_50);
lean_ctor_set(x_68, 7, x_51);
lean_ctor_set(x_68, 8, x_52);
lean_ctor_set(x_68, 9, x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 4, x_54);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 5, x_55);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 6, x_56);
lean_ctor_set_uint32(x_68, sizeof(void*)*10, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 7, x_67);
lean_ctor_set(x_4, 0, x_68);
x_3 = x_19;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint32_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_70 = lean_ctor_get(x_4, 1);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_4);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_21, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_21, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_21, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_21, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_21, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_21, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_21, 8);
lean_inc(x_79);
x_80 = lean_ctor_get(x_21, 9);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 4);
x_82 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 5);
x_83 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 lean_ctor_release(x_21, 6);
 lean_ctor_release(x_21, 7);
 lean_ctor_release(x_21, 8);
 lean_ctor_release(x_21, 9);
 x_84 = x_21;
} else {
 lean_dec_ref(x_21);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_22, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_22, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_22, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_22, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_22, 4);
lean_inc(x_89);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 x_90 = x_22;
} else {
 lean_dec_ref(x_22);
 x_90 = lean_box(0);
}
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_88, x_91);
lean_dec(x_88);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_89);
x_94 = 0;
x_95 = 0;
if (lean_is_scalar(x_84)) {
 x_96 = lean_alloc_ctor(0, 10, 8);
} else {
 x_96 = x_84;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_72);
lean_ctor_set(x_96, 2, x_73);
lean_ctor_set(x_96, 3, x_74);
lean_ctor_set(x_96, 4, x_75);
lean_ctor_set(x_96, 5, x_76);
lean_ctor_set(x_96, 6, x_77);
lean_ctor_set(x_96, 7, x_78);
lean_ctor_set(x_96, 8, x_79);
lean_ctor_set(x_96, 9, x_80);
lean_ctor_set_uint8(x_96, sizeof(void*)*10 + 4, x_81);
lean_ctor_set_uint8(x_96, sizeof(void*)*10 + 5, x_82);
lean_ctor_set_uint8(x_96, sizeof(void*)*10 + 6, x_83);
lean_ctor_set_uint32(x_96, sizeof(void*)*10, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*10 + 7, x_95);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_70);
lean_ctor_set(x_97, 2, x_71);
x_3 = x_19;
x_4 = x_97;
x_5 = x_20;
goto _start;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_10);
if (x_112 == 0)
{
return x_10;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_10, 0);
x_114 = lean_ctor_get(x_10, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_10);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 1:
{
lean_object* x_116; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_116 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_116, 0, x_120);
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_124 = lean_ctor_get(x_116, 1);
lean_inc(x_124);
lean_dec(x_116);
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
lean_dec(x_117);
x_206 = lean_ctor_get(x_4, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_ctor_get(x_207, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 4);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_nat_dec_eq(x_208, x_209);
lean_dec(x_209);
lean_dec(x_208);
if (x_210 == 0)
{
x_126 = x_124;
goto block_205;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_212 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_211, x_4, x_124);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_126 = x_213;
goto block_205;
}
else
{
uint8_t x_214; 
lean_dec(x_125);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
return x_212;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_212, 0);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_212);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
block_205:
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_4, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = !lean_is_exclusive(x_4);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_4, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_127);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_127, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_128);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint32_t x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_128, 3);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_134, x_135);
lean_dec(x_134);
lean_ctor_set(x_128, 3, x_136);
x_137 = 0;
x_138 = 0;
lean_ctor_set_uint32(x_127, sizeof(void*)*10, x_137);
lean_ctor_set_uint8(x_127, sizeof(void*)*10 + 7, x_138);
x_3 = x_125;
x_5 = x_126;
goto _start;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint32_t x_148; uint8_t x_149; 
x_140 = lean_ctor_get(x_128, 0);
x_141 = lean_ctor_get(x_128, 1);
x_142 = lean_ctor_get(x_128, 2);
x_143 = lean_ctor_get(x_128, 3);
x_144 = lean_ctor_get(x_128, 4);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_128);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_143, x_145);
lean_dec(x_143);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_141);
lean_ctor_set(x_147, 2, x_142);
lean_ctor_set(x_147, 3, x_146);
lean_ctor_set(x_147, 4, x_144);
x_148 = 0;
x_149 = 0;
lean_ctor_set(x_127, 0, x_147);
lean_ctor_set_uint32(x_127, sizeof(void*)*10, x_148);
lean_ctor_set_uint8(x_127, sizeof(void*)*10 + 7, x_149);
x_3 = x_125;
x_5 = x_126;
goto _start;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint32_t x_172; uint8_t x_173; lean_object* x_174; 
x_151 = lean_ctor_get(x_127, 1);
x_152 = lean_ctor_get(x_127, 2);
x_153 = lean_ctor_get(x_127, 3);
x_154 = lean_ctor_get(x_127, 4);
x_155 = lean_ctor_get(x_127, 5);
x_156 = lean_ctor_get(x_127, 6);
x_157 = lean_ctor_get(x_127, 7);
x_158 = lean_ctor_get(x_127, 8);
x_159 = lean_ctor_get(x_127, 9);
x_160 = lean_ctor_get_uint8(x_127, sizeof(void*)*10 + 4);
x_161 = lean_ctor_get_uint8(x_127, sizeof(void*)*10 + 5);
x_162 = lean_ctor_get_uint8(x_127, sizeof(void*)*10 + 6);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_127);
x_163 = lean_ctor_get(x_128, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_128, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_128, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_128, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_128, 4);
lean_inc(x_167);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 x_168 = x_128;
} else {
 lean_dec_ref(x_128);
 x_168 = lean_box(0);
}
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_nat_add(x_166, x_169);
lean_dec(x_166);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 5, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_163);
lean_ctor_set(x_171, 1, x_164);
lean_ctor_set(x_171, 2, x_165);
lean_ctor_set(x_171, 3, x_170);
lean_ctor_set(x_171, 4, x_167);
x_172 = 0;
x_173 = 0;
x_174 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_151);
lean_ctor_set(x_174, 2, x_152);
lean_ctor_set(x_174, 3, x_153);
lean_ctor_set(x_174, 4, x_154);
lean_ctor_set(x_174, 5, x_155);
lean_ctor_set(x_174, 6, x_156);
lean_ctor_set(x_174, 7, x_157);
lean_ctor_set(x_174, 8, x_158);
lean_ctor_set(x_174, 9, x_159);
lean_ctor_set_uint8(x_174, sizeof(void*)*10 + 4, x_160);
lean_ctor_set_uint8(x_174, sizeof(void*)*10 + 5, x_161);
lean_ctor_set_uint8(x_174, sizeof(void*)*10 + 6, x_162);
lean_ctor_set_uint32(x_174, sizeof(void*)*10, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*10 + 7, x_173);
lean_ctor_set(x_4, 0, x_174);
x_3 = x_125;
x_5 = x_126;
goto _start;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint32_t x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; 
x_176 = lean_ctor_get(x_4, 1);
x_177 = lean_ctor_get(x_4, 2);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_4);
x_178 = lean_ctor_get(x_127, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_127, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_127, 3);
lean_inc(x_180);
x_181 = lean_ctor_get(x_127, 4);
lean_inc(x_181);
x_182 = lean_ctor_get(x_127, 5);
lean_inc(x_182);
x_183 = lean_ctor_get(x_127, 6);
lean_inc(x_183);
x_184 = lean_ctor_get(x_127, 7);
lean_inc(x_184);
x_185 = lean_ctor_get(x_127, 8);
lean_inc(x_185);
x_186 = lean_ctor_get(x_127, 9);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_127, sizeof(void*)*10 + 4);
x_188 = lean_ctor_get_uint8(x_127, sizeof(void*)*10 + 5);
x_189 = lean_ctor_get_uint8(x_127, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 lean_ctor_release(x_127, 6);
 lean_ctor_release(x_127, 7);
 lean_ctor_release(x_127, 8);
 lean_ctor_release(x_127, 9);
 x_190 = x_127;
} else {
 lean_dec_ref(x_127);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_128, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_128, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_128, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_128, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_128, 4);
lean_inc(x_195);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 x_196 = x_128;
} else {
 lean_dec_ref(x_128);
 x_196 = lean_box(0);
}
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_194, x_197);
lean_dec(x_194);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(0, 5, 0);
} else {
 x_199 = x_196;
}
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_192);
lean_ctor_set(x_199, 2, x_193);
lean_ctor_set(x_199, 3, x_198);
lean_ctor_set(x_199, 4, x_195);
x_200 = 0;
x_201 = 0;
if (lean_is_scalar(x_190)) {
 x_202 = lean_alloc_ctor(0, 10, 8);
} else {
 x_202 = x_190;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_178);
lean_ctor_set(x_202, 2, x_179);
lean_ctor_set(x_202, 3, x_180);
lean_ctor_set(x_202, 4, x_181);
lean_ctor_set(x_202, 5, x_182);
lean_ctor_set(x_202, 6, x_183);
lean_ctor_set(x_202, 7, x_184);
lean_ctor_set(x_202, 8, x_185);
lean_ctor_set(x_202, 9, x_186);
lean_ctor_set_uint8(x_202, sizeof(void*)*10 + 4, x_187);
lean_ctor_set_uint8(x_202, sizeof(void*)*10 + 5, x_188);
lean_ctor_set_uint8(x_202, sizeof(void*)*10 + 6, x_189);
lean_ctor_set_uint32(x_202, sizeof(void*)*10, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*10 + 7, x_201);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_176);
lean_ctor_set(x_203, 2, x_177);
x_3 = x_125;
x_4 = x_203;
x_5 = x_126;
goto _start;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_116);
if (x_218 == 0)
{
return x_116;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_116, 0);
x_220 = lean_ctor_get(x_116, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_116);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
case 2:
{
lean_object* x_222; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_222 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_222);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 0);
lean_dec(x_225);
x_226 = lean_box(0);
lean_ctor_set(x_222, 0, x_226);
return x_222;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_dec(x_222);
x_228 = lean_box(0);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_230 = lean_ctor_get(x_222, 1);
lean_inc(x_230);
lean_dec(x_222);
x_231 = lean_ctor_get(x_223, 0);
lean_inc(x_231);
lean_dec(x_223);
x_312 = lean_ctor_get(x_4, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_ctor_get(x_313, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 4);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_nat_dec_eq(x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
if (x_316 == 0)
{
x_232 = x_230;
goto block_311;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_318 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_317, x_4, x_230);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_232 = x_319;
goto block_311;
}
else
{
uint8_t x_320; 
lean_dec(x_231);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_318);
if (x_320 == 0)
{
return x_318;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_318, 0);
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_318);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
block_311:
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_233 = lean_ctor_get(x_4, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = !lean_is_exclusive(x_4);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_4, 0);
lean_dec(x_236);
x_237 = !lean_is_exclusive(x_233);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_233, 0);
lean_dec(x_238);
x_239 = !lean_is_exclusive(x_234);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint32_t x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_234, 3);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_240, x_241);
lean_dec(x_240);
lean_ctor_set(x_234, 3, x_242);
x_243 = 0;
x_244 = 0;
lean_ctor_set_uint32(x_233, sizeof(void*)*10, x_243);
lean_ctor_set_uint8(x_233, sizeof(void*)*10 + 7, x_244);
x_3 = x_231;
x_5 = x_232;
goto _start;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint32_t x_254; uint8_t x_255; 
x_246 = lean_ctor_get(x_234, 0);
x_247 = lean_ctor_get(x_234, 1);
x_248 = lean_ctor_get(x_234, 2);
x_249 = lean_ctor_get(x_234, 3);
x_250 = lean_ctor_get(x_234, 4);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_234);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_249, x_251);
lean_dec(x_249);
x_253 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_253, 0, x_246);
lean_ctor_set(x_253, 1, x_247);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set(x_253, 3, x_252);
lean_ctor_set(x_253, 4, x_250);
x_254 = 0;
x_255 = 0;
lean_ctor_set(x_233, 0, x_253);
lean_ctor_set_uint32(x_233, sizeof(void*)*10, x_254);
lean_ctor_set_uint8(x_233, sizeof(void*)*10 + 7, x_255);
x_3 = x_231;
x_5 = x_232;
goto _start;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint32_t x_278; uint8_t x_279; lean_object* x_280; 
x_257 = lean_ctor_get(x_233, 1);
x_258 = lean_ctor_get(x_233, 2);
x_259 = lean_ctor_get(x_233, 3);
x_260 = lean_ctor_get(x_233, 4);
x_261 = lean_ctor_get(x_233, 5);
x_262 = lean_ctor_get(x_233, 6);
x_263 = lean_ctor_get(x_233, 7);
x_264 = lean_ctor_get(x_233, 8);
x_265 = lean_ctor_get(x_233, 9);
x_266 = lean_ctor_get_uint8(x_233, sizeof(void*)*10 + 4);
x_267 = lean_ctor_get_uint8(x_233, sizeof(void*)*10 + 5);
x_268 = lean_ctor_get_uint8(x_233, sizeof(void*)*10 + 6);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_233);
x_269 = lean_ctor_get(x_234, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_234, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_234, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_234, 3);
lean_inc(x_272);
x_273 = lean_ctor_get(x_234, 4);
lean_inc(x_273);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 lean_ctor_release(x_234, 4);
 x_274 = x_234;
} else {
 lean_dec_ref(x_234);
 x_274 = lean_box(0);
}
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_add(x_272, x_275);
lean_dec(x_272);
if (lean_is_scalar(x_274)) {
 x_277 = lean_alloc_ctor(0, 5, 0);
} else {
 x_277 = x_274;
}
lean_ctor_set(x_277, 0, x_269);
lean_ctor_set(x_277, 1, x_270);
lean_ctor_set(x_277, 2, x_271);
lean_ctor_set(x_277, 3, x_276);
lean_ctor_set(x_277, 4, x_273);
x_278 = 0;
x_279 = 0;
x_280 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_257);
lean_ctor_set(x_280, 2, x_258);
lean_ctor_set(x_280, 3, x_259);
lean_ctor_set(x_280, 4, x_260);
lean_ctor_set(x_280, 5, x_261);
lean_ctor_set(x_280, 6, x_262);
lean_ctor_set(x_280, 7, x_263);
lean_ctor_set(x_280, 8, x_264);
lean_ctor_set(x_280, 9, x_265);
lean_ctor_set_uint8(x_280, sizeof(void*)*10 + 4, x_266);
lean_ctor_set_uint8(x_280, sizeof(void*)*10 + 5, x_267);
lean_ctor_set_uint8(x_280, sizeof(void*)*10 + 6, x_268);
lean_ctor_set_uint32(x_280, sizeof(void*)*10, x_278);
lean_ctor_set_uint8(x_280, sizeof(void*)*10 + 7, x_279);
lean_ctor_set(x_4, 0, x_280);
x_3 = x_231;
x_5 = x_232;
goto _start;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint32_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; 
x_282 = lean_ctor_get(x_4, 1);
x_283 = lean_ctor_get(x_4, 2);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_4);
x_284 = lean_ctor_get(x_233, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_233, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_233, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_233, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_233, 5);
lean_inc(x_288);
x_289 = lean_ctor_get(x_233, 6);
lean_inc(x_289);
x_290 = lean_ctor_get(x_233, 7);
lean_inc(x_290);
x_291 = lean_ctor_get(x_233, 8);
lean_inc(x_291);
x_292 = lean_ctor_get(x_233, 9);
lean_inc(x_292);
x_293 = lean_ctor_get_uint8(x_233, sizeof(void*)*10 + 4);
x_294 = lean_ctor_get_uint8(x_233, sizeof(void*)*10 + 5);
x_295 = lean_ctor_get_uint8(x_233, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 lean_ctor_release(x_233, 3);
 lean_ctor_release(x_233, 4);
 lean_ctor_release(x_233, 5);
 lean_ctor_release(x_233, 6);
 lean_ctor_release(x_233, 7);
 lean_ctor_release(x_233, 8);
 lean_ctor_release(x_233, 9);
 x_296 = x_233;
} else {
 lean_dec_ref(x_233);
 x_296 = lean_box(0);
}
x_297 = lean_ctor_get(x_234, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_234, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_234, 2);
lean_inc(x_299);
x_300 = lean_ctor_get(x_234, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_234, 4);
lean_inc(x_301);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 lean_ctor_release(x_234, 4);
 x_302 = x_234;
} else {
 lean_dec_ref(x_234);
 x_302 = lean_box(0);
}
x_303 = lean_unsigned_to_nat(1u);
x_304 = lean_nat_add(x_300, x_303);
lean_dec(x_300);
if (lean_is_scalar(x_302)) {
 x_305 = lean_alloc_ctor(0, 5, 0);
} else {
 x_305 = x_302;
}
lean_ctor_set(x_305, 0, x_297);
lean_ctor_set(x_305, 1, x_298);
lean_ctor_set(x_305, 2, x_299);
lean_ctor_set(x_305, 3, x_304);
lean_ctor_set(x_305, 4, x_301);
x_306 = 0;
x_307 = 0;
if (lean_is_scalar(x_296)) {
 x_308 = lean_alloc_ctor(0, 10, 8);
} else {
 x_308 = x_296;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_284);
lean_ctor_set(x_308, 2, x_285);
lean_ctor_set(x_308, 3, x_286);
lean_ctor_set(x_308, 4, x_287);
lean_ctor_set(x_308, 5, x_288);
lean_ctor_set(x_308, 6, x_289);
lean_ctor_set(x_308, 7, x_290);
lean_ctor_set(x_308, 8, x_291);
lean_ctor_set(x_308, 9, x_292);
lean_ctor_set_uint8(x_308, sizeof(void*)*10 + 4, x_293);
lean_ctor_set_uint8(x_308, sizeof(void*)*10 + 5, x_294);
lean_ctor_set_uint8(x_308, sizeof(void*)*10 + 6, x_295);
lean_ctor_set_uint32(x_308, sizeof(void*)*10, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*10 + 7, x_307);
x_309 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_282);
lean_ctor_set(x_309, 2, x_283);
x_3 = x_231;
x_4 = x_309;
x_5 = x_232;
goto _start;
}
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_222);
if (x_324 == 0)
{
return x_222;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_222, 0);
x_326 = lean_ctor_get(x_222, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_222);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
case 3:
{
lean_object* x_328; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_328 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_330; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_328);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_328, 0);
lean_dec(x_331);
x_332 = lean_box(0);
lean_ctor_set(x_328, 0, x_332);
return x_328;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
lean_dec(x_328);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_336 = lean_ctor_get(x_328, 1);
lean_inc(x_336);
lean_dec(x_328);
x_337 = lean_ctor_get(x_329, 0);
lean_inc(x_337);
lean_dec(x_329);
x_418 = lean_ctor_get(x_4, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec(x_418);
x_420 = lean_ctor_get(x_419, 3);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 4);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_nat_dec_eq(x_420, x_421);
lean_dec(x_421);
lean_dec(x_420);
if (x_422 == 0)
{
x_338 = x_336;
goto block_417;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_424 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_423, x_4, x_336);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec(x_424);
x_338 = x_425;
goto block_417;
}
else
{
uint8_t x_426; 
lean_dec(x_337);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_424);
if (x_426 == 0)
{
return x_424;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_424, 0);
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_424);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
block_417:
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_4, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = !lean_is_exclusive(x_4);
if (x_341 == 0)
{
lean_object* x_342; uint8_t x_343; 
x_342 = lean_ctor_get(x_4, 0);
lean_dec(x_342);
x_343 = !lean_is_exclusive(x_339);
if (x_343 == 0)
{
lean_object* x_344; uint8_t x_345; 
x_344 = lean_ctor_get(x_339, 0);
lean_dec(x_344);
x_345 = !lean_is_exclusive(x_340);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; uint32_t x_349; uint8_t x_350; 
x_346 = lean_ctor_get(x_340, 3);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_nat_add(x_346, x_347);
lean_dec(x_346);
lean_ctor_set(x_340, 3, x_348);
x_349 = 0;
x_350 = 0;
lean_ctor_set_uint32(x_339, sizeof(void*)*10, x_349);
lean_ctor_set_uint8(x_339, sizeof(void*)*10 + 7, x_350);
x_3 = x_337;
x_5 = x_338;
goto _start;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint32_t x_360; uint8_t x_361; 
x_352 = lean_ctor_get(x_340, 0);
x_353 = lean_ctor_get(x_340, 1);
x_354 = lean_ctor_get(x_340, 2);
x_355 = lean_ctor_get(x_340, 3);
x_356 = lean_ctor_get(x_340, 4);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_340);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_nat_add(x_355, x_357);
lean_dec(x_355);
x_359 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_359, 1, x_353);
lean_ctor_set(x_359, 2, x_354);
lean_ctor_set(x_359, 3, x_358);
lean_ctor_set(x_359, 4, x_356);
x_360 = 0;
x_361 = 0;
lean_ctor_set(x_339, 0, x_359);
lean_ctor_set_uint32(x_339, sizeof(void*)*10, x_360);
lean_ctor_set_uint8(x_339, sizeof(void*)*10 + 7, x_361);
x_3 = x_337;
x_5 = x_338;
goto _start;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint32_t x_384; uint8_t x_385; lean_object* x_386; 
x_363 = lean_ctor_get(x_339, 1);
x_364 = lean_ctor_get(x_339, 2);
x_365 = lean_ctor_get(x_339, 3);
x_366 = lean_ctor_get(x_339, 4);
x_367 = lean_ctor_get(x_339, 5);
x_368 = lean_ctor_get(x_339, 6);
x_369 = lean_ctor_get(x_339, 7);
x_370 = lean_ctor_get(x_339, 8);
x_371 = lean_ctor_get(x_339, 9);
x_372 = lean_ctor_get_uint8(x_339, sizeof(void*)*10 + 4);
x_373 = lean_ctor_get_uint8(x_339, sizeof(void*)*10 + 5);
x_374 = lean_ctor_get_uint8(x_339, sizeof(void*)*10 + 6);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_339);
x_375 = lean_ctor_get(x_340, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_340, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_340, 2);
lean_inc(x_377);
x_378 = lean_ctor_get(x_340, 3);
lean_inc(x_378);
x_379 = lean_ctor_get(x_340, 4);
lean_inc(x_379);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 x_380 = x_340;
} else {
 lean_dec_ref(x_340);
 x_380 = lean_box(0);
}
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_378, x_381);
lean_dec(x_378);
if (lean_is_scalar(x_380)) {
 x_383 = lean_alloc_ctor(0, 5, 0);
} else {
 x_383 = x_380;
}
lean_ctor_set(x_383, 0, x_375);
lean_ctor_set(x_383, 1, x_376);
lean_ctor_set(x_383, 2, x_377);
lean_ctor_set(x_383, 3, x_382);
lean_ctor_set(x_383, 4, x_379);
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_363);
lean_ctor_set(x_386, 2, x_364);
lean_ctor_set(x_386, 3, x_365);
lean_ctor_set(x_386, 4, x_366);
lean_ctor_set(x_386, 5, x_367);
lean_ctor_set(x_386, 6, x_368);
lean_ctor_set(x_386, 7, x_369);
lean_ctor_set(x_386, 8, x_370);
lean_ctor_set(x_386, 9, x_371);
lean_ctor_set_uint8(x_386, sizeof(void*)*10 + 4, x_372);
lean_ctor_set_uint8(x_386, sizeof(void*)*10 + 5, x_373);
lean_ctor_set_uint8(x_386, sizeof(void*)*10 + 6, x_374);
lean_ctor_set_uint32(x_386, sizeof(void*)*10, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*10 + 7, x_385);
lean_ctor_set(x_4, 0, x_386);
x_3 = x_337;
x_5 = x_338;
goto _start;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint32_t x_412; uint8_t x_413; lean_object* x_414; lean_object* x_415; 
x_388 = lean_ctor_get(x_4, 1);
x_389 = lean_ctor_get(x_4, 2);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_4);
x_390 = lean_ctor_get(x_339, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_339, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_339, 3);
lean_inc(x_392);
x_393 = lean_ctor_get(x_339, 4);
lean_inc(x_393);
x_394 = lean_ctor_get(x_339, 5);
lean_inc(x_394);
x_395 = lean_ctor_get(x_339, 6);
lean_inc(x_395);
x_396 = lean_ctor_get(x_339, 7);
lean_inc(x_396);
x_397 = lean_ctor_get(x_339, 8);
lean_inc(x_397);
x_398 = lean_ctor_get(x_339, 9);
lean_inc(x_398);
x_399 = lean_ctor_get_uint8(x_339, sizeof(void*)*10 + 4);
x_400 = lean_ctor_get_uint8(x_339, sizeof(void*)*10 + 5);
x_401 = lean_ctor_get_uint8(x_339, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 lean_ctor_release(x_339, 4);
 lean_ctor_release(x_339, 5);
 lean_ctor_release(x_339, 6);
 lean_ctor_release(x_339, 7);
 lean_ctor_release(x_339, 8);
 lean_ctor_release(x_339, 9);
 x_402 = x_339;
} else {
 lean_dec_ref(x_339);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_340, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_340, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_340, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_340, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_340, 4);
lean_inc(x_407);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 x_408 = x_340;
} else {
 lean_dec_ref(x_340);
 x_408 = lean_box(0);
}
x_409 = lean_unsigned_to_nat(1u);
x_410 = lean_nat_add(x_406, x_409);
lean_dec(x_406);
if (lean_is_scalar(x_408)) {
 x_411 = lean_alloc_ctor(0, 5, 0);
} else {
 x_411 = x_408;
}
lean_ctor_set(x_411, 0, x_403);
lean_ctor_set(x_411, 1, x_404);
lean_ctor_set(x_411, 2, x_405);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set(x_411, 4, x_407);
x_412 = 0;
x_413 = 0;
if (lean_is_scalar(x_402)) {
 x_414 = lean_alloc_ctor(0, 10, 8);
} else {
 x_414 = x_402;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_390);
lean_ctor_set(x_414, 2, x_391);
lean_ctor_set(x_414, 3, x_392);
lean_ctor_set(x_414, 4, x_393);
lean_ctor_set(x_414, 5, x_394);
lean_ctor_set(x_414, 6, x_395);
lean_ctor_set(x_414, 7, x_396);
lean_ctor_set(x_414, 8, x_397);
lean_ctor_set(x_414, 9, x_398);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 4, x_399);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 5, x_400);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 6, x_401);
lean_ctor_set_uint32(x_414, sizeof(void*)*10, x_412);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 7, x_413);
x_415 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_388);
lean_ctor_set(x_415, 2, x_389);
x_3 = x_337;
x_4 = x_415;
x_5 = x_338;
goto _start;
}
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_328);
if (x_430 == 0)
{
return x_328;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_328, 0);
x_432 = lean_ctor_get(x_328, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_328);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
case 4:
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_434 = lean_ctor_get(x_9, 0);
lean_inc(x_434);
lean_dec(x_9);
lean_inc(x_2);
x_435 = l_Lean_Name_append___main(x_434, x_2);
lean_dec(x_434);
x_436 = l_Lean_Elab_Tactic_getEnv___rarg(x_8);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
lean_inc(x_435);
x_439 = lean_environment_find(x_437, x_435);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
lean_dec(x_435);
lean_inc(x_4);
lean_inc(x_1);
x_440 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_438);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_obj_tag(x_441) == 0)
{
uint8_t x_442; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_442 = !lean_is_exclusive(x_440);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_440, 0);
lean_dec(x_443);
x_444 = lean_box(0);
lean_ctor_set(x_440, 0, x_444);
return x_440;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_440, 1);
lean_inc(x_445);
lean_dec(x_440);
x_446 = lean_box(0);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_448 = lean_ctor_get(x_440, 1);
lean_inc(x_448);
lean_dec(x_440);
x_449 = lean_ctor_get(x_441, 0);
lean_inc(x_449);
lean_dec(x_441);
x_530 = lean_ctor_get(x_4, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
lean_dec(x_530);
x_532 = lean_ctor_get(x_531, 3);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 4);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_nat_dec_eq(x_532, x_533);
lean_dec(x_533);
lean_dec(x_532);
if (x_534 == 0)
{
x_450 = x_448;
goto block_529;
}
else
{
lean_object* x_535; lean_object* x_536; 
x_535 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_536 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_535, x_4, x_448);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; 
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
lean_dec(x_536);
x_450 = x_537;
goto block_529;
}
else
{
uint8_t x_538; 
lean_dec(x_449);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_538 = !lean_is_exclusive(x_536);
if (x_538 == 0)
{
return x_536;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_536, 0);
x_540 = lean_ctor_get(x_536, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_536);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
block_529:
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_451 = lean_ctor_get(x_4, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = !lean_is_exclusive(x_4);
if (x_453 == 0)
{
lean_object* x_454; uint8_t x_455; 
x_454 = lean_ctor_get(x_4, 0);
lean_dec(x_454);
x_455 = !lean_is_exclusive(x_451);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; 
x_456 = lean_ctor_get(x_451, 0);
lean_dec(x_456);
x_457 = !lean_is_exclusive(x_452);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint32_t x_461; uint8_t x_462; 
x_458 = lean_ctor_get(x_452, 3);
x_459 = lean_unsigned_to_nat(1u);
x_460 = lean_nat_add(x_458, x_459);
lean_dec(x_458);
lean_ctor_set(x_452, 3, x_460);
x_461 = 0;
x_462 = 0;
lean_ctor_set_uint32(x_451, sizeof(void*)*10, x_461);
lean_ctor_set_uint8(x_451, sizeof(void*)*10 + 7, x_462);
x_3 = x_449;
x_5 = x_450;
goto _start;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint32_t x_472; uint8_t x_473; 
x_464 = lean_ctor_get(x_452, 0);
x_465 = lean_ctor_get(x_452, 1);
x_466 = lean_ctor_get(x_452, 2);
x_467 = lean_ctor_get(x_452, 3);
x_468 = lean_ctor_get(x_452, 4);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_452);
x_469 = lean_unsigned_to_nat(1u);
x_470 = lean_nat_add(x_467, x_469);
lean_dec(x_467);
x_471 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_471, 0, x_464);
lean_ctor_set(x_471, 1, x_465);
lean_ctor_set(x_471, 2, x_466);
lean_ctor_set(x_471, 3, x_470);
lean_ctor_set(x_471, 4, x_468);
x_472 = 0;
x_473 = 0;
lean_ctor_set(x_451, 0, x_471);
lean_ctor_set_uint32(x_451, sizeof(void*)*10, x_472);
lean_ctor_set_uint8(x_451, sizeof(void*)*10 + 7, x_473);
x_3 = x_449;
x_5 = x_450;
goto _start;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; uint8_t x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint32_t x_496; uint8_t x_497; lean_object* x_498; 
x_475 = lean_ctor_get(x_451, 1);
x_476 = lean_ctor_get(x_451, 2);
x_477 = lean_ctor_get(x_451, 3);
x_478 = lean_ctor_get(x_451, 4);
x_479 = lean_ctor_get(x_451, 5);
x_480 = lean_ctor_get(x_451, 6);
x_481 = lean_ctor_get(x_451, 7);
x_482 = lean_ctor_get(x_451, 8);
x_483 = lean_ctor_get(x_451, 9);
x_484 = lean_ctor_get_uint8(x_451, sizeof(void*)*10 + 4);
x_485 = lean_ctor_get_uint8(x_451, sizeof(void*)*10 + 5);
x_486 = lean_ctor_get_uint8(x_451, sizeof(void*)*10 + 6);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_451);
x_487 = lean_ctor_get(x_452, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_452, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_452, 2);
lean_inc(x_489);
x_490 = lean_ctor_get(x_452, 3);
lean_inc(x_490);
x_491 = lean_ctor_get(x_452, 4);
lean_inc(x_491);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 lean_ctor_release(x_452, 3);
 lean_ctor_release(x_452, 4);
 x_492 = x_452;
} else {
 lean_dec_ref(x_452);
 x_492 = lean_box(0);
}
x_493 = lean_unsigned_to_nat(1u);
x_494 = lean_nat_add(x_490, x_493);
lean_dec(x_490);
if (lean_is_scalar(x_492)) {
 x_495 = lean_alloc_ctor(0, 5, 0);
} else {
 x_495 = x_492;
}
lean_ctor_set(x_495, 0, x_487);
lean_ctor_set(x_495, 1, x_488);
lean_ctor_set(x_495, 2, x_489);
lean_ctor_set(x_495, 3, x_494);
lean_ctor_set(x_495, 4, x_491);
x_496 = 0;
x_497 = 0;
x_498 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_475);
lean_ctor_set(x_498, 2, x_476);
lean_ctor_set(x_498, 3, x_477);
lean_ctor_set(x_498, 4, x_478);
lean_ctor_set(x_498, 5, x_479);
lean_ctor_set(x_498, 6, x_480);
lean_ctor_set(x_498, 7, x_481);
lean_ctor_set(x_498, 8, x_482);
lean_ctor_set(x_498, 9, x_483);
lean_ctor_set_uint8(x_498, sizeof(void*)*10 + 4, x_484);
lean_ctor_set_uint8(x_498, sizeof(void*)*10 + 5, x_485);
lean_ctor_set_uint8(x_498, sizeof(void*)*10 + 6, x_486);
lean_ctor_set_uint32(x_498, sizeof(void*)*10, x_496);
lean_ctor_set_uint8(x_498, sizeof(void*)*10 + 7, x_497);
lean_ctor_set(x_4, 0, x_498);
x_3 = x_449;
x_5 = x_450;
goto _start;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; uint8_t x_512; uint8_t x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint32_t x_524; uint8_t x_525; lean_object* x_526; lean_object* x_527; 
x_500 = lean_ctor_get(x_4, 1);
x_501 = lean_ctor_get(x_4, 2);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_4);
x_502 = lean_ctor_get(x_451, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_451, 2);
lean_inc(x_503);
x_504 = lean_ctor_get(x_451, 3);
lean_inc(x_504);
x_505 = lean_ctor_get(x_451, 4);
lean_inc(x_505);
x_506 = lean_ctor_get(x_451, 5);
lean_inc(x_506);
x_507 = lean_ctor_get(x_451, 6);
lean_inc(x_507);
x_508 = lean_ctor_get(x_451, 7);
lean_inc(x_508);
x_509 = lean_ctor_get(x_451, 8);
lean_inc(x_509);
x_510 = lean_ctor_get(x_451, 9);
lean_inc(x_510);
x_511 = lean_ctor_get_uint8(x_451, sizeof(void*)*10 + 4);
x_512 = lean_ctor_get_uint8(x_451, sizeof(void*)*10 + 5);
x_513 = lean_ctor_get_uint8(x_451, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 lean_ctor_release(x_451, 2);
 lean_ctor_release(x_451, 3);
 lean_ctor_release(x_451, 4);
 lean_ctor_release(x_451, 5);
 lean_ctor_release(x_451, 6);
 lean_ctor_release(x_451, 7);
 lean_ctor_release(x_451, 8);
 lean_ctor_release(x_451, 9);
 x_514 = x_451;
} else {
 lean_dec_ref(x_451);
 x_514 = lean_box(0);
}
x_515 = lean_ctor_get(x_452, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_452, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_452, 2);
lean_inc(x_517);
x_518 = lean_ctor_get(x_452, 3);
lean_inc(x_518);
x_519 = lean_ctor_get(x_452, 4);
lean_inc(x_519);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 lean_ctor_release(x_452, 3);
 lean_ctor_release(x_452, 4);
 x_520 = x_452;
} else {
 lean_dec_ref(x_452);
 x_520 = lean_box(0);
}
x_521 = lean_unsigned_to_nat(1u);
x_522 = lean_nat_add(x_518, x_521);
lean_dec(x_518);
if (lean_is_scalar(x_520)) {
 x_523 = lean_alloc_ctor(0, 5, 0);
} else {
 x_523 = x_520;
}
lean_ctor_set(x_523, 0, x_515);
lean_ctor_set(x_523, 1, x_516);
lean_ctor_set(x_523, 2, x_517);
lean_ctor_set(x_523, 3, x_522);
lean_ctor_set(x_523, 4, x_519);
x_524 = 0;
x_525 = 0;
if (lean_is_scalar(x_514)) {
 x_526 = lean_alloc_ctor(0, 10, 8);
} else {
 x_526 = x_514;
}
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_502);
lean_ctor_set(x_526, 2, x_503);
lean_ctor_set(x_526, 3, x_504);
lean_ctor_set(x_526, 4, x_505);
lean_ctor_set(x_526, 5, x_506);
lean_ctor_set(x_526, 6, x_507);
lean_ctor_set(x_526, 7, x_508);
lean_ctor_set(x_526, 8, x_509);
lean_ctor_set(x_526, 9, x_510);
lean_ctor_set_uint8(x_526, sizeof(void*)*10 + 4, x_511);
lean_ctor_set_uint8(x_526, sizeof(void*)*10 + 5, x_512);
lean_ctor_set_uint8(x_526, sizeof(void*)*10 + 6, x_513);
lean_ctor_set_uint32(x_526, sizeof(void*)*10, x_524);
lean_ctor_set_uint8(x_526, sizeof(void*)*10 + 7, x_525);
x_527 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_500);
lean_ctor_set(x_527, 2, x_501);
x_3 = x_449;
x_4 = x_527;
x_5 = x_450;
goto _start;
}
}
}
}
else
{
uint8_t x_542; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_542 = !lean_is_exclusive(x_440);
if (x_542 == 0)
{
return x_440;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_440, 0);
x_544 = lean_ctor_get(x_440, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_440);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_656; 
lean_dec(x_439);
x_546 = l_Lean_Elab_Tactic_save(x_438);
lean_inc(x_4);
lean_inc(x_1);
x_656 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_4, x_438);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = lean_ctor_get(x_657, 0);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_box(0);
x_661 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_661, 0, x_435);
lean_closure_set(x_661, 1, x_660);
x_662 = l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_663 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_663, 0, x_661);
lean_closure_set(x_663, 1, x_662);
lean_inc(x_1);
x_664 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_664, 0, x_1);
lean_closure_set(x_664, 1, x_663);
lean_inc(x_4);
x_665 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_659, x_664, x_4, x_658);
lean_dec(x_659);
if (lean_obj_tag(x_665) == 0)
{
lean_dec(x_546);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_665;
}
else
{
lean_object* x_666; 
x_666 = lean_ctor_get(x_665, 1);
lean_inc(x_666);
lean_dec(x_665);
x_547 = x_666;
goto block_655;
}
}
else
{
lean_object* x_667; 
lean_dec(x_435);
x_667 = lean_ctor_get(x_656, 1);
lean_inc(x_667);
lean_dec(x_656);
x_547 = x_667;
goto block_655;
}
block_655:
{
lean_object* x_548; lean_object* x_549; 
x_548 = l_Lean_Elab_Tactic_restore(x_547, x_546);
lean_dec(x_546);
lean_inc(x_4);
lean_inc(x_1);
x_549 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_548);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
if (lean_obj_tag(x_550) == 0)
{
uint8_t x_551; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_551 = !lean_is_exclusive(x_549);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_549, 0);
lean_dec(x_552);
x_553 = lean_box(0);
lean_ctor_set(x_549, 0, x_553);
return x_549;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_549, 1);
lean_inc(x_554);
lean_dec(x_549);
x_555 = lean_box(0);
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_554);
return x_556;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; 
x_557 = lean_ctor_get(x_549, 1);
lean_inc(x_557);
lean_dec(x_549);
x_558 = lean_ctor_get(x_550, 0);
lean_inc(x_558);
lean_dec(x_550);
x_639 = lean_ctor_get(x_4, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
lean_dec(x_639);
x_641 = lean_ctor_get(x_640, 3);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 4);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_nat_dec_eq(x_641, x_642);
lean_dec(x_642);
lean_dec(x_641);
if (x_643 == 0)
{
x_559 = x_557;
goto block_638;
}
else
{
lean_object* x_644; lean_object* x_645; 
x_644 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_645 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_644, x_4, x_557);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; 
x_646 = lean_ctor_get(x_645, 1);
lean_inc(x_646);
lean_dec(x_645);
x_559 = x_646;
goto block_638;
}
else
{
uint8_t x_647; 
lean_dec(x_558);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_645);
if (x_647 == 0)
{
return x_645;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_645, 0);
x_649 = lean_ctor_get(x_645, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_645);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
block_638:
{
lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_560 = lean_ctor_get(x_4, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = !lean_is_exclusive(x_4);
if (x_562 == 0)
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_ctor_get(x_4, 0);
lean_dec(x_563);
x_564 = !lean_is_exclusive(x_560);
if (x_564 == 0)
{
lean_object* x_565; uint8_t x_566; 
x_565 = lean_ctor_get(x_560, 0);
lean_dec(x_565);
x_566 = !lean_is_exclusive(x_561);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint32_t x_570; uint8_t x_571; 
x_567 = lean_ctor_get(x_561, 3);
x_568 = lean_unsigned_to_nat(1u);
x_569 = lean_nat_add(x_567, x_568);
lean_dec(x_567);
lean_ctor_set(x_561, 3, x_569);
x_570 = 0;
x_571 = 0;
lean_ctor_set_uint32(x_560, sizeof(void*)*10, x_570);
lean_ctor_set_uint8(x_560, sizeof(void*)*10 + 7, x_571);
x_3 = x_558;
x_5 = x_559;
goto _start;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint32_t x_581; uint8_t x_582; 
x_573 = lean_ctor_get(x_561, 0);
x_574 = lean_ctor_get(x_561, 1);
x_575 = lean_ctor_get(x_561, 2);
x_576 = lean_ctor_get(x_561, 3);
x_577 = lean_ctor_get(x_561, 4);
lean_inc(x_577);
lean_inc(x_576);
lean_inc(x_575);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_561);
x_578 = lean_unsigned_to_nat(1u);
x_579 = lean_nat_add(x_576, x_578);
lean_dec(x_576);
x_580 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_580, 0, x_573);
lean_ctor_set(x_580, 1, x_574);
lean_ctor_set(x_580, 2, x_575);
lean_ctor_set(x_580, 3, x_579);
lean_ctor_set(x_580, 4, x_577);
x_581 = 0;
x_582 = 0;
lean_ctor_set(x_560, 0, x_580);
lean_ctor_set_uint32(x_560, sizeof(void*)*10, x_581);
lean_ctor_set_uint8(x_560, sizeof(void*)*10 + 7, x_582);
x_3 = x_558;
x_5 = x_559;
goto _start;
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; uint8_t x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint32_t x_605; uint8_t x_606; lean_object* x_607; 
x_584 = lean_ctor_get(x_560, 1);
x_585 = lean_ctor_get(x_560, 2);
x_586 = lean_ctor_get(x_560, 3);
x_587 = lean_ctor_get(x_560, 4);
x_588 = lean_ctor_get(x_560, 5);
x_589 = lean_ctor_get(x_560, 6);
x_590 = lean_ctor_get(x_560, 7);
x_591 = lean_ctor_get(x_560, 8);
x_592 = lean_ctor_get(x_560, 9);
x_593 = lean_ctor_get_uint8(x_560, sizeof(void*)*10 + 4);
x_594 = lean_ctor_get_uint8(x_560, sizeof(void*)*10 + 5);
x_595 = lean_ctor_get_uint8(x_560, sizeof(void*)*10 + 6);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_587);
lean_inc(x_586);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_560);
x_596 = lean_ctor_get(x_561, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_561, 1);
lean_inc(x_597);
x_598 = lean_ctor_get(x_561, 2);
lean_inc(x_598);
x_599 = lean_ctor_get(x_561, 3);
lean_inc(x_599);
x_600 = lean_ctor_get(x_561, 4);
lean_inc(x_600);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 lean_ctor_release(x_561, 2);
 lean_ctor_release(x_561, 3);
 lean_ctor_release(x_561, 4);
 x_601 = x_561;
} else {
 lean_dec_ref(x_561);
 x_601 = lean_box(0);
}
x_602 = lean_unsigned_to_nat(1u);
x_603 = lean_nat_add(x_599, x_602);
lean_dec(x_599);
if (lean_is_scalar(x_601)) {
 x_604 = lean_alloc_ctor(0, 5, 0);
} else {
 x_604 = x_601;
}
lean_ctor_set(x_604, 0, x_596);
lean_ctor_set(x_604, 1, x_597);
lean_ctor_set(x_604, 2, x_598);
lean_ctor_set(x_604, 3, x_603);
lean_ctor_set(x_604, 4, x_600);
x_605 = 0;
x_606 = 0;
x_607 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_584);
lean_ctor_set(x_607, 2, x_585);
lean_ctor_set(x_607, 3, x_586);
lean_ctor_set(x_607, 4, x_587);
lean_ctor_set(x_607, 5, x_588);
lean_ctor_set(x_607, 6, x_589);
lean_ctor_set(x_607, 7, x_590);
lean_ctor_set(x_607, 8, x_591);
lean_ctor_set(x_607, 9, x_592);
lean_ctor_set_uint8(x_607, sizeof(void*)*10 + 4, x_593);
lean_ctor_set_uint8(x_607, sizeof(void*)*10 + 5, x_594);
lean_ctor_set_uint8(x_607, sizeof(void*)*10 + 6, x_595);
lean_ctor_set_uint32(x_607, sizeof(void*)*10, x_605);
lean_ctor_set_uint8(x_607, sizeof(void*)*10 + 7, x_606);
lean_ctor_set(x_4, 0, x_607);
x_3 = x_558;
x_5 = x_559;
goto _start;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; uint8_t x_621; uint8_t x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint32_t x_633; uint8_t x_634; lean_object* x_635; lean_object* x_636; 
x_609 = lean_ctor_get(x_4, 1);
x_610 = lean_ctor_get(x_4, 2);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_4);
x_611 = lean_ctor_get(x_560, 1);
lean_inc(x_611);
x_612 = lean_ctor_get(x_560, 2);
lean_inc(x_612);
x_613 = lean_ctor_get(x_560, 3);
lean_inc(x_613);
x_614 = lean_ctor_get(x_560, 4);
lean_inc(x_614);
x_615 = lean_ctor_get(x_560, 5);
lean_inc(x_615);
x_616 = lean_ctor_get(x_560, 6);
lean_inc(x_616);
x_617 = lean_ctor_get(x_560, 7);
lean_inc(x_617);
x_618 = lean_ctor_get(x_560, 8);
lean_inc(x_618);
x_619 = lean_ctor_get(x_560, 9);
lean_inc(x_619);
x_620 = lean_ctor_get_uint8(x_560, sizeof(void*)*10 + 4);
x_621 = lean_ctor_get_uint8(x_560, sizeof(void*)*10 + 5);
x_622 = lean_ctor_get_uint8(x_560, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 lean_ctor_release(x_560, 2);
 lean_ctor_release(x_560, 3);
 lean_ctor_release(x_560, 4);
 lean_ctor_release(x_560, 5);
 lean_ctor_release(x_560, 6);
 lean_ctor_release(x_560, 7);
 lean_ctor_release(x_560, 8);
 lean_ctor_release(x_560, 9);
 x_623 = x_560;
} else {
 lean_dec_ref(x_560);
 x_623 = lean_box(0);
}
x_624 = lean_ctor_get(x_561, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_561, 1);
lean_inc(x_625);
x_626 = lean_ctor_get(x_561, 2);
lean_inc(x_626);
x_627 = lean_ctor_get(x_561, 3);
lean_inc(x_627);
x_628 = lean_ctor_get(x_561, 4);
lean_inc(x_628);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 lean_ctor_release(x_561, 2);
 lean_ctor_release(x_561, 3);
 lean_ctor_release(x_561, 4);
 x_629 = x_561;
} else {
 lean_dec_ref(x_561);
 x_629 = lean_box(0);
}
x_630 = lean_unsigned_to_nat(1u);
x_631 = lean_nat_add(x_627, x_630);
lean_dec(x_627);
if (lean_is_scalar(x_629)) {
 x_632 = lean_alloc_ctor(0, 5, 0);
} else {
 x_632 = x_629;
}
lean_ctor_set(x_632, 0, x_624);
lean_ctor_set(x_632, 1, x_625);
lean_ctor_set(x_632, 2, x_626);
lean_ctor_set(x_632, 3, x_631);
lean_ctor_set(x_632, 4, x_628);
x_633 = 0;
x_634 = 0;
if (lean_is_scalar(x_623)) {
 x_635 = lean_alloc_ctor(0, 10, 8);
} else {
 x_635 = x_623;
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_611);
lean_ctor_set(x_635, 2, x_612);
lean_ctor_set(x_635, 3, x_613);
lean_ctor_set(x_635, 4, x_614);
lean_ctor_set(x_635, 5, x_615);
lean_ctor_set(x_635, 6, x_616);
lean_ctor_set(x_635, 7, x_617);
lean_ctor_set(x_635, 8, x_618);
lean_ctor_set(x_635, 9, x_619);
lean_ctor_set_uint8(x_635, sizeof(void*)*10 + 4, x_620);
lean_ctor_set_uint8(x_635, sizeof(void*)*10 + 5, x_621);
lean_ctor_set_uint8(x_635, sizeof(void*)*10 + 6, x_622);
lean_ctor_set_uint32(x_635, sizeof(void*)*10, x_633);
lean_ctor_set_uint8(x_635, sizeof(void*)*10 + 7, x_634);
x_636 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_609);
lean_ctor_set(x_636, 2, x_610);
x_3 = x_558;
x_4 = x_636;
x_5 = x_559;
goto _start;
}
}
}
}
else
{
uint8_t x_651; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_651 = !lean_is_exclusive(x_549);
if (x_651 == 0)
{
return x_549;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_549, 0);
x_653 = lean_ctor_get(x_549, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_549);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
}
}
case 5:
{
lean_object* x_668; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_668 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
if (lean_obj_tag(x_669) == 0)
{
uint8_t x_670; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_670 = !lean_is_exclusive(x_668);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; 
x_671 = lean_ctor_get(x_668, 0);
lean_dec(x_671);
x_672 = lean_box(0);
lean_ctor_set(x_668, 0, x_672);
return x_668;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_668, 1);
lean_inc(x_673);
lean_dec(x_668);
x_674 = lean_box(0);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_673);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; 
x_676 = lean_ctor_get(x_668, 1);
lean_inc(x_676);
lean_dec(x_668);
x_677 = lean_ctor_get(x_669, 0);
lean_inc(x_677);
lean_dec(x_669);
x_758 = lean_ctor_get(x_4, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
lean_dec(x_758);
x_760 = lean_ctor_get(x_759, 3);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 4);
lean_inc(x_761);
lean_dec(x_759);
x_762 = lean_nat_dec_eq(x_760, x_761);
lean_dec(x_761);
lean_dec(x_760);
if (x_762 == 0)
{
x_678 = x_676;
goto block_757;
}
else
{
lean_object* x_763; lean_object* x_764; 
x_763 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_764 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_763, x_4, x_676);
if (lean_obj_tag(x_764) == 0)
{
lean_object* x_765; 
x_765 = lean_ctor_get(x_764, 1);
lean_inc(x_765);
lean_dec(x_764);
x_678 = x_765;
goto block_757;
}
else
{
uint8_t x_766; 
lean_dec(x_677);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_766 = !lean_is_exclusive(x_764);
if (x_766 == 0)
{
return x_764;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_764, 0);
x_768 = lean_ctor_get(x_764, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_764);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
block_757:
{
lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_679 = lean_ctor_get(x_4, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = !lean_is_exclusive(x_4);
if (x_681 == 0)
{
lean_object* x_682; uint8_t x_683; 
x_682 = lean_ctor_get(x_4, 0);
lean_dec(x_682);
x_683 = !lean_is_exclusive(x_679);
if (x_683 == 0)
{
lean_object* x_684; uint8_t x_685; 
x_684 = lean_ctor_get(x_679, 0);
lean_dec(x_684);
x_685 = !lean_is_exclusive(x_680);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; uint32_t x_689; uint8_t x_690; 
x_686 = lean_ctor_get(x_680, 3);
x_687 = lean_unsigned_to_nat(1u);
x_688 = lean_nat_add(x_686, x_687);
lean_dec(x_686);
lean_ctor_set(x_680, 3, x_688);
x_689 = 0;
x_690 = 0;
lean_ctor_set_uint32(x_679, sizeof(void*)*10, x_689);
lean_ctor_set_uint8(x_679, sizeof(void*)*10 + 7, x_690);
x_3 = x_677;
x_5 = x_678;
goto _start;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; uint32_t x_700; uint8_t x_701; 
x_692 = lean_ctor_get(x_680, 0);
x_693 = lean_ctor_get(x_680, 1);
x_694 = lean_ctor_get(x_680, 2);
x_695 = lean_ctor_get(x_680, 3);
x_696 = lean_ctor_get(x_680, 4);
lean_inc(x_696);
lean_inc(x_695);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
lean_dec(x_680);
x_697 = lean_unsigned_to_nat(1u);
x_698 = lean_nat_add(x_695, x_697);
lean_dec(x_695);
x_699 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_699, 0, x_692);
lean_ctor_set(x_699, 1, x_693);
lean_ctor_set(x_699, 2, x_694);
lean_ctor_set(x_699, 3, x_698);
lean_ctor_set(x_699, 4, x_696);
x_700 = 0;
x_701 = 0;
lean_ctor_set(x_679, 0, x_699);
lean_ctor_set_uint32(x_679, sizeof(void*)*10, x_700);
lean_ctor_set_uint8(x_679, sizeof(void*)*10 + 7, x_701);
x_3 = x_677;
x_5 = x_678;
goto _start;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; uint8_t x_712; uint8_t x_713; uint8_t x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; uint32_t x_724; uint8_t x_725; lean_object* x_726; 
x_703 = lean_ctor_get(x_679, 1);
x_704 = lean_ctor_get(x_679, 2);
x_705 = lean_ctor_get(x_679, 3);
x_706 = lean_ctor_get(x_679, 4);
x_707 = lean_ctor_get(x_679, 5);
x_708 = lean_ctor_get(x_679, 6);
x_709 = lean_ctor_get(x_679, 7);
x_710 = lean_ctor_get(x_679, 8);
x_711 = lean_ctor_get(x_679, 9);
x_712 = lean_ctor_get_uint8(x_679, sizeof(void*)*10 + 4);
x_713 = lean_ctor_get_uint8(x_679, sizeof(void*)*10 + 5);
x_714 = lean_ctor_get_uint8(x_679, sizeof(void*)*10 + 6);
lean_inc(x_711);
lean_inc(x_710);
lean_inc(x_709);
lean_inc(x_708);
lean_inc(x_707);
lean_inc(x_706);
lean_inc(x_705);
lean_inc(x_704);
lean_inc(x_703);
lean_dec(x_679);
x_715 = lean_ctor_get(x_680, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_680, 1);
lean_inc(x_716);
x_717 = lean_ctor_get(x_680, 2);
lean_inc(x_717);
x_718 = lean_ctor_get(x_680, 3);
lean_inc(x_718);
x_719 = lean_ctor_get(x_680, 4);
lean_inc(x_719);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 lean_ctor_release(x_680, 2);
 lean_ctor_release(x_680, 3);
 lean_ctor_release(x_680, 4);
 x_720 = x_680;
} else {
 lean_dec_ref(x_680);
 x_720 = lean_box(0);
}
x_721 = lean_unsigned_to_nat(1u);
x_722 = lean_nat_add(x_718, x_721);
lean_dec(x_718);
if (lean_is_scalar(x_720)) {
 x_723 = lean_alloc_ctor(0, 5, 0);
} else {
 x_723 = x_720;
}
lean_ctor_set(x_723, 0, x_715);
lean_ctor_set(x_723, 1, x_716);
lean_ctor_set(x_723, 2, x_717);
lean_ctor_set(x_723, 3, x_722);
lean_ctor_set(x_723, 4, x_719);
x_724 = 0;
x_725 = 0;
x_726 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_726, 0, x_723);
lean_ctor_set(x_726, 1, x_703);
lean_ctor_set(x_726, 2, x_704);
lean_ctor_set(x_726, 3, x_705);
lean_ctor_set(x_726, 4, x_706);
lean_ctor_set(x_726, 5, x_707);
lean_ctor_set(x_726, 6, x_708);
lean_ctor_set(x_726, 7, x_709);
lean_ctor_set(x_726, 8, x_710);
lean_ctor_set(x_726, 9, x_711);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 4, x_712);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 5, x_713);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 6, x_714);
lean_ctor_set_uint32(x_726, sizeof(void*)*10, x_724);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 7, x_725);
lean_ctor_set(x_4, 0, x_726);
x_3 = x_677;
x_5 = x_678;
goto _start;
}
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; uint8_t x_740; uint8_t x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; uint32_t x_752; uint8_t x_753; lean_object* x_754; lean_object* x_755; 
x_728 = lean_ctor_get(x_4, 1);
x_729 = lean_ctor_get(x_4, 2);
lean_inc(x_729);
lean_inc(x_728);
lean_dec(x_4);
x_730 = lean_ctor_get(x_679, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_679, 2);
lean_inc(x_731);
x_732 = lean_ctor_get(x_679, 3);
lean_inc(x_732);
x_733 = lean_ctor_get(x_679, 4);
lean_inc(x_733);
x_734 = lean_ctor_get(x_679, 5);
lean_inc(x_734);
x_735 = lean_ctor_get(x_679, 6);
lean_inc(x_735);
x_736 = lean_ctor_get(x_679, 7);
lean_inc(x_736);
x_737 = lean_ctor_get(x_679, 8);
lean_inc(x_737);
x_738 = lean_ctor_get(x_679, 9);
lean_inc(x_738);
x_739 = lean_ctor_get_uint8(x_679, sizeof(void*)*10 + 4);
x_740 = lean_ctor_get_uint8(x_679, sizeof(void*)*10 + 5);
x_741 = lean_ctor_get_uint8(x_679, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 lean_ctor_release(x_679, 4);
 lean_ctor_release(x_679, 5);
 lean_ctor_release(x_679, 6);
 lean_ctor_release(x_679, 7);
 lean_ctor_release(x_679, 8);
 lean_ctor_release(x_679, 9);
 x_742 = x_679;
} else {
 lean_dec_ref(x_679);
 x_742 = lean_box(0);
}
x_743 = lean_ctor_get(x_680, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_680, 1);
lean_inc(x_744);
x_745 = lean_ctor_get(x_680, 2);
lean_inc(x_745);
x_746 = lean_ctor_get(x_680, 3);
lean_inc(x_746);
x_747 = lean_ctor_get(x_680, 4);
lean_inc(x_747);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 lean_ctor_release(x_680, 2);
 lean_ctor_release(x_680, 3);
 lean_ctor_release(x_680, 4);
 x_748 = x_680;
} else {
 lean_dec_ref(x_680);
 x_748 = lean_box(0);
}
x_749 = lean_unsigned_to_nat(1u);
x_750 = lean_nat_add(x_746, x_749);
lean_dec(x_746);
if (lean_is_scalar(x_748)) {
 x_751 = lean_alloc_ctor(0, 5, 0);
} else {
 x_751 = x_748;
}
lean_ctor_set(x_751, 0, x_743);
lean_ctor_set(x_751, 1, x_744);
lean_ctor_set(x_751, 2, x_745);
lean_ctor_set(x_751, 3, x_750);
lean_ctor_set(x_751, 4, x_747);
x_752 = 0;
x_753 = 0;
if (lean_is_scalar(x_742)) {
 x_754 = lean_alloc_ctor(0, 10, 8);
} else {
 x_754 = x_742;
}
lean_ctor_set(x_754, 0, x_751);
lean_ctor_set(x_754, 1, x_730);
lean_ctor_set(x_754, 2, x_731);
lean_ctor_set(x_754, 3, x_732);
lean_ctor_set(x_754, 4, x_733);
lean_ctor_set(x_754, 5, x_734);
lean_ctor_set(x_754, 6, x_735);
lean_ctor_set(x_754, 7, x_736);
lean_ctor_set(x_754, 8, x_737);
lean_ctor_set(x_754, 9, x_738);
lean_ctor_set_uint8(x_754, sizeof(void*)*10 + 4, x_739);
lean_ctor_set_uint8(x_754, sizeof(void*)*10 + 5, x_740);
lean_ctor_set_uint8(x_754, sizeof(void*)*10 + 6, x_741);
lean_ctor_set_uint32(x_754, sizeof(void*)*10, x_752);
lean_ctor_set_uint8(x_754, sizeof(void*)*10 + 7, x_753);
x_755 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_728);
lean_ctor_set(x_755, 2, x_729);
x_3 = x_677;
x_4 = x_755;
x_5 = x_678;
goto _start;
}
}
}
}
else
{
uint8_t x_770; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_770 = !lean_is_exclusive(x_668);
if (x_770 == 0)
{
return x_668;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_668, 0);
x_772 = lean_ctor_get(x_668, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_668);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
case 6:
{
lean_object* x_774; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_774 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
if (lean_obj_tag(x_775) == 0)
{
uint8_t x_776; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_776 = !lean_is_exclusive(x_774);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_ctor_get(x_774, 0);
lean_dec(x_777);
x_778 = lean_box(0);
lean_ctor_set(x_774, 0, x_778);
return x_774;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_774, 1);
lean_inc(x_779);
lean_dec(x_774);
x_780 = lean_box(0);
x_781 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_781, 0, x_780);
lean_ctor_set(x_781, 1, x_779);
return x_781;
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; uint8_t x_868; 
x_782 = lean_ctor_get(x_774, 1);
lean_inc(x_782);
lean_dec(x_774);
x_783 = lean_ctor_get(x_775, 0);
lean_inc(x_783);
lean_dec(x_775);
x_864 = lean_ctor_get(x_4, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
lean_dec(x_864);
x_866 = lean_ctor_get(x_865, 3);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 4);
lean_inc(x_867);
lean_dec(x_865);
x_868 = lean_nat_dec_eq(x_866, x_867);
lean_dec(x_867);
lean_dec(x_866);
if (x_868 == 0)
{
x_784 = x_782;
goto block_863;
}
else
{
lean_object* x_869; lean_object* x_870; 
x_869 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_870 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_869, x_4, x_782);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; 
x_871 = lean_ctor_get(x_870, 1);
lean_inc(x_871);
lean_dec(x_870);
x_784 = x_871;
goto block_863;
}
else
{
uint8_t x_872; 
lean_dec(x_783);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_872 = !lean_is_exclusive(x_870);
if (x_872 == 0)
{
return x_870;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_870, 0);
x_874 = lean_ctor_get(x_870, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_870);
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_875, 1, x_874);
return x_875;
}
}
}
block_863:
{
lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_785 = lean_ctor_get(x_4, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = !lean_is_exclusive(x_4);
if (x_787 == 0)
{
lean_object* x_788; uint8_t x_789; 
x_788 = lean_ctor_get(x_4, 0);
lean_dec(x_788);
x_789 = !lean_is_exclusive(x_785);
if (x_789 == 0)
{
lean_object* x_790; uint8_t x_791; 
x_790 = lean_ctor_get(x_785, 0);
lean_dec(x_790);
x_791 = !lean_is_exclusive(x_786);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; uint32_t x_795; uint8_t x_796; 
x_792 = lean_ctor_get(x_786, 3);
x_793 = lean_unsigned_to_nat(1u);
x_794 = lean_nat_add(x_792, x_793);
lean_dec(x_792);
lean_ctor_set(x_786, 3, x_794);
x_795 = 0;
x_796 = 0;
lean_ctor_set_uint32(x_785, sizeof(void*)*10, x_795);
lean_ctor_set_uint8(x_785, sizeof(void*)*10 + 7, x_796);
x_3 = x_783;
x_5 = x_784;
goto _start;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; uint32_t x_806; uint8_t x_807; 
x_798 = lean_ctor_get(x_786, 0);
x_799 = lean_ctor_get(x_786, 1);
x_800 = lean_ctor_get(x_786, 2);
x_801 = lean_ctor_get(x_786, 3);
x_802 = lean_ctor_get(x_786, 4);
lean_inc(x_802);
lean_inc(x_801);
lean_inc(x_800);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_786);
x_803 = lean_unsigned_to_nat(1u);
x_804 = lean_nat_add(x_801, x_803);
lean_dec(x_801);
x_805 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_805, 0, x_798);
lean_ctor_set(x_805, 1, x_799);
lean_ctor_set(x_805, 2, x_800);
lean_ctor_set(x_805, 3, x_804);
lean_ctor_set(x_805, 4, x_802);
x_806 = 0;
x_807 = 0;
lean_ctor_set(x_785, 0, x_805);
lean_ctor_set_uint32(x_785, sizeof(void*)*10, x_806);
lean_ctor_set_uint8(x_785, sizeof(void*)*10 + 7, x_807);
x_3 = x_783;
x_5 = x_784;
goto _start;
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; uint8_t x_818; uint8_t x_819; uint8_t x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint32_t x_830; uint8_t x_831; lean_object* x_832; 
x_809 = lean_ctor_get(x_785, 1);
x_810 = lean_ctor_get(x_785, 2);
x_811 = lean_ctor_get(x_785, 3);
x_812 = lean_ctor_get(x_785, 4);
x_813 = lean_ctor_get(x_785, 5);
x_814 = lean_ctor_get(x_785, 6);
x_815 = lean_ctor_get(x_785, 7);
x_816 = lean_ctor_get(x_785, 8);
x_817 = lean_ctor_get(x_785, 9);
x_818 = lean_ctor_get_uint8(x_785, sizeof(void*)*10 + 4);
x_819 = lean_ctor_get_uint8(x_785, sizeof(void*)*10 + 5);
x_820 = lean_ctor_get_uint8(x_785, sizeof(void*)*10 + 6);
lean_inc(x_817);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_814);
lean_inc(x_813);
lean_inc(x_812);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_785);
x_821 = lean_ctor_get(x_786, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_786, 1);
lean_inc(x_822);
x_823 = lean_ctor_get(x_786, 2);
lean_inc(x_823);
x_824 = lean_ctor_get(x_786, 3);
lean_inc(x_824);
x_825 = lean_ctor_get(x_786, 4);
lean_inc(x_825);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_826 = x_786;
} else {
 lean_dec_ref(x_786);
 x_826 = lean_box(0);
}
x_827 = lean_unsigned_to_nat(1u);
x_828 = lean_nat_add(x_824, x_827);
lean_dec(x_824);
if (lean_is_scalar(x_826)) {
 x_829 = lean_alloc_ctor(0, 5, 0);
} else {
 x_829 = x_826;
}
lean_ctor_set(x_829, 0, x_821);
lean_ctor_set(x_829, 1, x_822);
lean_ctor_set(x_829, 2, x_823);
lean_ctor_set(x_829, 3, x_828);
lean_ctor_set(x_829, 4, x_825);
x_830 = 0;
x_831 = 0;
x_832 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_809);
lean_ctor_set(x_832, 2, x_810);
lean_ctor_set(x_832, 3, x_811);
lean_ctor_set(x_832, 4, x_812);
lean_ctor_set(x_832, 5, x_813);
lean_ctor_set(x_832, 6, x_814);
lean_ctor_set(x_832, 7, x_815);
lean_ctor_set(x_832, 8, x_816);
lean_ctor_set(x_832, 9, x_817);
lean_ctor_set_uint8(x_832, sizeof(void*)*10 + 4, x_818);
lean_ctor_set_uint8(x_832, sizeof(void*)*10 + 5, x_819);
lean_ctor_set_uint8(x_832, sizeof(void*)*10 + 6, x_820);
lean_ctor_set_uint32(x_832, sizeof(void*)*10, x_830);
lean_ctor_set_uint8(x_832, sizeof(void*)*10 + 7, x_831);
lean_ctor_set(x_4, 0, x_832);
x_3 = x_783;
x_5 = x_784;
goto _start;
}
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; uint8_t x_845; uint8_t x_846; uint8_t x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; uint32_t x_858; uint8_t x_859; lean_object* x_860; lean_object* x_861; 
x_834 = lean_ctor_get(x_4, 1);
x_835 = lean_ctor_get(x_4, 2);
lean_inc(x_835);
lean_inc(x_834);
lean_dec(x_4);
x_836 = lean_ctor_get(x_785, 1);
lean_inc(x_836);
x_837 = lean_ctor_get(x_785, 2);
lean_inc(x_837);
x_838 = lean_ctor_get(x_785, 3);
lean_inc(x_838);
x_839 = lean_ctor_get(x_785, 4);
lean_inc(x_839);
x_840 = lean_ctor_get(x_785, 5);
lean_inc(x_840);
x_841 = lean_ctor_get(x_785, 6);
lean_inc(x_841);
x_842 = lean_ctor_get(x_785, 7);
lean_inc(x_842);
x_843 = lean_ctor_get(x_785, 8);
lean_inc(x_843);
x_844 = lean_ctor_get(x_785, 9);
lean_inc(x_844);
x_845 = lean_ctor_get_uint8(x_785, sizeof(void*)*10 + 4);
x_846 = lean_ctor_get_uint8(x_785, sizeof(void*)*10 + 5);
x_847 = lean_ctor_get_uint8(x_785, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 lean_ctor_release(x_785, 2);
 lean_ctor_release(x_785, 3);
 lean_ctor_release(x_785, 4);
 lean_ctor_release(x_785, 5);
 lean_ctor_release(x_785, 6);
 lean_ctor_release(x_785, 7);
 lean_ctor_release(x_785, 8);
 lean_ctor_release(x_785, 9);
 x_848 = x_785;
} else {
 lean_dec_ref(x_785);
 x_848 = lean_box(0);
}
x_849 = lean_ctor_get(x_786, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_786, 1);
lean_inc(x_850);
x_851 = lean_ctor_get(x_786, 2);
lean_inc(x_851);
x_852 = lean_ctor_get(x_786, 3);
lean_inc(x_852);
x_853 = lean_ctor_get(x_786, 4);
lean_inc(x_853);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 lean_ctor_release(x_786, 2);
 lean_ctor_release(x_786, 3);
 lean_ctor_release(x_786, 4);
 x_854 = x_786;
} else {
 lean_dec_ref(x_786);
 x_854 = lean_box(0);
}
x_855 = lean_unsigned_to_nat(1u);
x_856 = lean_nat_add(x_852, x_855);
lean_dec(x_852);
if (lean_is_scalar(x_854)) {
 x_857 = lean_alloc_ctor(0, 5, 0);
} else {
 x_857 = x_854;
}
lean_ctor_set(x_857, 0, x_849);
lean_ctor_set(x_857, 1, x_850);
lean_ctor_set(x_857, 2, x_851);
lean_ctor_set(x_857, 3, x_856);
lean_ctor_set(x_857, 4, x_853);
x_858 = 0;
x_859 = 0;
if (lean_is_scalar(x_848)) {
 x_860 = lean_alloc_ctor(0, 10, 8);
} else {
 x_860 = x_848;
}
lean_ctor_set(x_860, 0, x_857);
lean_ctor_set(x_860, 1, x_836);
lean_ctor_set(x_860, 2, x_837);
lean_ctor_set(x_860, 3, x_838);
lean_ctor_set(x_860, 4, x_839);
lean_ctor_set(x_860, 5, x_840);
lean_ctor_set(x_860, 6, x_841);
lean_ctor_set(x_860, 7, x_842);
lean_ctor_set(x_860, 8, x_843);
lean_ctor_set(x_860, 9, x_844);
lean_ctor_set_uint8(x_860, sizeof(void*)*10 + 4, x_845);
lean_ctor_set_uint8(x_860, sizeof(void*)*10 + 5, x_846);
lean_ctor_set_uint8(x_860, sizeof(void*)*10 + 6, x_847);
lean_ctor_set_uint32(x_860, sizeof(void*)*10, x_858);
lean_ctor_set_uint8(x_860, sizeof(void*)*10 + 7, x_859);
x_861 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_834);
lean_ctor_set(x_861, 2, x_835);
x_3 = x_783;
x_4 = x_861;
x_5 = x_784;
goto _start;
}
}
}
}
else
{
uint8_t x_876; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_876 = !lean_is_exclusive(x_774);
if (x_876 == 0)
{
return x_774;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_774, 0);
x_878 = lean_ctor_get(x_774, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_774);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
}
}
case 7:
{
lean_object* x_880; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_880 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
if (lean_obj_tag(x_881) == 0)
{
uint8_t x_882; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_882 = !lean_is_exclusive(x_880);
if (x_882 == 0)
{
lean_object* x_883; lean_object* x_884; 
x_883 = lean_ctor_get(x_880, 0);
lean_dec(x_883);
x_884 = lean_box(0);
lean_ctor_set(x_880, 0, x_884);
return x_880;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_885 = lean_ctor_get(x_880, 1);
lean_inc(x_885);
lean_dec(x_880);
x_886 = lean_box(0);
x_887 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_887, 0, x_886);
lean_ctor_set(x_887, 1, x_885);
return x_887;
}
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; uint8_t x_974; 
x_888 = lean_ctor_get(x_880, 1);
lean_inc(x_888);
lean_dec(x_880);
x_889 = lean_ctor_get(x_881, 0);
lean_inc(x_889);
lean_dec(x_881);
x_970 = lean_ctor_get(x_4, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
lean_dec(x_970);
x_972 = lean_ctor_get(x_971, 3);
lean_inc(x_972);
x_973 = lean_ctor_get(x_971, 4);
lean_inc(x_973);
lean_dec(x_971);
x_974 = lean_nat_dec_eq(x_972, x_973);
lean_dec(x_973);
lean_dec(x_972);
if (x_974 == 0)
{
x_890 = x_888;
goto block_969;
}
else
{
lean_object* x_975; lean_object* x_976; 
x_975 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_976 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_975, x_4, x_888);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; 
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
lean_dec(x_976);
x_890 = x_977;
goto block_969;
}
else
{
uint8_t x_978; 
lean_dec(x_889);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_978 = !lean_is_exclusive(x_976);
if (x_978 == 0)
{
return x_976;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_ctor_get(x_976, 0);
x_980 = lean_ctor_get(x_976, 1);
lean_inc(x_980);
lean_inc(x_979);
lean_dec(x_976);
x_981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_981, 0, x_979);
lean_ctor_set(x_981, 1, x_980);
return x_981;
}
}
}
block_969:
{
lean_object* x_891; lean_object* x_892; uint8_t x_893; 
x_891 = lean_ctor_get(x_4, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_891, 0);
lean_inc(x_892);
x_893 = !lean_is_exclusive(x_4);
if (x_893 == 0)
{
lean_object* x_894; uint8_t x_895; 
x_894 = lean_ctor_get(x_4, 0);
lean_dec(x_894);
x_895 = !lean_is_exclusive(x_891);
if (x_895 == 0)
{
lean_object* x_896; uint8_t x_897; 
x_896 = lean_ctor_get(x_891, 0);
lean_dec(x_896);
x_897 = !lean_is_exclusive(x_892);
if (x_897 == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; uint32_t x_901; uint8_t x_902; 
x_898 = lean_ctor_get(x_892, 3);
x_899 = lean_unsigned_to_nat(1u);
x_900 = lean_nat_add(x_898, x_899);
lean_dec(x_898);
lean_ctor_set(x_892, 3, x_900);
x_901 = 0;
x_902 = 0;
lean_ctor_set_uint32(x_891, sizeof(void*)*10, x_901);
lean_ctor_set_uint8(x_891, sizeof(void*)*10 + 7, x_902);
x_3 = x_889;
x_5 = x_890;
goto _start;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint32_t x_912; uint8_t x_913; 
x_904 = lean_ctor_get(x_892, 0);
x_905 = lean_ctor_get(x_892, 1);
x_906 = lean_ctor_get(x_892, 2);
x_907 = lean_ctor_get(x_892, 3);
x_908 = lean_ctor_get(x_892, 4);
lean_inc(x_908);
lean_inc(x_907);
lean_inc(x_906);
lean_inc(x_905);
lean_inc(x_904);
lean_dec(x_892);
x_909 = lean_unsigned_to_nat(1u);
x_910 = lean_nat_add(x_907, x_909);
lean_dec(x_907);
x_911 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_911, 0, x_904);
lean_ctor_set(x_911, 1, x_905);
lean_ctor_set(x_911, 2, x_906);
lean_ctor_set(x_911, 3, x_910);
lean_ctor_set(x_911, 4, x_908);
x_912 = 0;
x_913 = 0;
lean_ctor_set(x_891, 0, x_911);
lean_ctor_set_uint32(x_891, sizeof(void*)*10, x_912);
lean_ctor_set_uint8(x_891, sizeof(void*)*10 + 7, x_913);
x_3 = x_889;
x_5 = x_890;
goto _start;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; uint8_t x_924; uint8_t x_925; uint8_t x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; uint32_t x_936; uint8_t x_937; lean_object* x_938; 
x_915 = lean_ctor_get(x_891, 1);
x_916 = lean_ctor_get(x_891, 2);
x_917 = lean_ctor_get(x_891, 3);
x_918 = lean_ctor_get(x_891, 4);
x_919 = lean_ctor_get(x_891, 5);
x_920 = lean_ctor_get(x_891, 6);
x_921 = lean_ctor_get(x_891, 7);
x_922 = lean_ctor_get(x_891, 8);
x_923 = lean_ctor_get(x_891, 9);
x_924 = lean_ctor_get_uint8(x_891, sizeof(void*)*10 + 4);
x_925 = lean_ctor_get_uint8(x_891, sizeof(void*)*10 + 5);
x_926 = lean_ctor_get_uint8(x_891, sizeof(void*)*10 + 6);
lean_inc(x_923);
lean_inc(x_922);
lean_inc(x_921);
lean_inc(x_920);
lean_inc(x_919);
lean_inc(x_918);
lean_inc(x_917);
lean_inc(x_916);
lean_inc(x_915);
lean_dec(x_891);
x_927 = lean_ctor_get(x_892, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_892, 1);
lean_inc(x_928);
x_929 = lean_ctor_get(x_892, 2);
lean_inc(x_929);
x_930 = lean_ctor_get(x_892, 3);
lean_inc(x_930);
x_931 = lean_ctor_get(x_892, 4);
lean_inc(x_931);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 lean_ctor_release(x_892, 2);
 lean_ctor_release(x_892, 3);
 lean_ctor_release(x_892, 4);
 x_932 = x_892;
} else {
 lean_dec_ref(x_892);
 x_932 = lean_box(0);
}
x_933 = lean_unsigned_to_nat(1u);
x_934 = lean_nat_add(x_930, x_933);
lean_dec(x_930);
if (lean_is_scalar(x_932)) {
 x_935 = lean_alloc_ctor(0, 5, 0);
} else {
 x_935 = x_932;
}
lean_ctor_set(x_935, 0, x_927);
lean_ctor_set(x_935, 1, x_928);
lean_ctor_set(x_935, 2, x_929);
lean_ctor_set(x_935, 3, x_934);
lean_ctor_set(x_935, 4, x_931);
x_936 = 0;
x_937 = 0;
x_938 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_915);
lean_ctor_set(x_938, 2, x_916);
lean_ctor_set(x_938, 3, x_917);
lean_ctor_set(x_938, 4, x_918);
lean_ctor_set(x_938, 5, x_919);
lean_ctor_set(x_938, 6, x_920);
lean_ctor_set(x_938, 7, x_921);
lean_ctor_set(x_938, 8, x_922);
lean_ctor_set(x_938, 9, x_923);
lean_ctor_set_uint8(x_938, sizeof(void*)*10 + 4, x_924);
lean_ctor_set_uint8(x_938, sizeof(void*)*10 + 5, x_925);
lean_ctor_set_uint8(x_938, sizeof(void*)*10 + 6, x_926);
lean_ctor_set_uint32(x_938, sizeof(void*)*10, x_936);
lean_ctor_set_uint8(x_938, sizeof(void*)*10 + 7, x_937);
lean_ctor_set(x_4, 0, x_938);
x_3 = x_889;
x_5 = x_890;
goto _start;
}
}
else
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; uint8_t x_951; uint8_t x_952; uint8_t x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; uint32_t x_964; uint8_t x_965; lean_object* x_966; lean_object* x_967; 
x_940 = lean_ctor_get(x_4, 1);
x_941 = lean_ctor_get(x_4, 2);
lean_inc(x_941);
lean_inc(x_940);
lean_dec(x_4);
x_942 = lean_ctor_get(x_891, 1);
lean_inc(x_942);
x_943 = lean_ctor_get(x_891, 2);
lean_inc(x_943);
x_944 = lean_ctor_get(x_891, 3);
lean_inc(x_944);
x_945 = lean_ctor_get(x_891, 4);
lean_inc(x_945);
x_946 = lean_ctor_get(x_891, 5);
lean_inc(x_946);
x_947 = lean_ctor_get(x_891, 6);
lean_inc(x_947);
x_948 = lean_ctor_get(x_891, 7);
lean_inc(x_948);
x_949 = lean_ctor_get(x_891, 8);
lean_inc(x_949);
x_950 = lean_ctor_get(x_891, 9);
lean_inc(x_950);
x_951 = lean_ctor_get_uint8(x_891, sizeof(void*)*10 + 4);
x_952 = lean_ctor_get_uint8(x_891, sizeof(void*)*10 + 5);
x_953 = lean_ctor_get_uint8(x_891, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_891)) {
 lean_ctor_release(x_891, 0);
 lean_ctor_release(x_891, 1);
 lean_ctor_release(x_891, 2);
 lean_ctor_release(x_891, 3);
 lean_ctor_release(x_891, 4);
 lean_ctor_release(x_891, 5);
 lean_ctor_release(x_891, 6);
 lean_ctor_release(x_891, 7);
 lean_ctor_release(x_891, 8);
 lean_ctor_release(x_891, 9);
 x_954 = x_891;
} else {
 lean_dec_ref(x_891);
 x_954 = lean_box(0);
}
x_955 = lean_ctor_get(x_892, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_892, 1);
lean_inc(x_956);
x_957 = lean_ctor_get(x_892, 2);
lean_inc(x_957);
x_958 = lean_ctor_get(x_892, 3);
lean_inc(x_958);
x_959 = lean_ctor_get(x_892, 4);
lean_inc(x_959);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 lean_ctor_release(x_892, 2);
 lean_ctor_release(x_892, 3);
 lean_ctor_release(x_892, 4);
 x_960 = x_892;
} else {
 lean_dec_ref(x_892);
 x_960 = lean_box(0);
}
x_961 = lean_unsigned_to_nat(1u);
x_962 = lean_nat_add(x_958, x_961);
lean_dec(x_958);
if (lean_is_scalar(x_960)) {
 x_963 = lean_alloc_ctor(0, 5, 0);
} else {
 x_963 = x_960;
}
lean_ctor_set(x_963, 0, x_955);
lean_ctor_set(x_963, 1, x_956);
lean_ctor_set(x_963, 2, x_957);
lean_ctor_set(x_963, 3, x_962);
lean_ctor_set(x_963, 4, x_959);
x_964 = 0;
x_965 = 0;
if (lean_is_scalar(x_954)) {
 x_966 = lean_alloc_ctor(0, 10, 8);
} else {
 x_966 = x_954;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_942);
lean_ctor_set(x_966, 2, x_943);
lean_ctor_set(x_966, 3, x_944);
lean_ctor_set(x_966, 4, x_945);
lean_ctor_set(x_966, 5, x_946);
lean_ctor_set(x_966, 6, x_947);
lean_ctor_set(x_966, 7, x_948);
lean_ctor_set(x_966, 8, x_949);
lean_ctor_set(x_966, 9, x_950);
lean_ctor_set_uint8(x_966, sizeof(void*)*10 + 4, x_951);
lean_ctor_set_uint8(x_966, sizeof(void*)*10 + 5, x_952);
lean_ctor_set_uint8(x_966, sizeof(void*)*10 + 6, x_953);
lean_ctor_set_uint32(x_966, sizeof(void*)*10, x_964);
lean_ctor_set_uint8(x_966, sizeof(void*)*10 + 7, x_965);
x_967 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_967, 0, x_966);
lean_ctor_set(x_967, 1, x_940);
lean_ctor_set(x_967, 2, x_941);
x_3 = x_889;
x_4 = x_967;
x_5 = x_890;
goto _start;
}
}
}
}
else
{
uint8_t x_982; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_982 = !lean_is_exclusive(x_880);
if (x_982 == 0)
{
return x_880;
}
else
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_983 = lean_ctor_get(x_880, 0);
x_984 = lean_ctor_get(x_880, 1);
lean_inc(x_984);
lean_inc(x_983);
lean_dec(x_880);
x_985 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_985, 0, x_983);
lean_ctor_set(x_985, 1, x_984);
return x_985;
}
}
}
case 8:
{
lean_object* x_986; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_986 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; 
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
if (lean_obj_tag(x_987) == 0)
{
uint8_t x_988; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_988 = !lean_is_exclusive(x_986);
if (x_988 == 0)
{
lean_object* x_989; lean_object* x_990; 
x_989 = lean_ctor_get(x_986, 0);
lean_dec(x_989);
x_990 = lean_box(0);
lean_ctor_set(x_986, 0, x_990);
return x_986;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_986, 1);
lean_inc(x_991);
lean_dec(x_986);
x_992 = lean_box(0);
x_993 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_991);
return x_993;
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; 
x_994 = lean_ctor_get(x_986, 1);
lean_inc(x_994);
lean_dec(x_986);
x_995 = lean_ctor_get(x_987, 0);
lean_inc(x_995);
lean_dec(x_987);
x_1076 = lean_ctor_get(x_4, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
lean_dec(x_1076);
x_1078 = lean_ctor_get(x_1077, 3);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 4);
lean_inc(x_1079);
lean_dec(x_1077);
x_1080 = lean_nat_dec_eq(x_1078, x_1079);
lean_dec(x_1079);
lean_dec(x_1078);
if (x_1080 == 0)
{
x_996 = x_994;
goto block_1075;
}
else
{
lean_object* x_1081; lean_object* x_1082; 
x_1081 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1082 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1081, x_4, x_994);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; 
x_1083 = lean_ctor_get(x_1082, 1);
lean_inc(x_1083);
lean_dec(x_1082);
x_996 = x_1083;
goto block_1075;
}
else
{
uint8_t x_1084; 
lean_dec(x_995);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1084 = !lean_is_exclusive(x_1082);
if (x_1084 == 0)
{
return x_1082;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1085 = lean_ctor_get(x_1082, 0);
x_1086 = lean_ctor_get(x_1082, 1);
lean_inc(x_1086);
lean_inc(x_1085);
lean_dec(x_1082);
x_1087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1087, 0, x_1085);
lean_ctor_set(x_1087, 1, x_1086);
return x_1087;
}
}
}
block_1075:
{
lean_object* x_997; lean_object* x_998; uint8_t x_999; 
x_997 = lean_ctor_get(x_4, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = !lean_is_exclusive(x_4);
if (x_999 == 0)
{
lean_object* x_1000; uint8_t x_1001; 
x_1000 = lean_ctor_get(x_4, 0);
lean_dec(x_1000);
x_1001 = !lean_is_exclusive(x_997);
if (x_1001 == 0)
{
lean_object* x_1002; uint8_t x_1003; 
x_1002 = lean_ctor_get(x_997, 0);
lean_dec(x_1002);
x_1003 = !lean_is_exclusive(x_998);
if (x_1003 == 0)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; uint32_t x_1007; uint8_t x_1008; 
x_1004 = lean_ctor_get(x_998, 3);
x_1005 = lean_unsigned_to_nat(1u);
x_1006 = lean_nat_add(x_1004, x_1005);
lean_dec(x_1004);
lean_ctor_set(x_998, 3, x_1006);
x_1007 = 0;
x_1008 = 0;
lean_ctor_set_uint32(x_997, sizeof(void*)*10, x_1007);
lean_ctor_set_uint8(x_997, sizeof(void*)*10 + 7, x_1008);
x_3 = x_995;
x_5 = x_996;
goto _start;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; uint32_t x_1018; uint8_t x_1019; 
x_1010 = lean_ctor_get(x_998, 0);
x_1011 = lean_ctor_get(x_998, 1);
x_1012 = lean_ctor_get(x_998, 2);
x_1013 = lean_ctor_get(x_998, 3);
x_1014 = lean_ctor_get(x_998, 4);
lean_inc(x_1014);
lean_inc(x_1013);
lean_inc(x_1012);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_998);
x_1015 = lean_unsigned_to_nat(1u);
x_1016 = lean_nat_add(x_1013, x_1015);
lean_dec(x_1013);
x_1017 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1017, 0, x_1010);
lean_ctor_set(x_1017, 1, x_1011);
lean_ctor_set(x_1017, 2, x_1012);
lean_ctor_set(x_1017, 3, x_1016);
lean_ctor_set(x_1017, 4, x_1014);
x_1018 = 0;
x_1019 = 0;
lean_ctor_set(x_997, 0, x_1017);
lean_ctor_set_uint32(x_997, sizeof(void*)*10, x_1018);
lean_ctor_set_uint8(x_997, sizeof(void*)*10 + 7, x_1019);
x_3 = x_995;
x_5 = x_996;
goto _start;
}
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; uint8_t x_1030; uint8_t x_1031; uint8_t x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; uint32_t x_1042; uint8_t x_1043; lean_object* x_1044; 
x_1021 = lean_ctor_get(x_997, 1);
x_1022 = lean_ctor_get(x_997, 2);
x_1023 = lean_ctor_get(x_997, 3);
x_1024 = lean_ctor_get(x_997, 4);
x_1025 = lean_ctor_get(x_997, 5);
x_1026 = lean_ctor_get(x_997, 6);
x_1027 = lean_ctor_get(x_997, 7);
x_1028 = lean_ctor_get(x_997, 8);
x_1029 = lean_ctor_get(x_997, 9);
x_1030 = lean_ctor_get_uint8(x_997, sizeof(void*)*10 + 4);
x_1031 = lean_ctor_get_uint8(x_997, sizeof(void*)*10 + 5);
x_1032 = lean_ctor_get_uint8(x_997, sizeof(void*)*10 + 6);
lean_inc(x_1029);
lean_inc(x_1028);
lean_inc(x_1027);
lean_inc(x_1026);
lean_inc(x_1025);
lean_inc(x_1024);
lean_inc(x_1023);
lean_inc(x_1022);
lean_inc(x_1021);
lean_dec(x_997);
x_1033 = lean_ctor_get(x_998, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_998, 1);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_998, 2);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_998, 3);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_998, 4);
lean_inc(x_1037);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 lean_ctor_release(x_998, 2);
 lean_ctor_release(x_998, 3);
 lean_ctor_release(x_998, 4);
 x_1038 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1038 = lean_box(0);
}
x_1039 = lean_unsigned_to_nat(1u);
x_1040 = lean_nat_add(x_1036, x_1039);
lean_dec(x_1036);
if (lean_is_scalar(x_1038)) {
 x_1041 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1041 = x_1038;
}
lean_ctor_set(x_1041, 0, x_1033);
lean_ctor_set(x_1041, 1, x_1034);
lean_ctor_set(x_1041, 2, x_1035);
lean_ctor_set(x_1041, 3, x_1040);
lean_ctor_set(x_1041, 4, x_1037);
x_1042 = 0;
x_1043 = 0;
x_1044 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_1044, 0, x_1041);
lean_ctor_set(x_1044, 1, x_1021);
lean_ctor_set(x_1044, 2, x_1022);
lean_ctor_set(x_1044, 3, x_1023);
lean_ctor_set(x_1044, 4, x_1024);
lean_ctor_set(x_1044, 5, x_1025);
lean_ctor_set(x_1044, 6, x_1026);
lean_ctor_set(x_1044, 7, x_1027);
lean_ctor_set(x_1044, 8, x_1028);
lean_ctor_set(x_1044, 9, x_1029);
lean_ctor_set_uint8(x_1044, sizeof(void*)*10 + 4, x_1030);
lean_ctor_set_uint8(x_1044, sizeof(void*)*10 + 5, x_1031);
lean_ctor_set_uint8(x_1044, sizeof(void*)*10 + 6, x_1032);
lean_ctor_set_uint32(x_1044, sizeof(void*)*10, x_1042);
lean_ctor_set_uint8(x_1044, sizeof(void*)*10 + 7, x_1043);
lean_ctor_set(x_4, 0, x_1044);
x_3 = x_995;
x_5 = x_996;
goto _start;
}
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; uint8_t x_1057; uint8_t x_1058; uint8_t x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint32_t x_1070; uint8_t x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1046 = lean_ctor_get(x_4, 1);
x_1047 = lean_ctor_get(x_4, 2);
lean_inc(x_1047);
lean_inc(x_1046);
lean_dec(x_4);
x_1048 = lean_ctor_get(x_997, 1);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_997, 2);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_997, 3);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_997, 4);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_997, 5);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_997, 6);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_997, 7);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_997, 8);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_997, 9);
lean_inc(x_1056);
x_1057 = lean_ctor_get_uint8(x_997, sizeof(void*)*10 + 4);
x_1058 = lean_ctor_get_uint8(x_997, sizeof(void*)*10 + 5);
x_1059 = lean_ctor_get_uint8(x_997, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 lean_ctor_release(x_997, 2);
 lean_ctor_release(x_997, 3);
 lean_ctor_release(x_997, 4);
 lean_ctor_release(x_997, 5);
 lean_ctor_release(x_997, 6);
 lean_ctor_release(x_997, 7);
 lean_ctor_release(x_997, 8);
 lean_ctor_release(x_997, 9);
 x_1060 = x_997;
} else {
 lean_dec_ref(x_997);
 x_1060 = lean_box(0);
}
x_1061 = lean_ctor_get(x_998, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_998, 1);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_998, 2);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_998, 3);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_998, 4);
lean_inc(x_1065);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 lean_ctor_release(x_998, 2);
 lean_ctor_release(x_998, 3);
 lean_ctor_release(x_998, 4);
 x_1066 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1066 = lean_box(0);
}
x_1067 = lean_unsigned_to_nat(1u);
x_1068 = lean_nat_add(x_1064, x_1067);
lean_dec(x_1064);
if (lean_is_scalar(x_1066)) {
 x_1069 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1069 = x_1066;
}
lean_ctor_set(x_1069, 0, x_1061);
lean_ctor_set(x_1069, 1, x_1062);
lean_ctor_set(x_1069, 2, x_1063);
lean_ctor_set(x_1069, 3, x_1068);
lean_ctor_set(x_1069, 4, x_1065);
x_1070 = 0;
x_1071 = 0;
if (lean_is_scalar(x_1060)) {
 x_1072 = lean_alloc_ctor(0, 10, 8);
} else {
 x_1072 = x_1060;
}
lean_ctor_set(x_1072, 0, x_1069);
lean_ctor_set(x_1072, 1, x_1048);
lean_ctor_set(x_1072, 2, x_1049);
lean_ctor_set(x_1072, 3, x_1050);
lean_ctor_set(x_1072, 4, x_1051);
lean_ctor_set(x_1072, 5, x_1052);
lean_ctor_set(x_1072, 6, x_1053);
lean_ctor_set(x_1072, 7, x_1054);
lean_ctor_set(x_1072, 8, x_1055);
lean_ctor_set(x_1072, 9, x_1056);
lean_ctor_set_uint8(x_1072, sizeof(void*)*10 + 4, x_1057);
lean_ctor_set_uint8(x_1072, sizeof(void*)*10 + 5, x_1058);
lean_ctor_set_uint8(x_1072, sizeof(void*)*10 + 6, x_1059);
lean_ctor_set_uint32(x_1072, sizeof(void*)*10, x_1070);
lean_ctor_set_uint8(x_1072, sizeof(void*)*10 + 7, x_1071);
x_1073 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1073, 0, x_1072);
lean_ctor_set(x_1073, 1, x_1046);
lean_ctor_set(x_1073, 2, x_1047);
x_3 = x_995;
x_4 = x_1073;
x_5 = x_996;
goto _start;
}
}
}
}
else
{
uint8_t x_1088; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1088 = !lean_is_exclusive(x_986);
if (x_1088 == 0)
{
return x_986;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1089 = lean_ctor_get(x_986, 0);
x_1090 = lean_ctor_get(x_986, 1);
lean_inc(x_1090);
lean_inc(x_1089);
lean_dec(x_986);
x_1091 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1091, 0, x_1089);
lean_ctor_set(x_1091, 1, x_1090);
return x_1091;
}
}
}
case 9:
{
lean_object* x_1092; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1092 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; 
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
if (lean_obj_tag(x_1093) == 0)
{
uint8_t x_1094; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1094 = !lean_is_exclusive(x_1092);
if (x_1094 == 0)
{
lean_object* x_1095; lean_object* x_1096; 
x_1095 = lean_ctor_get(x_1092, 0);
lean_dec(x_1095);
x_1096 = lean_box(0);
lean_ctor_set(x_1092, 0, x_1096);
return x_1092;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1092, 1);
lean_inc(x_1097);
lean_dec(x_1092);
x_1098 = lean_box(0);
x_1099 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1099, 0, x_1098);
lean_ctor_set(x_1099, 1, x_1097);
return x_1099;
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
x_1100 = lean_ctor_get(x_1092, 1);
lean_inc(x_1100);
lean_dec(x_1092);
x_1101 = lean_ctor_get(x_1093, 0);
lean_inc(x_1101);
lean_dec(x_1093);
x_1182 = lean_ctor_get(x_4, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
lean_dec(x_1182);
x_1184 = lean_ctor_get(x_1183, 3);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1183, 4);
lean_inc(x_1185);
lean_dec(x_1183);
x_1186 = lean_nat_dec_eq(x_1184, x_1185);
lean_dec(x_1185);
lean_dec(x_1184);
if (x_1186 == 0)
{
x_1102 = x_1100;
goto block_1181;
}
else
{
lean_object* x_1187; lean_object* x_1188; 
x_1187 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1188 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1187, x_4, x_1100);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; 
x_1189 = lean_ctor_get(x_1188, 1);
lean_inc(x_1189);
lean_dec(x_1188);
x_1102 = x_1189;
goto block_1181;
}
else
{
uint8_t x_1190; 
lean_dec(x_1101);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1190 = !lean_is_exclusive(x_1188);
if (x_1190 == 0)
{
return x_1188;
}
else
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
x_1191 = lean_ctor_get(x_1188, 0);
x_1192 = lean_ctor_get(x_1188, 1);
lean_inc(x_1192);
lean_inc(x_1191);
lean_dec(x_1188);
x_1193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1193, 0, x_1191);
lean_ctor_set(x_1193, 1, x_1192);
return x_1193;
}
}
}
block_1181:
{
lean_object* x_1103; lean_object* x_1104; uint8_t x_1105; 
x_1103 = lean_ctor_get(x_4, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
x_1105 = !lean_is_exclusive(x_4);
if (x_1105 == 0)
{
lean_object* x_1106; uint8_t x_1107; 
x_1106 = lean_ctor_get(x_4, 0);
lean_dec(x_1106);
x_1107 = !lean_is_exclusive(x_1103);
if (x_1107 == 0)
{
lean_object* x_1108; uint8_t x_1109; 
x_1108 = lean_ctor_get(x_1103, 0);
lean_dec(x_1108);
x_1109 = !lean_is_exclusive(x_1104);
if (x_1109 == 0)
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; uint32_t x_1113; uint8_t x_1114; 
x_1110 = lean_ctor_get(x_1104, 3);
x_1111 = lean_unsigned_to_nat(1u);
x_1112 = lean_nat_add(x_1110, x_1111);
lean_dec(x_1110);
lean_ctor_set(x_1104, 3, x_1112);
x_1113 = 0;
x_1114 = 0;
lean_ctor_set_uint32(x_1103, sizeof(void*)*10, x_1113);
lean_ctor_set_uint8(x_1103, sizeof(void*)*10 + 7, x_1114);
x_3 = x_1101;
x_5 = x_1102;
goto _start;
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; uint32_t x_1124; uint8_t x_1125; 
x_1116 = lean_ctor_get(x_1104, 0);
x_1117 = lean_ctor_get(x_1104, 1);
x_1118 = lean_ctor_get(x_1104, 2);
x_1119 = lean_ctor_get(x_1104, 3);
x_1120 = lean_ctor_get(x_1104, 4);
lean_inc(x_1120);
lean_inc(x_1119);
lean_inc(x_1118);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1104);
x_1121 = lean_unsigned_to_nat(1u);
x_1122 = lean_nat_add(x_1119, x_1121);
lean_dec(x_1119);
x_1123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1123, 0, x_1116);
lean_ctor_set(x_1123, 1, x_1117);
lean_ctor_set(x_1123, 2, x_1118);
lean_ctor_set(x_1123, 3, x_1122);
lean_ctor_set(x_1123, 4, x_1120);
x_1124 = 0;
x_1125 = 0;
lean_ctor_set(x_1103, 0, x_1123);
lean_ctor_set_uint32(x_1103, sizeof(void*)*10, x_1124);
lean_ctor_set_uint8(x_1103, sizeof(void*)*10 + 7, x_1125);
x_3 = x_1101;
x_5 = x_1102;
goto _start;
}
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; uint8_t x_1136; uint8_t x_1137; uint8_t x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; uint32_t x_1148; uint8_t x_1149; lean_object* x_1150; 
x_1127 = lean_ctor_get(x_1103, 1);
x_1128 = lean_ctor_get(x_1103, 2);
x_1129 = lean_ctor_get(x_1103, 3);
x_1130 = lean_ctor_get(x_1103, 4);
x_1131 = lean_ctor_get(x_1103, 5);
x_1132 = lean_ctor_get(x_1103, 6);
x_1133 = lean_ctor_get(x_1103, 7);
x_1134 = lean_ctor_get(x_1103, 8);
x_1135 = lean_ctor_get(x_1103, 9);
x_1136 = lean_ctor_get_uint8(x_1103, sizeof(void*)*10 + 4);
x_1137 = lean_ctor_get_uint8(x_1103, sizeof(void*)*10 + 5);
x_1138 = lean_ctor_get_uint8(x_1103, sizeof(void*)*10 + 6);
lean_inc(x_1135);
lean_inc(x_1134);
lean_inc(x_1133);
lean_inc(x_1132);
lean_inc(x_1131);
lean_inc(x_1130);
lean_inc(x_1129);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_1103);
x_1139 = lean_ctor_get(x_1104, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1104, 1);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1104, 2);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1104, 3);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1104, 4);
lean_inc(x_1143);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 lean_ctor_release(x_1104, 2);
 lean_ctor_release(x_1104, 3);
 lean_ctor_release(x_1104, 4);
 x_1144 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1144 = lean_box(0);
}
x_1145 = lean_unsigned_to_nat(1u);
x_1146 = lean_nat_add(x_1142, x_1145);
lean_dec(x_1142);
if (lean_is_scalar(x_1144)) {
 x_1147 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1147 = x_1144;
}
lean_ctor_set(x_1147, 0, x_1139);
lean_ctor_set(x_1147, 1, x_1140);
lean_ctor_set(x_1147, 2, x_1141);
lean_ctor_set(x_1147, 3, x_1146);
lean_ctor_set(x_1147, 4, x_1143);
x_1148 = 0;
x_1149 = 0;
x_1150 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_1150, 0, x_1147);
lean_ctor_set(x_1150, 1, x_1127);
lean_ctor_set(x_1150, 2, x_1128);
lean_ctor_set(x_1150, 3, x_1129);
lean_ctor_set(x_1150, 4, x_1130);
lean_ctor_set(x_1150, 5, x_1131);
lean_ctor_set(x_1150, 6, x_1132);
lean_ctor_set(x_1150, 7, x_1133);
lean_ctor_set(x_1150, 8, x_1134);
lean_ctor_set(x_1150, 9, x_1135);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10 + 4, x_1136);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10 + 5, x_1137);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10 + 6, x_1138);
lean_ctor_set_uint32(x_1150, sizeof(void*)*10, x_1148);
lean_ctor_set_uint8(x_1150, sizeof(void*)*10 + 7, x_1149);
lean_ctor_set(x_4, 0, x_1150);
x_3 = x_1101;
x_5 = x_1102;
goto _start;
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; uint8_t x_1163; uint8_t x_1164; uint8_t x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; uint32_t x_1176; uint8_t x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1152 = lean_ctor_get(x_4, 1);
x_1153 = lean_ctor_get(x_4, 2);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_4);
x_1154 = lean_ctor_get(x_1103, 1);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1103, 2);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1103, 3);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1103, 4);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1103, 5);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1103, 6);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1103, 7);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1103, 8);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1103, 9);
lean_inc(x_1162);
x_1163 = lean_ctor_get_uint8(x_1103, sizeof(void*)*10 + 4);
x_1164 = lean_ctor_get_uint8(x_1103, sizeof(void*)*10 + 5);
x_1165 = lean_ctor_get_uint8(x_1103, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_1103)) {
 lean_ctor_release(x_1103, 0);
 lean_ctor_release(x_1103, 1);
 lean_ctor_release(x_1103, 2);
 lean_ctor_release(x_1103, 3);
 lean_ctor_release(x_1103, 4);
 lean_ctor_release(x_1103, 5);
 lean_ctor_release(x_1103, 6);
 lean_ctor_release(x_1103, 7);
 lean_ctor_release(x_1103, 8);
 lean_ctor_release(x_1103, 9);
 x_1166 = x_1103;
} else {
 lean_dec_ref(x_1103);
 x_1166 = lean_box(0);
}
x_1167 = lean_ctor_get(x_1104, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1104, 1);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1104, 2);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1104, 3);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1104, 4);
lean_inc(x_1171);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 lean_ctor_release(x_1104, 2);
 lean_ctor_release(x_1104, 3);
 lean_ctor_release(x_1104, 4);
 x_1172 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1172 = lean_box(0);
}
x_1173 = lean_unsigned_to_nat(1u);
x_1174 = lean_nat_add(x_1170, x_1173);
lean_dec(x_1170);
if (lean_is_scalar(x_1172)) {
 x_1175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1175 = x_1172;
}
lean_ctor_set(x_1175, 0, x_1167);
lean_ctor_set(x_1175, 1, x_1168);
lean_ctor_set(x_1175, 2, x_1169);
lean_ctor_set(x_1175, 3, x_1174);
lean_ctor_set(x_1175, 4, x_1171);
x_1176 = 0;
x_1177 = 0;
if (lean_is_scalar(x_1166)) {
 x_1178 = lean_alloc_ctor(0, 10, 8);
} else {
 x_1178 = x_1166;
}
lean_ctor_set(x_1178, 0, x_1175);
lean_ctor_set(x_1178, 1, x_1154);
lean_ctor_set(x_1178, 2, x_1155);
lean_ctor_set(x_1178, 3, x_1156);
lean_ctor_set(x_1178, 4, x_1157);
lean_ctor_set(x_1178, 5, x_1158);
lean_ctor_set(x_1178, 6, x_1159);
lean_ctor_set(x_1178, 7, x_1160);
lean_ctor_set(x_1178, 8, x_1161);
lean_ctor_set(x_1178, 9, x_1162);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 4, x_1163);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 5, x_1164);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 6, x_1165);
lean_ctor_set_uint32(x_1178, sizeof(void*)*10, x_1176);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 7, x_1177);
x_1179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1179, 0, x_1178);
lean_ctor_set(x_1179, 1, x_1152);
lean_ctor_set(x_1179, 2, x_1153);
x_3 = x_1101;
x_4 = x_1179;
x_5 = x_1102;
goto _start;
}
}
}
}
else
{
uint8_t x_1194; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1194 = !lean_is_exclusive(x_1092);
if (x_1194 == 0)
{
return x_1092;
}
else
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
x_1195 = lean_ctor_get(x_1092, 0);
x_1196 = lean_ctor_get(x_1092, 1);
lean_inc(x_1196);
lean_inc(x_1195);
lean_dec(x_1092);
x_1197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1197, 0, x_1195);
lean_ctor_set(x_1197, 1, x_1196);
return x_1197;
}
}
}
case 10:
{
lean_object* x_1198; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1198 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; 
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
if (lean_obj_tag(x_1199) == 0)
{
uint8_t x_1200; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1200 = !lean_is_exclusive(x_1198);
if (x_1200 == 0)
{
lean_object* x_1201; lean_object* x_1202; 
x_1201 = lean_ctor_get(x_1198, 0);
lean_dec(x_1201);
x_1202 = lean_box(0);
lean_ctor_set(x_1198, 0, x_1202);
return x_1198;
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1203 = lean_ctor_get(x_1198, 1);
lean_inc(x_1203);
lean_dec(x_1198);
x_1204 = lean_box(0);
x_1205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1205, 0, x_1204);
lean_ctor_set(x_1205, 1, x_1203);
return x_1205;
}
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; uint8_t x_1292; 
x_1206 = lean_ctor_get(x_1198, 1);
lean_inc(x_1206);
lean_dec(x_1198);
x_1207 = lean_ctor_get(x_1199, 0);
lean_inc(x_1207);
lean_dec(x_1199);
x_1288 = lean_ctor_get(x_4, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1288, 0);
lean_inc(x_1289);
lean_dec(x_1288);
x_1290 = lean_ctor_get(x_1289, 3);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 4);
lean_inc(x_1291);
lean_dec(x_1289);
x_1292 = lean_nat_dec_eq(x_1290, x_1291);
lean_dec(x_1291);
lean_dec(x_1290);
if (x_1292 == 0)
{
x_1208 = x_1206;
goto block_1287;
}
else
{
lean_object* x_1293; lean_object* x_1294; 
x_1293 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1294 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1293, x_4, x_1206);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; 
x_1295 = lean_ctor_get(x_1294, 1);
lean_inc(x_1295);
lean_dec(x_1294);
x_1208 = x_1295;
goto block_1287;
}
else
{
uint8_t x_1296; 
lean_dec(x_1207);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1296 = !lean_is_exclusive(x_1294);
if (x_1296 == 0)
{
return x_1294;
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1297 = lean_ctor_get(x_1294, 0);
x_1298 = lean_ctor_get(x_1294, 1);
lean_inc(x_1298);
lean_inc(x_1297);
lean_dec(x_1294);
x_1299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1299, 0, x_1297);
lean_ctor_set(x_1299, 1, x_1298);
return x_1299;
}
}
}
block_1287:
{
lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; 
x_1209 = lean_ctor_get(x_4, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
x_1211 = !lean_is_exclusive(x_4);
if (x_1211 == 0)
{
lean_object* x_1212; uint8_t x_1213; 
x_1212 = lean_ctor_get(x_4, 0);
lean_dec(x_1212);
x_1213 = !lean_is_exclusive(x_1209);
if (x_1213 == 0)
{
lean_object* x_1214; uint8_t x_1215; 
x_1214 = lean_ctor_get(x_1209, 0);
lean_dec(x_1214);
x_1215 = !lean_is_exclusive(x_1210);
if (x_1215 == 0)
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; uint32_t x_1219; uint8_t x_1220; 
x_1216 = lean_ctor_get(x_1210, 3);
x_1217 = lean_unsigned_to_nat(1u);
x_1218 = lean_nat_add(x_1216, x_1217);
lean_dec(x_1216);
lean_ctor_set(x_1210, 3, x_1218);
x_1219 = 0;
x_1220 = 0;
lean_ctor_set_uint32(x_1209, sizeof(void*)*10, x_1219);
lean_ctor_set_uint8(x_1209, sizeof(void*)*10 + 7, x_1220);
x_3 = x_1207;
x_5 = x_1208;
goto _start;
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; uint32_t x_1230; uint8_t x_1231; 
x_1222 = lean_ctor_get(x_1210, 0);
x_1223 = lean_ctor_get(x_1210, 1);
x_1224 = lean_ctor_get(x_1210, 2);
x_1225 = lean_ctor_get(x_1210, 3);
x_1226 = lean_ctor_get(x_1210, 4);
lean_inc(x_1226);
lean_inc(x_1225);
lean_inc(x_1224);
lean_inc(x_1223);
lean_inc(x_1222);
lean_dec(x_1210);
x_1227 = lean_unsigned_to_nat(1u);
x_1228 = lean_nat_add(x_1225, x_1227);
lean_dec(x_1225);
x_1229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1229, 0, x_1222);
lean_ctor_set(x_1229, 1, x_1223);
lean_ctor_set(x_1229, 2, x_1224);
lean_ctor_set(x_1229, 3, x_1228);
lean_ctor_set(x_1229, 4, x_1226);
x_1230 = 0;
x_1231 = 0;
lean_ctor_set(x_1209, 0, x_1229);
lean_ctor_set_uint32(x_1209, sizeof(void*)*10, x_1230);
lean_ctor_set_uint8(x_1209, sizeof(void*)*10 + 7, x_1231);
x_3 = x_1207;
x_5 = x_1208;
goto _start;
}
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; uint8_t x_1242; uint8_t x_1243; uint8_t x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; uint32_t x_1254; uint8_t x_1255; lean_object* x_1256; 
x_1233 = lean_ctor_get(x_1209, 1);
x_1234 = lean_ctor_get(x_1209, 2);
x_1235 = lean_ctor_get(x_1209, 3);
x_1236 = lean_ctor_get(x_1209, 4);
x_1237 = lean_ctor_get(x_1209, 5);
x_1238 = lean_ctor_get(x_1209, 6);
x_1239 = lean_ctor_get(x_1209, 7);
x_1240 = lean_ctor_get(x_1209, 8);
x_1241 = lean_ctor_get(x_1209, 9);
x_1242 = lean_ctor_get_uint8(x_1209, sizeof(void*)*10 + 4);
x_1243 = lean_ctor_get_uint8(x_1209, sizeof(void*)*10 + 5);
x_1244 = lean_ctor_get_uint8(x_1209, sizeof(void*)*10 + 6);
lean_inc(x_1241);
lean_inc(x_1240);
lean_inc(x_1239);
lean_inc(x_1238);
lean_inc(x_1237);
lean_inc(x_1236);
lean_inc(x_1235);
lean_inc(x_1234);
lean_inc(x_1233);
lean_dec(x_1209);
x_1245 = lean_ctor_get(x_1210, 0);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_1210, 1);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1210, 2);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_1210, 3);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1210, 4);
lean_inc(x_1249);
if (lean_is_exclusive(x_1210)) {
 lean_ctor_release(x_1210, 0);
 lean_ctor_release(x_1210, 1);
 lean_ctor_release(x_1210, 2);
 lean_ctor_release(x_1210, 3);
 lean_ctor_release(x_1210, 4);
 x_1250 = x_1210;
} else {
 lean_dec_ref(x_1210);
 x_1250 = lean_box(0);
}
x_1251 = lean_unsigned_to_nat(1u);
x_1252 = lean_nat_add(x_1248, x_1251);
lean_dec(x_1248);
if (lean_is_scalar(x_1250)) {
 x_1253 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1253 = x_1250;
}
lean_ctor_set(x_1253, 0, x_1245);
lean_ctor_set(x_1253, 1, x_1246);
lean_ctor_set(x_1253, 2, x_1247);
lean_ctor_set(x_1253, 3, x_1252);
lean_ctor_set(x_1253, 4, x_1249);
x_1254 = 0;
x_1255 = 0;
x_1256 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_1256, 0, x_1253);
lean_ctor_set(x_1256, 1, x_1233);
lean_ctor_set(x_1256, 2, x_1234);
lean_ctor_set(x_1256, 3, x_1235);
lean_ctor_set(x_1256, 4, x_1236);
lean_ctor_set(x_1256, 5, x_1237);
lean_ctor_set(x_1256, 6, x_1238);
lean_ctor_set(x_1256, 7, x_1239);
lean_ctor_set(x_1256, 8, x_1240);
lean_ctor_set(x_1256, 9, x_1241);
lean_ctor_set_uint8(x_1256, sizeof(void*)*10 + 4, x_1242);
lean_ctor_set_uint8(x_1256, sizeof(void*)*10 + 5, x_1243);
lean_ctor_set_uint8(x_1256, sizeof(void*)*10 + 6, x_1244);
lean_ctor_set_uint32(x_1256, sizeof(void*)*10, x_1254);
lean_ctor_set_uint8(x_1256, sizeof(void*)*10 + 7, x_1255);
lean_ctor_set(x_4, 0, x_1256);
x_3 = x_1207;
x_5 = x_1208;
goto _start;
}
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; uint8_t x_1270; uint8_t x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint32_t x_1282; uint8_t x_1283; lean_object* x_1284; lean_object* x_1285; 
x_1258 = lean_ctor_get(x_4, 1);
x_1259 = lean_ctor_get(x_4, 2);
lean_inc(x_1259);
lean_inc(x_1258);
lean_dec(x_4);
x_1260 = lean_ctor_get(x_1209, 1);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1209, 2);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1209, 3);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1209, 4);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1209, 5);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1209, 6);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1209, 7);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1209, 8);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_1209, 9);
lean_inc(x_1268);
x_1269 = lean_ctor_get_uint8(x_1209, sizeof(void*)*10 + 4);
x_1270 = lean_ctor_get_uint8(x_1209, sizeof(void*)*10 + 5);
x_1271 = lean_ctor_get_uint8(x_1209, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_1209)) {
 lean_ctor_release(x_1209, 0);
 lean_ctor_release(x_1209, 1);
 lean_ctor_release(x_1209, 2);
 lean_ctor_release(x_1209, 3);
 lean_ctor_release(x_1209, 4);
 lean_ctor_release(x_1209, 5);
 lean_ctor_release(x_1209, 6);
 lean_ctor_release(x_1209, 7);
 lean_ctor_release(x_1209, 8);
 lean_ctor_release(x_1209, 9);
 x_1272 = x_1209;
} else {
 lean_dec_ref(x_1209);
 x_1272 = lean_box(0);
}
x_1273 = lean_ctor_get(x_1210, 0);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_1210, 1);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_1210, 2);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1210, 3);
lean_inc(x_1276);
x_1277 = lean_ctor_get(x_1210, 4);
lean_inc(x_1277);
if (lean_is_exclusive(x_1210)) {
 lean_ctor_release(x_1210, 0);
 lean_ctor_release(x_1210, 1);
 lean_ctor_release(x_1210, 2);
 lean_ctor_release(x_1210, 3);
 lean_ctor_release(x_1210, 4);
 x_1278 = x_1210;
} else {
 lean_dec_ref(x_1210);
 x_1278 = lean_box(0);
}
x_1279 = lean_unsigned_to_nat(1u);
x_1280 = lean_nat_add(x_1276, x_1279);
lean_dec(x_1276);
if (lean_is_scalar(x_1278)) {
 x_1281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1281 = x_1278;
}
lean_ctor_set(x_1281, 0, x_1273);
lean_ctor_set(x_1281, 1, x_1274);
lean_ctor_set(x_1281, 2, x_1275);
lean_ctor_set(x_1281, 3, x_1280);
lean_ctor_set(x_1281, 4, x_1277);
x_1282 = 0;
x_1283 = 0;
if (lean_is_scalar(x_1272)) {
 x_1284 = lean_alloc_ctor(0, 10, 8);
} else {
 x_1284 = x_1272;
}
lean_ctor_set(x_1284, 0, x_1281);
lean_ctor_set(x_1284, 1, x_1260);
lean_ctor_set(x_1284, 2, x_1261);
lean_ctor_set(x_1284, 3, x_1262);
lean_ctor_set(x_1284, 4, x_1263);
lean_ctor_set(x_1284, 5, x_1264);
lean_ctor_set(x_1284, 6, x_1265);
lean_ctor_set(x_1284, 7, x_1266);
lean_ctor_set(x_1284, 8, x_1267);
lean_ctor_set(x_1284, 9, x_1268);
lean_ctor_set_uint8(x_1284, sizeof(void*)*10 + 4, x_1269);
lean_ctor_set_uint8(x_1284, sizeof(void*)*10 + 5, x_1270);
lean_ctor_set_uint8(x_1284, sizeof(void*)*10 + 6, x_1271);
lean_ctor_set_uint32(x_1284, sizeof(void*)*10, x_1282);
lean_ctor_set_uint8(x_1284, sizeof(void*)*10 + 7, x_1283);
x_1285 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1285, 0, x_1284);
lean_ctor_set(x_1285, 1, x_1258);
lean_ctor_set(x_1285, 2, x_1259);
x_3 = x_1207;
x_4 = x_1285;
x_5 = x_1208;
goto _start;
}
}
}
}
else
{
uint8_t x_1300; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1300 = !lean_is_exclusive(x_1198);
if (x_1300 == 0)
{
return x_1198;
}
else
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1301 = lean_ctor_get(x_1198, 0);
x_1302 = lean_ctor_get(x_1198, 1);
lean_inc(x_1302);
lean_inc(x_1301);
lean_dec(x_1198);
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1301);
lean_ctor_set(x_1303, 1, x_1302);
return x_1303;
}
}
}
case 11:
{
lean_object* x_1304; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1304 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1304) == 0)
{
lean_object* x_1305; 
x_1305 = lean_ctor_get(x_1304, 0);
lean_inc(x_1305);
if (lean_obj_tag(x_1305) == 0)
{
uint8_t x_1306; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1306 = !lean_is_exclusive(x_1304);
if (x_1306 == 0)
{
lean_object* x_1307; lean_object* x_1308; 
x_1307 = lean_ctor_get(x_1304, 0);
lean_dec(x_1307);
x_1308 = lean_box(0);
lean_ctor_set(x_1304, 0, x_1308);
return x_1304;
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1309 = lean_ctor_get(x_1304, 1);
lean_inc(x_1309);
lean_dec(x_1304);
x_1310 = lean_box(0);
x_1311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1311, 0, x_1310);
lean_ctor_set(x_1311, 1, x_1309);
return x_1311;
}
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; uint8_t x_1398; 
x_1312 = lean_ctor_get(x_1304, 1);
lean_inc(x_1312);
lean_dec(x_1304);
x_1313 = lean_ctor_get(x_1305, 0);
lean_inc(x_1313);
lean_dec(x_1305);
x_1394 = lean_ctor_get(x_4, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1394, 0);
lean_inc(x_1395);
lean_dec(x_1394);
x_1396 = lean_ctor_get(x_1395, 3);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_1395, 4);
lean_inc(x_1397);
lean_dec(x_1395);
x_1398 = lean_nat_dec_eq(x_1396, x_1397);
lean_dec(x_1397);
lean_dec(x_1396);
if (x_1398 == 0)
{
x_1314 = x_1312;
goto block_1393;
}
else
{
lean_object* x_1399; lean_object* x_1400; 
x_1399 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1400 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1399, x_4, x_1312);
if (lean_obj_tag(x_1400) == 0)
{
lean_object* x_1401; 
x_1401 = lean_ctor_get(x_1400, 1);
lean_inc(x_1401);
lean_dec(x_1400);
x_1314 = x_1401;
goto block_1393;
}
else
{
uint8_t x_1402; 
lean_dec(x_1313);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1402 = !lean_is_exclusive(x_1400);
if (x_1402 == 0)
{
return x_1400;
}
else
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
x_1403 = lean_ctor_get(x_1400, 0);
x_1404 = lean_ctor_get(x_1400, 1);
lean_inc(x_1404);
lean_inc(x_1403);
lean_dec(x_1400);
x_1405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1405, 0, x_1403);
lean_ctor_set(x_1405, 1, x_1404);
return x_1405;
}
}
}
block_1393:
{
lean_object* x_1315; lean_object* x_1316; uint8_t x_1317; 
x_1315 = lean_ctor_get(x_4, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = !lean_is_exclusive(x_4);
if (x_1317 == 0)
{
lean_object* x_1318; uint8_t x_1319; 
x_1318 = lean_ctor_get(x_4, 0);
lean_dec(x_1318);
x_1319 = !lean_is_exclusive(x_1315);
if (x_1319 == 0)
{
lean_object* x_1320; uint8_t x_1321; 
x_1320 = lean_ctor_get(x_1315, 0);
lean_dec(x_1320);
x_1321 = !lean_is_exclusive(x_1316);
if (x_1321 == 0)
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint32_t x_1325; uint8_t x_1326; 
x_1322 = lean_ctor_get(x_1316, 3);
x_1323 = lean_unsigned_to_nat(1u);
x_1324 = lean_nat_add(x_1322, x_1323);
lean_dec(x_1322);
lean_ctor_set(x_1316, 3, x_1324);
x_1325 = 0;
x_1326 = 0;
lean_ctor_set_uint32(x_1315, sizeof(void*)*10, x_1325);
lean_ctor_set_uint8(x_1315, sizeof(void*)*10 + 7, x_1326);
x_3 = x_1313;
x_5 = x_1314;
goto _start;
}
else
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; uint32_t x_1336; uint8_t x_1337; 
x_1328 = lean_ctor_get(x_1316, 0);
x_1329 = lean_ctor_get(x_1316, 1);
x_1330 = lean_ctor_get(x_1316, 2);
x_1331 = lean_ctor_get(x_1316, 3);
x_1332 = lean_ctor_get(x_1316, 4);
lean_inc(x_1332);
lean_inc(x_1331);
lean_inc(x_1330);
lean_inc(x_1329);
lean_inc(x_1328);
lean_dec(x_1316);
x_1333 = lean_unsigned_to_nat(1u);
x_1334 = lean_nat_add(x_1331, x_1333);
lean_dec(x_1331);
x_1335 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1335, 0, x_1328);
lean_ctor_set(x_1335, 1, x_1329);
lean_ctor_set(x_1335, 2, x_1330);
lean_ctor_set(x_1335, 3, x_1334);
lean_ctor_set(x_1335, 4, x_1332);
x_1336 = 0;
x_1337 = 0;
lean_ctor_set(x_1315, 0, x_1335);
lean_ctor_set_uint32(x_1315, sizeof(void*)*10, x_1336);
lean_ctor_set_uint8(x_1315, sizeof(void*)*10 + 7, x_1337);
x_3 = x_1313;
x_5 = x_1314;
goto _start;
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; uint8_t x_1348; uint8_t x_1349; uint8_t x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; uint32_t x_1360; uint8_t x_1361; lean_object* x_1362; 
x_1339 = lean_ctor_get(x_1315, 1);
x_1340 = lean_ctor_get(x_1315, 2);
x_1341 = lean_ctor_get(x_1315, 3);
x_1342 = lean_ctor_get(x_1315, 4);
x_1343 = lean_ctor_get(x_1315, 5);
x_1344 = lean_ctor_get(x_1315, 6);
x_1345 = lean_ctor_get(x_1315, 7);
x_1346 = lean_ctor_get(x_1315, 8);
x_1347 = lean_ctor_get(x_1315, 9);
x_1348 = lean_ctor_get_uint8(x_1315, sizeof(void*)*10 + 4);
x_1349 = lean_ctor_get_uint8(x_1315, sizeof(void*)*10 + 5);
x_1350 = lean_ctor_get_uint8(x_1315, sizeof(void*)*10 + 6);
lean_inc(x_1347);
lean_inc(x_1346);
lean_inc(x_1345);
lean_inc(x_1344);
lean_inc(x_1343);
lean_inc(x_1342);
lean_inc(x_1341);
lean_inc(x_1340);
lean_inc(x_1339);
lean_dec(x_1315);
x_1351 = lean_ctor_get(x_1316, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1316, 1);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1316, 2);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1316, 3);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1316, 4);
lean_inc(x_1355);
if (lean_is_exclusive(x_1316)) {
 lean_ctor_release(x_1316, 0);
 lean_ctor_release(x_1316, 1);
 lean_ctor_release(x_1316, 2);
 lean_ctor_release(x_1316, 3);
 lean_ctor_release(x_1316, 4);
 x_1356 = x_1316;
} else {
 lean_dec_ref(x_1316);
 x_1356 = lean_box(0);
}
x_1357 = lean_unsigned_to_nat(1u);
x_1358 = lean_nat_add(x_1354, x_1357);
lean_dec(x_1354);
if (lean_is_scalar(x_1356)) {
 x_1359 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1359 = x_1356;
}
lean_ctor_set(x_1359, 0, x_1351);
lean_ctor_set(x_1359, 1, x_1352);
lean_ctor_set(x_1359, 2, x_1353);
lean_ctor_set(x_1359, 3, x_1358);
lean_ctor_set(x_1359, 4, x_1355);
x_1360 = 0;
x_1361 = 0;
x_1362 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_1362, 0, x_1359);
lean_ctor_set(x_1362, 1, x_1339);
lean_ctor_set(x_1362, 2, x_1340);
lean_ctor_set(x_1362, 3, x_1341);
lean_ctor_set(x_1362, 4, x_1342);
lean_ctor_set(x_1362, 5, x_1343);
lean_ctor_set(x_1362, 6, x_1344);
lean_ctor_set(x_1362, 7, x_1345);
lean_ctor_set(x_1362, 8, x_1346);
lean_ctor_set(x_1362, 9, x_1347);
lean_ctor_set_uint8(x_1362, sizeof(void*)*10 + 4, x_1348);
lean_ctor_set_uint8(x_1362, sizeof(void*)*10 + 5, x_1349);
lean_ctor_set_uint8(x_1362, sizeof(void*)*10 + 6, x_1350);
lean_ctor_set_uint32(x_1362, sizeof(void*)*10, x_1360);
lean_ctor_set_uint8(x_1362, sizeof(void*)*10 + 7, x_1361);
lean_ctor_set(x_4, 0, x_1362);
x_3 = x_1313;
x_5 = x_1314;
goto _start;
}
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; uint8_t x_1375; uint8_t x_1376; uint8_t x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; uint32_t x_1388; uint8_t x_1389; lean_object* x_1390; lean_object* x_1391; 
x_1364 = lean_ctor_get(x_4, 1);
x_1365 = lean_ctor_get(x_4, 2);
lean_inc(x_1365);
lean_inc(x_1364);
lean_dec(x_4);
x_1366 = lean_ctor_get(x_1315, 1);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1315, 2);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1315, 3);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1315, 4);
lean_inc(x_1369);
x_1370 = lean_ctor_get(x_1315, 5);
lean_inc(x_1370);
x_1371 = lean_ctor_get(x_1315, 6);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1315, 7);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1315, 8);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1315, 9);
lean_inc(x_1374);
x_1375 = lean_ctor_get_uint8(x_1315, sizeof(void*)*10 + 4);
x_1376 = lean_ctor_get_uint8(x_1315, sizeof(void*)*10 + 5);
x_1377 = lean_ctor_get_uint8(x_1315, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_1315)) {
 lean_ctor_release(x_1315, 0);
 lean_ctor_release(x_1315, 1);
 lean_ctor_release(x_1315, 2);
 lean_ctor_release(x_1315, 3);
 lean_ctor_release(x_1315, 4);
 lean_ctor_release(x_1315, 5);
 lean_ctor_release(x_1315, 6);
 lean_ctor_release(x_1315, 7);
 lean_ctor_release(x_1315, 8);
 lean_ctor_release(x_1315, 9);
 x_1378 = x_1315;
} else {
 lean_dec_ref(x_1315);
 x_1378 = lean_box(0);
}
x_1379 = lean_ctor_get(x_1316, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1316, 1);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1316, 2);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1316, 3);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1316, 4);
lean_inc(x_1383);
if (lean_is_exclusive(x_1316)) {
 lean_ctor_release(x_1316, 0);
 lean_ctor_release(x_1316, 1);
 lean_ctor_release(x_1316, 2);
 lean_ctor_release(x_1316, 3);
 lean_ctor_release(x_1316, 4);
 x_1384 = x_1316;
} else {
 lean_dec_ref(x_1316);
 x_1384 = lean_box(0);
}
x_1385 = lean_unsigned_to_nat(1u);
x_1386 = lean_nat_add(x_1382, x_1385);
lean_dec(x_1382);
if (lean_is_scalar(x_1384)) {
 x_1387 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1387 = x_1384;
}
lean_ctor_set(x_1387, 0, x_1379);
lean_ctor_set(x_1387, 1, x_1380);
lean_ctor_set(x_1387, 2, x_1381);
lean_ctor_set(x_1387, 3, x_1386);
lean_ctor_set(x_1387, 4, x_1383);
x_1388 = 0;
x_1389 = 0;
if (lean_is_scalar(x_1378)) {
 x_1390 = lean_alloc_ctor(0, 10, 8);
} else {
 x_1390 = x_1378;
}
lean_ctor_set(x_1390, 0, x_1387);
lean_ctor_set(x_1390, 1, x_1366);
lean_ctor_set(x_1390, 2, x_1367);
lean_ctor_set(x_1390, 3, x_1368);
lean_ctor_set(x_1390, 4, x_1369);
lean_ctor_set(x_1390, 5, x_1370);
lean_ctor_set(x_1390, 6, x_1371);
lean_ctor_set(x_1390, 7, x_1372);
lean_ctor_set(x_1390, 8, x_1373);
lean_ctor_set(x_1390, 9, x_1374);
lean_ctor_set_uint8(x_1390, sizeof(void*)*10 + 4, x_1375);
lean_ctor_set_uint8(x_1390, sizeof(void*)*10 + 5, x_1376);
lean_ctor_set_uint8(x_1390, sizeof(void*)*10 + 6, x_1377);
lean_ctor_set_uint32(x_1390, sizeof(void*)*10, x_1388);
lean_ctor_set_uint8(x_1390, sizeof(void*)*10 + 7, x_1389);
x_1391 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1391, 0, x_1390);
lean_ctor_set(x_1391, 1, x_1364);
lean_ctor_set(x_1391, 2, x_1365);
x_3 = x_1313;
x_4 = x_1391;
x_5 = x_1314;
goto _start;
}
}
}
}
else
{
uint8_t x_1406; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1406 = !lean_is_exclusive(x_1304);
if (x_1406 == 0)
{
return x_1304;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
x_1407 = lean_ctor_get(x_1304, 0);
x_1408 = lean_ctor_get(x_1304, 1);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1304);
x_1409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1409, 0, x_1407);
lean_ctor_set(x_1409, 1, x_1408);
return x_1409;
}
}
}
default: 
{
lean_object* x_1410; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1410 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1410) == 0)
{
lean_object* x_1411; 
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
if (lean_obj_tag(x_1411) == 0)
{
uint8_t x_1412; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1412 = !lean_is_exclusive(x_1410);
if (x_1412 == 0)
{
lean_object* x_1413; lean_object* x_1414; 
x_1413 = lean_ctor_get(x_1410, 0);
lean_dec(x_1413);
x_1414 = lean_box(0);
lean_ctor_set(x_1410, 0, x_1414);
return x_1410;
}
else
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
x_1415 = lean_ctor_get(x_1410, 1);
lean_inc(x_1415);
lean_dec(x_1410);
x_1416 = lean_box(0);
x_1417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1417, 0, x_1416);
lean_ctor_set(x_1417, 1, x_1415);
return x_1417;
}
}
else
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; uint8_t x_1504; 
x_1418 = lean_ctor_get(x_1410, 1);
lean_inc(x_1418);
lean_dec(x_1410);
x_1419 = lean_ctor_get(x_1411, 0);
lean_inc(x_1419);
lean_dec(x_1411);
x_1500 = lean_ctor_get(x_4, 0);
lean_inc(x_1500);
x_1501 = lean_ctor_get(x_1500, 0);
lean_inc(x_1501);
lean_dec(x_1500);
x_1502 = lean_ctor_get(x_1501, 3);
lean_inc(x_1502);
x_1503 = lean_ctor_get(x_1501, 4);
lean_inc(x_1503);
lean_dec(x_1501);
x_1504 = lean_nat_dec_eq(x_1502, x_1503);
lean_dec(x_1503);
lean_dec(x_1502);
if (x_1504 == 0)
{
x_1420 = x_1418;
goto block_1499;
}
else
{
lean_object* x_1505; lean_object* x_1506; 
x_1505 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1506 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1505, x_4, x_1418);
if (lean_obj_tag(x_1506) == 0)
{
lean_object* x_1507; 
x_1507 = lean_ctor_get(x_1506, 1);
lean_inc(x_1507);
lean_dec(x_1506);
x_1420 = x_1507;
goto block_1499;
}
else
{
uint8_t x_1508; 
lean_dec(x_1419);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1508 = !lean_is_exclusive(x_1506);
if (x_1508 == 0)
{
return x_1506;
}
else
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1509 = lean_ctor_get(x_1506, 0);
x_1510 = lean_ctor_get(x_1506, 1);
lean_inc(x_1510);
lean_inc(x_1509);
lean_dec(x_1506);
x_1511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1511, 0, x_1509);
lean_ctor_set(x_1511, 1, x_1510);
return x_1511;
}
}
}
block_1499:
{
lean_object* x_1421; lean_object* x_1422; uint8_t x_1423; 
x_1421 = lean_ctor_get(x_4, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
x_1423 = !lean_is_exclusive(x_4);
if (x_1423 == 0)
{
lean_object* x_1424; uint8_t x_1425; 
x_1424 = lean_ctor_get(x_4, 0);
lean_dec(x_1424);
x_1425 = !lean_is_exclusive(x_1421);
if (x_1425 == 0)
{
lean_object* x_1426; uint8_t x_1427; 
x_1426 = lean_ctor_get(x_1421, 0);
lean_dec(x_1426);
x_1427 = !lean_is_exclusive(x_1422);
if (x_1427 == 0)
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; uint32_t x_1431; uint8_t x_1432; 
x_1428 = lean_ctor_get(x_1422, 3);
x_1429 = lean_unsigned_to_nat(1u);
x_1430 = lean_nat_add(x_1428, x_1429);
lean_dec(x_1428);
lean_ctor_set(x_1422, 3, x_1430);
x_1431 = 0;
x_1432 = 0;
lean_ctor_set_uint32(x_1421, sizeof(void*)*10, x_1431);
lean_ctor_set_uint8(x_1421, sizeof(void*)*10 + 7, x_1432);
x_3 = x_1419;
x_5 = x_1420;
goto _start;
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; uint32_t x_1442; uint8_t x_1443; 
x_1434 = lean_ctor_get(x_1422, 0);
x_1435 = lean_ctor_get(x_1422, 1);
x_1436 = lean_ctor_get(x_1422, 2);
x_1437 = lean_ctor_get(x_1422, 3);
x_1438 = lean_ctor_get(x_1422, 4);
lean_inc(x_1438);
lean_inc(x_1437);
lean_inc(x_1436);
lean_inc(x_1435);
lean_inc(x_1434);
lean_dec(x_1422);
x_1439 = lean_unsigned_to_nat(1u);
x_1440 = lean_nat_add(x_1437, x_1439);
lean_dec(x_1437);
x_1441 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1441, 0, x_1434);
lean_ctor_set(x_1441, 1, x_1435);
lean_ctor_set(x_1441, 2, x_1436);
lean_ctor_set(x_1441, 3, x_1440);
lean_ctor_set(x_1441, 4, x_1438);
x_1442 = 0;
x_1443 = 0;
lean_ctor_set(x_1421, 0, x_1441);
lean_ctor_set_uint32(x_1421, sizeof(void*)*10, x_1442);
lean_ctor_set_uint8(x_1421, sizeof(void*)*10 + 7, x_1443);
x_3 = x_1419;
x_5 = x_1420;
goto _start;
}
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; uint8_t x_1454; uint8_t x_1455; uint8_t x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; uint32_t x_1466; uint8_t x_1467; lean_object* x_1468; 
x_1445 = lean_ctor_get(x_1421, 1);
x_1446 = lean_ctor_get(x_1421, 2);
x_1447 = lean_ctor_get(x_1421, 3);
x_1448 = lean_ctor_get(x_1421, 4);
x_1449 = lean_ctor_get(x_1421, 5);
x_1450 = lean_ctor_get(x_1421, 6);
x_1451 = lean_ctor_get(x_1421, 7);
x_1452 = lean_ctor_get(x_1421, 8);
x_1453 = lean_ctor_get(x_1421, 9);
x_1454 = lean_ctor_get_uint8(x_1421, sizeof(void*)*10 + 4);
x_1455 = lean_ctor_get_uint8(x_1421, sizeof(void*)*10 + 5);
x_1456 = lean_ctor_get_uint8(x_1421, sizeof(void*)*10 + 6);
lean_inc(x_1453);
lean_inc(x_1452);
lean_inc(x_1451);
lean_inc(x_1450);
lean_inc(x_1449);
lean_inc(x_1448);
lean_inc(x_1447);
lean_inc(x_1446);
lean_inc(x_1445);
lean_dec(x_1421);
x_1457 = lean_ctor_get(x_1422, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1422, 1);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1422, 2);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1422, 3);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1422, 4);
lean_inc(x_1461);
if (lean_is_exclusive(x_1422)) {
 lean_ctor_release(x_1422, 0);
 lean_ctor_release(x_1422, 1);
 lean_ctor_release(x_1422, 2);
 lean_ctor_release(x_1422, 3);
 lean_ctor_release(x_1422, 4);
 x_1462 = x_1422;
} else {
 lean_dec_ref(x_1422);
 x_1462 = lean_box(0);
}
x_1463 = lean_unsigned_to_nat(1u);
x_1464 = lean_nat_add(x_1460, x_1463);
lean_dec(x_1460);
if (lean_is_scalar(x_1462)) {
 x_1465 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1465 = x_1462;
}
lean_ctor_set(x_1465, 0, x_1457);
lean_ctor_set(x_1465, 1, x_1458);
lean_ctor_set(x_1465, 2, x_1459);
lean_ctor_set(x_1465, 3, x_1464);
lean_ctor_set(x_1465, 4, x_1461);
x_1466 = 0;
x_1467 = 0;
x_1468 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_1468, 0, x_1465);
lean_ctor_set(x_1468, 1, x_1445);
lean_ctor_set(x_1468, 2, x_1446);
lean_ctor_set(x_1468, 3, x_1447);
lean_ctor_set(x_1468, 4, x_1448);
lean_ctor_set(x_1468, 5, x_1449);
lean_ctor_set(x_1468, 6, x_1450);
lean_ctor_set(x_1468, 7, x_1451);
lean_ctor_set(x_1468, 8, x_1452);
lean_ctor_set(x_1468, 9, x_1453);
lean_ctor_set_uint8(x_1468, sizeof(void*)*10 + 4, x_1454);
lean_ctor_set_uint8(x_1468, sizeof(void*)*10 + 5, x_1455);
lean_ctor_set_uint8(x_1468, sizeof(void*)*10 + 6, x_1456);
lean_ctor_set_uint32(x_1468, sizeof(void*)*10, x_1466);
lean_ctor_set_uint8(x_1468, sizeof(void*)*10 + 7, x_1467);
lean_ctor_set(x_4, 0, x_1468);
x_3 = x_1419;
x_5 = x_1420;
goto _start;
}
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; uint8_t x_1481; uint8_t x_1482; uint8_t x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; uint32_t x_1494; uint8_t x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1470 = lean_ctor_get(x_4, 1);
x_1471 = lean_ctor_get(x_4, 2);
lean_inc(x_1471);
lean_inc(x_1470);
lean_dec(x_4);
x_1472 = lean_ctor_get(x_1421, 1);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1421, 2);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1421, 3);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1421, 4);
lean_inc(x_1475);
x_1476 = lean_ctor_get(x_1421, 5);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1421, 6);
lean_inc(x_1477);
x_1478 = lean_ctor_get(x_1421, 7);
lean_inc(x_1478);
x_1479 = lean_ctor_get(x_1421, 8);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1421, 9);
lean_inc(x_1480);
x_1481 = lean_ctor_get_uint8(x_1421, sizeof(void*)*10 + 4);
x_1482 = lean_ctor_get_uint8(x_1421, sizeof(void*)*10 + 5);
x_1483 = lean_ctor_get_uint8(x_1421, sizeof(void*)*10 + 6);
if (lean_is_exclusive(x_1421)) {
 lean_ctor_release(x_1421, 0);
 lean_ctor_release(x_1421, 1);
 lean_ctor_release(x_1421, 2);
 lean_ctor_release(x_1421, 3);
 lean_ctor_release(x_1421, 4);
 lean_ctor_release(x_1421, 5);
 lean_ctor_release(x_1421, 6);
 lean_ctor_release(x_1421, 7);
 lean_ctor_release(x_1421, 8);
 lean_ctor_release(x_1421, 9);
 x_1484 = x_1421;
} else {
 lean_dec_ref(x_1421);
 x_1484 = lean_box(0);
}
x_1485 = lean_ctor_get(x_1422, 0);
lean_inc(x_1485);
x_1486 = lean_ctor_get(x_1422, 1);
lean_inc(x_1486);
x_1487 = lean_ctor_get(x_1422, 2);
lean_inc(x_1487);
x_1488 = lean_ctor_get(x_1422, 3);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1422, 4);
lean_inc(x_1489);
if (lean_is_exclusive(x_1422)) {
 lean_ctor_release(x_1422, 0);
 lean_ctor_release(x_1422, 1);
 lean_ctor_release(x_1422, 2);
 lean_ctor_release(x_1422, 3);
 lean_ctor_release(x_1422, 4);
 x_1490 = x_1422;
} else {
 lean_dec_ref(x_1422);
 x_1490 = lean_box(0);
}
x_1491 = lean_unsigned_to_nat(1u);
x_1492 = lean_nat_add(x_1488, x_1491);
lean_dec(x_1488);
if (lean_is_scalar(x_1490)) {
 x_1493 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1493 = x_1490;
}
lean_ctor_set(x_1493, 0, x_1485);
lean_ctor_set(x_1493, 1, x_1486);
lean_ctor_set(x_1493, 2, x_1487);
lean_ctor_set(x_1493, 3, x_1492);
lean_ctor_set(x_1493, 4, x_1489);
x_1494 = 0;
x_1495 = 0;
if (lean_is_scalar(x_1484)) {
 x_1496 = lean_alloc_ctor(0, 10, 8);
} else {
 x_1496 = x_1484;
}
lean_ctor_set(x_1496, 0, x_1493);
lean_ctor_set(x_1496, 1, x_1472);
lean_ctor_set(x_1496, 2, x_1473);
lean_ctor_set(x_1496, 3, x_1474);
lean_ctor_set(x_1496, 4, x_1475);
lean_ctor_set(x_1496, 5, x_1476);
lean_ctor_set(x_1496, 6, x_1477);
lean_ctor_set(x_1496, 7, x_1478);
lean_ctor_set(x_1496, 8, x_1479);
lean_ctor_set(x_1496, 9, x_1480);
lean_ctor_set_uint8(x_1496, sizeof(void*)*10 + 4, x_1481);
lean_ctor_set_uint8(x_1496, sizeof(void*)*10 + 5, x_1482);
lean_ctor_set_uint8(x_1496, sizeof(void*)*10 + 6, x_1483);
lean_ctor_set_uint32(x_1496, sizeof(void*)*10, x_1494);
lean_ctor_set_uint8(x_1496, sizeof(void*)*10 + 7, x_1495);
x_1497 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1497, 0, x_1496);
lean_ctor_set(x_1497, 1, x_1470);
lean_ctor_set(x_1497, 2, x_1471);
x_3 = x_1419;
x_4 = x_1497;
x_5 = x_1420;
goto _start;
}
}
}
}
else
{
uint8_t x_1512; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1512 = !lean_is_exclusive(x_1410);
if (x_1512 == 0)
{
return x_1410;
}
else
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; 
x_1513 = lean_ctor_get(x_1410, 0);
x_1514 = lean_ctor_get(x_1410, 1);
lean_inc(x_1514);
lean_inc(x_1513);
lean_dec(x_1410);
x_1515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1515, 0, x_1513);
lean_ctor_set(x_1515, 1, x_1514);
return x_1515;
}
}
}
}
}
else
{
uint8_t x_1516; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1516 = !lean_is_exclusive(x_6);
if (x_1516 == 0)
{
return x_6;
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1517 = lean_ctor_get(x_6, 0);
x_1518 = lean_ctor_get(x_6, 1);
lean_inc(x_1518);
lean_inc(x_1517);
lean_dec(x_6);
x_1519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1519, 0, x_1517);
lean_ctor_set(x_1519, 1, x_1518);
return x_1519;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_1, x_2, x_3, x_4, x_5);
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
x_9 = l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_1, x_3, x_7, x_4, x_8);
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
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(x_7);
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
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(x_6);
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
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for minor premise '");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_29 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1(x_18, x_27, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_27, x_9);
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
x_35 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
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
x_48 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_47);
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
x_62 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_61);
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
x_73 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_72);
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
x_86 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_85);
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
x_102 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_101);
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
x_113 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_112);
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
x_125 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1(x_18, x_123, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_123, x_9);
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
x_131 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
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
x_144 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_143);
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
x_157 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_156);
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
x_172 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_171);
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
x_187 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1(x_18, x_185, x_9);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_185, x_9);
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
x_193 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
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
x_206 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_205);
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
x_220 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_219);
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
x_236 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_235);
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
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(x_7);
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
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for constructor '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
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
x_20 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(x_9, x_17, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_17, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
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
x_26 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_4);
lean_inc(x_1);
x_30 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_29, x_4, x_5);
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
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_38);
x_40 = l_Array_toList___rarg(x_39);
lean_dec(x_39);
x_41 = lean_array_push(x_12, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = l_Lean_Syntax_getArg(x_38, x_42);
lean_dec(x_38);
x_44 = lean_array_push(x_15, x_43);
lean_ctor_set(x_7, 0, x_44);
lean_ctor_set(x_2, 0, x_41);
x_3 = x_10;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_18);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_8, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_8, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = l_Lean_Syntax_inhabited;
x_52 = lean_array_get(x_51, x_17, x_50);
x_53 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_52);
x_54 = l_Array_toList___rarg(x_53);
lean_dec(x_53);
x_55 = lean_array_push(x_12, x_54);
x_56 = lean_unsigned_to_nat(3u);
x_57 = l_Lean_Syntax_getArg(x_52, x_56);
x_58 = lean_array_push(x_15, x_57);
x_59 = l_Array_eraseIdx___rarg(x_17, x_50);
lean_dec(x_50);
lean_ctor_set(x_21, 0, x_52);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_59);
lean_ctor_set(x_7, 0, x_58);
lean_ctor_set(x_2, 0, x_55);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_21, 0);
lean_inc(x_61);
lean_dec(x_21);
x_62 = l_Lean_Syntax_inhabited;
x_63 = lean_array_get(x_62, x_17, x_61);
x_64 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_63);
x_65 = l_Array_toList___rarg(x_64);
lean_dec(x_64);
x_66 = lean_array_push(x_12, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = l_Lean_Syntax_getArg(x_63, x_67);
x_69 = lean_array_push(x_15, x_68);
x_70 = l_Array_eraseIdx___rarg(x_17, x_61);
lean_dec(x_61);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_8, 1, x_71);
lean_ctor_set(x_8, 0, x_70);
lean_ctor_set(x_7, 0, x_69);
lean_ctor_set(x_2, 0, x_66);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_8);
x_73 = lean_ctor_get(x_21, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_74 = x_21;
} else {
 lean_dec_ref(x_21);
 x_74 = lean_box(0);
}
x_75 = l_Lean_Syntax_inhabited;
x_76 = lean_array_get(x_75, x_17, x_73);
x_77 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_76);
x_78 = l_Array_toList___rarg(x_77);
lean_dec(x_77);
x_79 = lean_array_push(x_12, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = l_Lean_Syntax_getArg(x_76, x_80);
x_82 = lean_array_push(x_15, x_81);
x_83 = l_Array_eraseIdx___rarg(x_17, x_73);
lean_dec(x_73);
if (lean_is_scalar(x_74)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_74;
}
lean_ctor_set(x_84, 0, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_7, 1, x_85);
lean_ctor_set(x_7, 0, x_82);
lean_ctor_set(x_2, 0, x_79);
x_3 = x_10;
goto _start;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_9);
x_87 = !lean_is_exclusive(x_8);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_8, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_8, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_20, 0);
lean_inc(x_90);
lean_dec(x_20);
x_91 = l_Lean_Syntax_inhabited;
x_92 = lean_array_get(x_91, x_17, x_90);
x_93 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_92);
x_94 = l_Array_toList___rarg(x_93);
lean_dec(x_93);
x_95 = lean_array_push(x_12, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = l_Lean_Syntax_getArg(x_92, x_96);
lean_dec(x_92);
x_98 = lean_array_push(x_15, x_97);
x_99 = l_Array_eraseIdx___rarg(x_17, x_90);
lean_dec(x_90);
lean_ctor_set(x_8, 0, x_99);
lean_ctor_set(x_7, 0, x_98);
lean_ctor_set(x_2, 0, x_95);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_8);
x_101 = lean_ctor_get(x_20, 0);
lean_inc(x_101);
lean_dec(x_20);
x_102 = l_Lean_Syntax_inhabited;
x_103 = lean_array_get(x_102, x_17, x_101);
x_104 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_103);
x_105 = l_Array_toList___rarg(x_104);
lean_dec(x_104);
x_106 = lean_array_push(x_12, x_105);
x_107 = lean_unsigned_to_nat(3u);
x_108 = l_Lean_Syntax_getArg(x_103, x_107);
lean_dec(x_103);
x_109 = lean_array_push(x_15, x_108);
x_110 = l_Array_eraseIdx___rarg(x_17, x_101);
lean_dec(x_101);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_18);
lean_ctor_set(x_7, 1, x_111);
lean_ctor_set(x_7, 0, x_109);
lean_ctor_set(x_2, 0, x_106);
x_3 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_7, 0);
lean_inc(x_113);
lean_dec(x_7);
x_114 = lean_ctor_get(x_8, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_8, 1);
lean_inc(x_115);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(x_9, x_114, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_114, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_dec(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_113);
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_8);
x_119 = l_Lean_Name_toString___closed__1;
x_120 = l_Lean_Name_toStringWithSep___main(x_119, x_9);
x_121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3;
x_124 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
x_126 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_4);
lean_inc(x_1);
x_127 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_126, x_4, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_2 = x_128;
x_3 = x_10;
x_5 = x_129;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_9);
x_135 = lean_ctor_get(x_115, 0);
lean_inc(x_135);
lean_dec(x_115);
x_136 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_135);
x_137 = l_Array_toList___rarg(x_136);
lean_dec(x_136);
x_138 = lean_array_push(x_12, x_137);
x_139 = lean_unsigned_to_nat(3u);
x_140 = l_Lean_Syntax_getArg(x_135, x_139);
lean_dec(x_135);
x_141 = lean_array_push(x_113, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_8);
lean_ctor_set(x_2, 1, x_142);
lean_ctor_set(x_2, 0, x_138);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_144 = x_8;
} else {
 lean_dec_ref(x_8);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_118, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_146 = x_118;
} else {
 lean_dec_ref(x_118);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Syntax_inhabited;
x_148 = lean_array_get(x_147, x_114, x_145);
x_149 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_148);
x_150 = l_Array_toList___rarg(x_149);
lean_dec(x_149);
x_151 = lean_array_push(x_12, x_150);
x_152 = lean_unsigned_to_nat(3u);
x_153 = l_Lean_Syntax_getArg(x_148, x_152);
x_154 = lean_array_push(x_113, x_153);
x_155 = l_Array_eraseIdx___rarg(x_114, x_145);
lean_dec(x_145);
if (lean_is_scalar(x_146)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_146;
}
lean_ctor_set(x_156, 0, x_148);
if (lean_is_scalar(x_144)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_144;
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_2, 1, x_158);
lean_ctor_set(x_2, 0, x_151);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_160 = x_8;
} else {
 lean_dec_ref(x_8);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_117, 0);
lean_inc(x_161);
lean_dec(x_117);
x_162 = l_Lean_Syntax_inhabited;
x_163 = lean_array_get(x_162, x_114, x_161);
x_164 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_163);
x_165 = l_Array_toList___rarg(x_164);
lean_dec(x_164);
x_166 = lean_array_push(x_12, x_165);
x_167 = lean_unsigned_to_nat(3u);
x_168 = l_Lean_Syntax_getArg(x_163, x_167);
lean_dec(x_163);
x_169 = lean_array_push(x_113, x_168);
x_170 = l_Array_eraseIdx___rarg(x_114, x_161);
lean_dec(x_161);
if (lean_is_scalar(x_160)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_160;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_115);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_2, 1, x_172);
lean_ctor_set(x_2, 0, x_166);
x_3 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_2, 0);
lean_inc(x_174);
lean_dec(x_2);
x_175 = lean_ctor_get(x_7, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_176 = x_7;
} else {
 lean_dec_ref(x_7);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_8, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_8, 1);
lean_inc(x_178);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(x_9, x_177, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_177, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_dec(x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_8);
x_182 = l_Lean_Name_toString___closed__1;
x_183 = l_Lean_Name_toStringWithSep___main(x_182, x_9);
x_184 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3;
x_187 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
x_189 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_4);
lean_inc(x_1);
x_190 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_189, x_4, x_5);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_2 = x_191;
x_3 = x_10;
x_5 = x_192;
goto _start;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_196 = x_190;
} else {
 lean_dec_ref(x_190);
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
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_9);
x_198 = lean_ctor_get(x_178, 0);
lean_inc(x_198);
lean_dec(x_178);
x_199 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_198);
x_200 = l_Array_toList___rarg(x_199);
lean_dec(x_199);
x_201 = lean_array_push(x_174, x_200);
x_202 = lean_unsigned_to_nat(3u);
x_203 = l_Lean_Syntax_getArg(x_198, x_202);
lean_dec(x_198);
x_204 = lean_array_push(x_175, x_203);
if (lean_is_scalar(x_176)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_176;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_8);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_205);
x_2 = x_206;
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_178);
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_208 = x_8;
} else {
 lean_dec_ref(x_8);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_181, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_210 = x_181;
} else {
 lean_dec_ref(x_181);
 x_210 = lean_box(0);
}
x_211 = l_Lean_Syntax_inhabited;
x_212 = lean_array_get(x_211, x_177, x_209);
x_213 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_212);
x_214 = l_Array_toList___rarg(x_213);
lean_dec(x_213);
x_215 = lean_array_push(x_174, x_214);
x_216 = lean_unsigned_to_nat(3u);
x_217 = l_Lean_Syntax_getArg(x_212, x_216);
x_218 = lean_array_push(x_175, x_217);
x_219 = l_Array_eraseIdx___rarg(x_177, x_209);
lean_dec(x_209);
if (lean_is_scalar(x_210)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_210;
}
lean_ctor_set(x_220, 0, x_212);
if (lean_is_scalar(x_208)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_208;
}
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
if (lean_is_scalar(x_176)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_176;
}
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_215);
lean_ctor_set(x_223, 1, x_222);
x_2 = x_223;
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_225 = x_8;
} else {
 lean_dec_ref(x_8);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_180, 0);
lean_inc(x_226);
lean_dec(x_180);
x_227 = l_Lean_Syntax_inhabited;
x_228 = lean_array_get(x_227, x_177, x_226);
x_229 = l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_228);
x_230 = l_Array_toList___rarg(x_229);
lean_dec(x_229);
x_231 = lean_array_push(x_174, x_230);
x_232 = lean_unsigned_to_nat(3u);
x_233 = l_Lean_Syntax_getArg(x_228, x_232);
lean_dec(x_228);
x_234 = lean_array_push(x_175, x_233);
x_235 = l_Array_eraseIdx___rarg(x_177, x_226);
lean_dec(x_226);
if (lean_is_scalar(x_225)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_225;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_178);
if (lean_is_scalar(x_176)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_176;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set(x_238, 1, x_237);
x_2 = x_238;
x_3 = x_10;
goto _start;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unused alternative");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_19 = l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
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
x_36 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3(x_1, x_15, x_29, x_35, x_35, x_34, x_3, x_30);
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
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
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_36);
x_47 = l_Lean_Syntax_inhabited;
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get(x_47, x_45, x_48);
lean_dec(x_45);
x_50 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_51 = l_Lean_Elab_Tactic_throwError___rarg(x_49, x_50, x_3, x_41);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_44);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_17);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_45);
lean_dec(x_3);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_43);
lean_ctor_set(x_62, 2, x_44);
lean_ctor_set(x_36, 0, x_62);
return x_36;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_dec(x_36);
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
lean_dec(x_37);
x_65 = lean_ctor_get(x_38, 0);
lean_inc(x_65);
lean_dec(x_38);
x_66 = lean_ctor_get(x_39, 0);
lean_inc(x_66);
lean_dec(x_39);
x_67 = l_Array_isEmpty___rarg(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = l_Lean_Syntax_inhabited;
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_array_get(x_68, x_66, x_69);
lean_dec(x_66);
x_71 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_72 = l_Lean_Elab_Tactic_throwError___rarg(x_70, x_71, x_3, x_63);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_17);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_65);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_17);
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_66);
lean_dec(x_3);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_17);
lean_ctor_set(x_81, 1, x_64);
lean_ctor_set(x_81, 2, x_65);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_63);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_17);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_36);
if (x_83 == 0)
{
return x_36;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_36, 0);
x_85 = lean_ctor_get(x_36, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_36);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_28);
if (x_87 == 0)
{
return x_28;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_28, 0);
x_89 = lean_ctor_get(x_28, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_28);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_21, 0);
lean_inc(x_91);
lean_dec(x_21);
lean_inc(x_17);
x_92 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 3, 1);
lean_closure_set(x_92, 0, x_17);
lean_inc(x_1);
x_93 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_93, 0, x_1);
lean_closure_set(x_93, 1, x_92);
lean_inc(x_3);
x_94 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_91, x_93, x_3, x_22);
lean_dec(x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_19);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Array_empty___closed__1;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_get_size(x_95);
lean_inc(x_3);
lean_inc(x_102);
x_103 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3(x_1, x_15, x_95, x_102, x_102, x_101, x_3, x_96);
lean_dec(x_102);
lean_dec(x_95);
lean_dec(x_15);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_108 = x_103;
} else {
 lean_dec_ref(x_103);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
lean_dec(x_104);
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = l_Array_isEmpty___rarg(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_108);
x_113 = l_Lean_Syntax_inhabited;
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_array_get(x_113, x_111, x_114);
lean_dec(x_111);
x_116 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_117 = l_Lean_Elab_Tactic_throwError___rarg(x_115, x_116, x_3, x_107);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_17);
lean_ctor_set(x_120, 1, x_109);
lean_ctor_set(x_120, 2, x_110);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_17);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
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
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_111);
lean_dec(x_3);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_17);
lean_ctor_set(x_126, 1, x_109);
lean_ctor_set(x_126, 2, x_110);
if (lean_is_scalar(x_108)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_108;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_107);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_17);
lean_dec(x_3);
x_128 = lean_ctor_get(x_103, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_103, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_130 = x_103;
} else {
 lean_dec_ref(x_103);
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
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_132 = lean_ctor_get(x_94, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_94, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_134 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_20);
if (x_136 == 0)
{
return x_20;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_20, 0);
x_138 = lean_ctor_get(x_20, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_140 = l_Array_empty___closed__1;
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_17);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_13, 0, x_141);
return x_13;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_13, 0);
x_143 = lean_ctor_get(x_13, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_13);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = l_Lean_Syntax_isNone(x_8);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_147 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_143);
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
lean_inc(x_1);
x_153 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_153, 0, x_1);
lean_closure_set(x_153, 1, x_152);
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
x_163 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3(x_1, x_142, x_155, x_162, x_162, x_161, x_3, x_156);
lean_dec(x_162);
lean_dec(x_155);
lean_dec(x_142);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
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
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_168);
x_173 = l_Lean_Syntax_inhabited;
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_array_get(x_173, x_171, x_174);
lean_dec(x_171);
x_176 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_177 = l_Lean_Elab_Tactic_throwError___rarg(x_175, x_176, x_3, x_167);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_144);
lean_ctor_set(x_180, 1, x_169);
lean_ctor_set(x_180, 2, x_170);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_144);
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_184 = x_177;
} else {
 lean_dec_ref(x_177);
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
lean_object* x_186; lean_object* x_187; 
lean_dec(x_171);
lean_dec(x_3);
x_186 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_186, 0, x_144);
lean_ctor_set(x_186, 1, x_169);
lean_ctor_set(x_186, 2, x_170);
if (lean_is_scalar(x_168)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_168;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_167);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_144);
lean_dec(x_3);
x_188 = lean_ctor_get(x_163, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_163, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_190 = x_163;
} else {
 lean_dec_ref(x_163);
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
lean_dec(x_151);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_3);
lean_dec(x_1);
x_192 = lean_ctor_get(x_154, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_154, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_194 = x_154;
} else {
 lean_dec_ref(x_154);
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
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_3);
lean_dec(x_1);
x_196 = lean_ctor_get(x_147, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_147, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_198 = x_147;
} else {
 lean_dec_ref(x_147);
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
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_200 = l_Array_empty___closed__1;
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_144);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_143);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_13);
if (x_203 == 0)
{
return x_13;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_13, 0);
x_205 = lean_ctor_get(x_13, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_13);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; 
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_207 = l_Lean_Elab_Tactic_getInductiveValFromMajor(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_207, 1);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Lean_mkRecFor___closed__1;
x_214 = lean_name_mk_string(x_212, x_213);
x_215 = l_Lean_Syntax_isNone(x_8);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_free_object(x_207);
x_216 = lean_ctor_get(x_209, 4);
lean_inc(x_216);
lean_dec(x_209);
x_217 = l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
x_218 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_219 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_216, x_217, x_218, x_3, x_210);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_217);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Array_empty___closed__1;
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
lean_inc(x_3);
x_226 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5(x_1, x_225, x_216, x_3, x_220);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = !lean_is_exclusive(x_226);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_231 = lean_ctor_get(x_226, 1);
x_232 = lean_ctor_get(x_226, 0);
lean_dec(x_232);
x_233 = lean_ctor_get(x_227, 0);
lean_inc(x_233);
lean_dec(x_227);
x_234 = lean_ctor_get(x_228, 0);
lean_inc(x_234);
lean_dec(x_228);
x_235 = lean_ctor_get(x_229, 0);
lean_inc(x_235);
lean_dec(x_229);
x_236 = l_Array_isEmpty___rarg(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_226);
x_237 = l_Lean_Syntax_inhabited;
x_238 = lean_array_get(x_237, x_235, x_218);
lean_dec(x_235);
x_239 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_240 = l_Lean_Elab_Tactic_throwError___rarg(x_238, x_239, x_3, x_231);
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_240, 0);
lean_dec(x_242);
x_243 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_243, 0, x_214);
lean_ctor_set(x_243, 1, x_233);
lean_ctor_set(x_243, 2, x_234);
lean_ctor_set(x_240, 0, x_243);
return x_240;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_245, 0, x_214);
lean_ctor_set(x_245, 1, x_233);
lean_ctor_set(x_245, 2, x_234);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_214);
x_247 = !lean_is_exclusive(x_240);
if (x_247 == 0)
{
return x_240;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_240, 0);
x_249 = lean_ctor_get(x_240, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_240);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; 
lean_dec(x_235);
lean_dec(x_3);
x_251 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_251, 0, x_214);
lean_ctor_set(x_251, 1, x_233);
lean_ctor_set(x_251, 2, x_234);
lean_ctor_set(x_226, 0, x_251);
return x_226;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_252 = lean_ctor_get(x_226, 1);
lean_inc(x_252);
lean_dec(x_226);
x_253 = lean_ctor_get(x_227, 0);
lean_inc(x_253);
lean_dec(x_227);
x_254 = lean_ctor_get(x_228, 0);
lean_inc(x_254);
lean_dec(x_228);
x_255 = lean_ctor_get(x_229, 0);
lean_inc(x_255);
lean_dec(x_229);
x_256 = l_Array_isEmpty___rarg(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = l_Lean_Syntax_inhabited;
x_258 = lean_array_get(x_257, x_255, x_218);
lean_dec(x_255);
x_259 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_260 = l_Lean_Elab_Tactic_throwError___rarg(x_258, x_259, x_3, x_252);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_262 = x_260;
} else {
 lean_dec_ref(x_260);
 x_262 = lean_box(0);
}
x_263 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_263, 0, x_214);
lean_ctor_set(x_263, 1, x_253);
lean_ctor_set(x_263, 2, x_254);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_261);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_214);
x_265 = lean_ctor_get(x_260, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_260, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_267 = x_260;
} else {
 lean_dec_ref(x_260);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_255);
lean_dec(x_3);
x_269 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_269, 0, x_214);
lean_ctor_set(x_269, 1, x_253);
lean_ctor_set(x_269, 2, x_254);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_252);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_214);
lean_dec(x_3);
x_271 = !lean_is_exclusive(x_226);
if (x_271 == 0)
{
return x_226;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_226, 0);
x_273 = lean_ctor_get(x_226, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_226);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_3);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_219);
if (x_275 == 0)
{
return x_219;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_219, 0);
x_277 = lean_ctor_get(x_219, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_219);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_209);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_279 = l_Array_empty___closed__1;
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_214);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_279);
lean_ctor_set(x_207, 0, x_280);
return x_207;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_281 = lean_ctor_get(x_207, 0);
x_282 = lean_ctor_get(x_207, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_207);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec(x_283);
x_285 = l_Lean_mkRecFor___closed__1;
x_286 = lean_name_mk_string(x_284, x_285);
x_287 = l_Lean_Syntax_isNone(x_8);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_281, 4);
lean_inc(x_288);
lean_dec(x_281);
x_289 = l___private_Init_Lean_Elab_Tactic_Induction_7__getAlts(x_8);
lean_dec(x_8);
x_290 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_291 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_288, x_289, x_290, x_3, x_282);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Array_empty___closed__1;
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
lean_inc(x_3);
x_298 = l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5(x_1, x_297, x_288, x_3, x_292);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_298, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_303 = x_298;
} else {
 lean_dec_ref(x_298);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_299, 0);
lean_inc(x_304);
lean_dec(x_299);
x_305 = lean_ctor_get(x_300, 0);
lean_inc(x_305);
lean_dec(x_300);
x_306 = lean_ctor_get(x_301, 0);
lean_inc(x_306);
lean_dec(x_301);
x_307 = l_Array_isEmpty___rarg(x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_303);
x_308 = l_Lean_Syntax_inhabited;
x_309 = lean_array_get(x_308, x_306, x_290);
lean_dec(x_306);
x_310 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3;
x_311 = l_Lean_Elab_Tactic_throwError___rarg(x_309, x_310, x_3, x_302);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_286);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_312);
return x_315;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_286);
x_316 = lean_ctor_get(x_311, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_311, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_318 = x_311;
} else {
 lean_dec_ref(x_311);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_306);
lean_dec(x_3);
x_320 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_320, 0, x_286);
lean_ctor_set(x_320, 1, x_304);
lean_ctor_set(x_320, 2, x_305);
if (lean_is_scalar(x_303)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_303;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_302);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_286);
lean_dec(x_3);
x_322 = lean_ctor_get(x_298, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_298, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_324 = x_298;
} else {
 lean_dec_ref(x_298);
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
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_286);
lean_dec(x_3);
lean_dec(x_1);
x_326 = lean_ctor_get(x_291, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_291, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_328 = x_291;
} else {
 lean_dec_ref(x_291);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_281);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_330 = l_Array_empty___closed__1;
x_331 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_331, 0, x_286);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_331, 2, x_330);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_282);
return x_332;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_333 = !lean_is_exclusive(x_207);
if (x_333 == 0)
{
return x_207;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_207, 0);
x_335 = lean_ctor_get(x_207, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_207);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = 0;
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_Lean_Elab_Tactic_elabTerm(x_1, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_Elab_Tactic_ensureHasType(x_1, x_7, x_10, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_13);
x_15 = l_Lean_Elab_Tactic_assignExprMVar(x_2, x_13, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_4);
x_17 = l_Lean_Elab_Tactic_collectMVars(x_1, x_13, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_inc(x_18);
x_22 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_20, x_21, x_18, x_4, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Tactic_appendGoals(x_18, x_4, x_23);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
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
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_Meta_InductionSubgoal_inhabited;
x_14 = lean_array_get(x_13, x_1, x_12);
x_15 = l_Lean_Syntax_inhabited;
x_16 = lean_array_get(x_15, x_2, x_12);
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1___lambda__1), 5, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_17);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_5);
x_21 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_17, x_20, x_5, x_6);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_4 = x_10;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_Meta_InductionSubgoal_inhabited;
x_14 = lean_array_get(x_13, x_1, x_12);
x_15 = l_Lean_Syntax_inhabited;
x_16 = lean_array_get(x_15, x_2, x_12);
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1___lambda__1), 5, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_17);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_5);
x_21 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_17, x_20, x_5, x_6);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_4 = x_10;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__3(lean_object* x_1) {
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
x_7 = l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__3(x_5);
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
x_11 = l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mistmatch on the number of subgoals produced (");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") and ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternatives provided (");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_1, x_2, x_3, x_4);
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
x_8 = l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo(x_1, x_6, x_3, x_9);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_11, 2);
lean_inc(x_26);
lean_dec(x_11);
x_27 = l_Array_isEmpty___rarg(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_array_get_size(x_26);
x_29 = lean_array_get_size(x_24);
x_30 = lean_nat_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc(x_29);
x_31 = l_Nat_repr(x_29);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__3;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__6;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__9;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Nat_repr(x_28);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__10;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_3);
x_46 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_45, x_3, x_25);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_29);
x_48 = l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1(x_24, x_26, x_29, x_29, x_3, x_47);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_28);
lean_dec(x_1);
lean_inc(x_29);
x_53 = l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__2(x_24, x_26, x_29, x_29, x_3, x_25);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_54 = l_Array_toList___rarg(x_24);
lean_dec(x_24);
x_55 = l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__3(x_54);
x_56 = l_Lean_Elab_Tactic_setGoals(x_55, x_3, x_25);
lean_dec(x_3);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_13);
if (x_61 == 0)
{
return x_13;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_13, 0);
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_13);
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
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_10);
if (x_65 == 0)
{
return x_10;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_10, 0);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_10);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
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
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
return x_5;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
x_5 = l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor), 5, 3);
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
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_Elab_Tactic_evalInduction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalInduction");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Induction(lean_object*);
lean_object* initialize_Init_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Init_Lean_Elab_Tactic_Generalize(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Tactic_Generalize(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1);
l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2 = _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2);
l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3 = _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3);
l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1);
l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1);
l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1);
l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1);
l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2 = _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2);
l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3 = _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3);
l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4 = _init_l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4);
l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1 = _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__1);
l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2 = _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2);
l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3 = _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3);
l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4 = _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4();
lean_mark_persistent(l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__4);
l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5 = _init_l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5();
lean_mark_persistent(l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3);
l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1);
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
l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1);
l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__2 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__2();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__2);
l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3);
l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4);
l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__5 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__5();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__5);
l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6);
l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__1);
l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__2 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__2);
l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5___closed__3);
l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1);
l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__2 = _init_l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__2);
l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3 = _init_l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__3);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__3);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__4);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__5);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__6);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__7);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__8 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__8);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__9 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__9);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__10 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__10);
l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
