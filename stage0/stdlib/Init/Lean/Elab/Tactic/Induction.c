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
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor(lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__3;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__4;
extern lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_9__getAltVarNames___boxed(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__2;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalInduction(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__6;
uint8_t l_List_foldr___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___spec__3___closed__3;
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
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
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__8;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__4;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__3;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___closed__5;
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Induction_13__getRecInfo___closed__1;
lean_object* l_Lean_Meta_getParamNames(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_29 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_ctor_get(x_93, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 4);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_nat_dec_eq(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
x_20 = x_18;
goto block_91;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_98 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_97, x_4, x_18);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_20 = x_99;
goto block_91;
}
else
{
uint8_t x_100; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_91:
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 3);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
lean_ctor_set(x_22, 3, x_30);
x_3 = x_19;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 3);
x_36 = lean_ctor_get(x_22, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_21, 0, x_39);
x_3 = x_19;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_41 = lean_ctor_get(x_21, 1);
x_42 = lean_ctor_get(x_21, 2);
x_43 = lean_ctor_get(x_21, 3);
x_44 = lean_ctor_get(x_21, 4);
x_45 = lean_ctor_get(x_21, 5);
x_46 = lean_ctor_get(x_21, 6);
x_47 = lean_ctor_get(x_21, 7);
x_48 = lean_ctor_get(x_21, 8);
x_49 = lean_ctor_get(x_21, 9);
x_50 = lean_ctor_get_uint8(x_21, sizeof(void*)*10);
x_51 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 1);
x_52 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_22, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_22, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_22, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 x_58 = x_22;
} else {
 lean_dec_ref(x_22);
 x_58 = lean_box(0);
}
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_56, x_59);
lean_dec(x_56);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 5, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_57);
x_62 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_62, 2, x_42);
lean_ctor_set(x_62, 3, x_43);
lean_ctor_set(x_62, 4, x_44);
lean_ctor_set(x_62, 5, x_45);
lean_ctor_set(x_62, 6, x_46);
lean_ctor_set(x_62, 7, x_47);
lean_ctor_set(x_62, 8, x_48);
lean_ctor_set(x_62, 9, x_49);
lean_ctor_set_uint8(x_62, sizeof(void*)*10, x_50);
lean_ctor_set_uint8(x_62, sizeof(void*)*10 + 1, x_51);
lean_ctor_set_uint8(x_62, sizeof(void*)*10 + 2, x_52);
lean_ctor_set(x_4, 0, x_62);
x_3 = x_19;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_64 = lean_ctor_get(x_4, 1);
x_65 = lean_ctor_get(x_4, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_21, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_21, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_21, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_21, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_21, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_21, 7);
lean_inc(x_72);
x_73 = lean_ctor_get(x_21, 8);
lean_inc(x_73);
x_74 = lean_ctor_get(x_21, 9);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_21, sizeof(void*)*10);
x_76 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 1);
x_77 = lean_ctor_get_uint8(x_21, sizeof(void*)*10 + 2);
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
 x_78 = x_21;
} else {
 lean_dec_ref(x_21);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_22, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_22, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_22, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_22, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 x_84 = x_22;
} else {
 lean_dec_ref(x_22);
 x_84 = lean_box(0);
}
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_82, x_85);
lean_dec(x_82);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 5, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_80);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set(x_87, 4, x_83);
if (lean_is_scalar(x_78)) {
 x_88 = lean_alloc_ctor(0, 10, 3);
} else {
 x_88 = x_78;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_66);
lean_ctor_set(x_88, 2, x_67);
lean_ctor_set(x_88, 3, x_68);
lean_ctor_set(x_88, 4, x_69);
lean_ctor_set(x_88, 5, x_70);
lean_ctor_set(x_88, 6, x_71);
lean_ctor_set(x_88, 7, x_72);
lean_ctor_set(x_88, 8, x_73);
lean_ctor_set(x_88, 9, x_74);
lean_ctor_set_uint8(x_88, sizeof(void*)*10, x_75);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 1, x_76);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 2, x_77);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_64);
lean_ctor_set(x_89, 2, x_65);
x_3 = x_19;
x_4 = x_89;
x_5 = x_20;
goto _start;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_10);
if (x_104 == 0)
{
return x_10;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_10, 0);
x_106 = lean_ctor_get(x_10, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_10);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
case 1:
{
lean_object* x_108; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_108 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
x_112 = lean_box(0);
lean_ctor_set(x_108, 0, x_112);
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
lean_dec(x_108);
x_117 = lean_ctor_get(x_109, 0);
lean_inc(x_117);
lean_dec(x_109);
x_190 = lean_ctor_get(x_4, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_ctor_get(x_191, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 4);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_nat_dec_eq(x_192, x_193);
lean_dec(x_193);
lean_dec(x_192);
if (x_194 == 0)
{
x_118 = x_116;
goto block_189;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_196 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_195, x_4, x_116);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_118 = x_197;
goto block_189;
}
else
{
uint8_t x_198; 
lean_dec(x_117);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_196);
if (x_198 == 0)
{
return x_196;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_196, 0);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_196);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
block_189:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_4, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = !lean_is_exclusive(x_4);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_4, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_119);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_119, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_120);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_120, 3);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_add(x_126, x_127);
lean_dec(x_126);
lean_ctor_set(x_120, 3, x_128);
x_3 = x_117;
x_5 = x_118;
goto _start;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
x_132 = lean_ctor_get(x_120, 2);
x_133 = lean_ctor_get(x_120, 3);
x_134 = lean_ctor_get(x_120, 4);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_133, x_135);
lean_dec(x_133);
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_131);
lean_ctor_set(x_137, 2, x_132);
lean_ctor_set(x_137, 3, x_136);
lean_ctor_set(x_137, 4, x_134);
lean_ctor_set(x_119, 0, x_137);
x_3 = x_117;
x_5 = x_118;
goto _start;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_139 = lean_ctor_get(x_119, 1);
x_140 = lean_ctor_get(x_119, 2);
x_141 = lean_ctor_get(x_119, 3);
x_142 = lean_ctor_get(x_119, 4);
x_143 = lean_ctor_get(x_119, 5);
x_144 = lean_ctor_get(x_119, 6);
x_145 = lean_ctor_get(x_119, 7);
x_146 = lean_ctor_get(x_119, 8);
x_147 = lean_ctor_get(x_119, 9);
x_148 = lean_ctor_get_uint8(x_119, sizeof(void*)*10);
x_149 = lean_ctor_get_uint8(x_119, sizeof(void*)*10 + 1);
x_150 = lean_ctor_get_uint8(x_119, sizeof(void*)*10 + 2);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_119);
x_151 = lean_ctor_get(x_120, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_120, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_120, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_120, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_120, 4);
lean_inc(x_155);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_156 = x_120;
} else {
 lean_dec_ref(x_120);
 x_156 = lean_box(0);
}
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_add(x_154, x_157);
lean_dec(x_154);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_151);
lean_ctor_set(x_159, 1, x_152);
lean_ctor_set(x_159, 2, x_153);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set(x_159, 4, x_155);
x_160 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_139);
lean_ctor_set(x_160, 2, x_140);
lean_ctor_set(x_160, 3, x_141);
lean_ctor_set(x_160, 4, x_142);
lean_ctor_set(x_160, 5, x_143);
lean_ctor_set(x_160, 6, x_144);
lean_ctor_set(x_160, 7, x_145);
lean_ctor_set(x_160, 8, x_146);
lean_ctor_set(x_160, 9, x_147);
lean_ctor_set_uint8(x_160, sizeof(void*)*10, x_148);
lean_ctor_set_uint8(x_160, sizeof(void*)*10 + 1, x_149);
lean_ctor_set_uint8(x_160, sizeof(void*)*10 + 2, x_150);
lean_ctor_set(x_4, 0, x_160);
x_3 = x_117;
x_5 = x_118;
goto _start;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_162 = lean_ctor_get(x_4, 1);
x_163 = lean_ctor_get(x_4, 2);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_4);
x_164 = lean_ctor_get(x_119, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_119, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_119, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_119, 4);
lean_inc(x_167);
x_168 = lean_ctor_get(x_119, 5);
lean_inc(x_168);
x_169 = lean_ctor_get(x_119, 6);
lean_inc(x_169);
x_170 = lean_ctor_get(x_119, 7);
lean_inc(x_170);
x_171 = lean_ctor_get(x_119, 8);
lean_inc(x_171);
x_172 = lean_ctor_get(x_119, 9);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_119, sizeof(void*)*10);
x_174 = lean_ctor_get_uint8(x_119, sizeof(void*)*10 + 1);
x_175 = lean_ctor_get_uint8(x_119, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 lean_ctor_release(x_119, 6);
 lean_ctor_release(x_119, 7);
 lean_ctor_release(x_119, 8);
 lean_ctor_release(x_119, 9);
 x_176 = x_119;
} else {
 lean_dec_ref(x_119);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_120, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_120, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_120, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_120, 3);
lean_inc(x_180);
x_181 = lean_ctor_get(x_120, 4);
lean_inc(x_181);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_182 = x_120;
} else {
 lean_dec_ref(x_120);
 x_182 = lean_box(0);
}
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_add(x_180, x_183);
lean_dec(x_180);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_182;
}
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_178);
lean_ctor_set(x_185, 2, x_179);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_185, 4, x_181);
if (lean_is_scalar(x_176)) {
 x_186 = lean_alloc_ctor(0, 10, 3);
} else {
 x_186 = x_176;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_164);
lean_ctor_set(x_186, 2, x_165);
lean_ctor_set(x_186, 3, x_166);
lean_ctor_set(x_186, 4, x_167);
lean_ctor_set(x_186, 5, x_168);
lean_ctor_set(x_186, 6, x_169);
lean_ctor_set(x_186, 7, x_170);
lean_ctor_set(x_186, 8, x_171);
lean_ctor_set(x_186, 9, x_172);
lean_ctor_set_uint8(x_186, sizeof(void*)*10, x_173);
lean_ctor_set_uint8(x_186, sizeof(void*)*10 + 1, x_174);
lean_ctor_set_uint8(x_186, sizeof(void*)*10 + 2, x_175);
x_187 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_162);
lean_ctor_set(x_187, 2, x_163);
x_3 = x_117;
x_4 = x_187;
x_5 = x_118;
goto _start;
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_108);
if (x_202 == 0)
{
return x_108;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_108, 0);
x_204 = lean_ctor_get(x_108, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_108);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
case 2:
{
lean_object* x_206; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_206 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_206, 0);
lean_dec(x_209);
x_210 = lean_box(0);
lean_ctor_set(x_206, 0, x_210);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_dec(x_206);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_214 = lean_ctor_get(x_206, 1);
lean_inc(x_214);
lean_dec(x_206);
x_215 = lean_ctor_get(x_207, 0);
lean_inc(x_215);
lean_dec(x_207);
x_288 = lean_ctor_get(x_4, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec(x_288);
x_290 = lean_ctor_get(x_289, 3);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 4);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_nat_dec_eq(x_290, x_291);
lean_dec(x_291);
lean_dec(x_290);
if (x_292 == 0)
{
x_216 = x_214;
goto block_287;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_294 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_293, x_4, x_214);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_216 = x_295;
goto block_287;
}
else
{
uint8_t x_296; 
lean_dec(x_215);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_294);
if (x_296 == 0)
{
return x_294;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_294, 0);
x_298 = lean_ctor_get(x_294, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_294);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
block_287:
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_4, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = !lean_is_exclusive(x_4);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_4, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_217);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_217, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_218);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_218, 3);
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_nat_add(x_224, x_225);
lean_dec(x_224);
lean_ctor_set(x_218, 3, x_226);
x_3 = x_215;
x_5 = x_216;
goto _start;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_218, 0);
x_229 = lean_ctor_get(x_218, 1);
x_230 = lean_ctor_get(x_218, 2);
x_231 = lean_ctor_get(x_218, 3);
x_232 = lean_ctor_get(x_218, 4);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_218);
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_add(x_231, x_233);
lean_dec(x_231);
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_228);
lean_ctor_set(x_235, 1, x_229);
lean_ctor_set(x_235, 2, x_230);
lean_ctor_set(x_235, 3, x_234);
lean_ctor_set(x_235, 4, x_232);
lean_ctor_set(x_217, 0, x_235);
x_3 = x_215;
x_5 = x_216;
goto _start;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_237 = lean_ctor_get(x_217, 1);
x_238 = lean_ctor_get(x_217, 2);
x_239 = lean_ctor_get(x_217, 3);
x_240 = lean_ctor_get(x_217, 4);
x_241 = lean_ctor_get(x_217, 5);
x_242 = lean_ctor_get(x_217, 6);
x_243 = lean_ctor_get(x_217, 7);
x_244 = lean_ctor_get(x_217, 8);
x_245 = lean_ctor_get(x_217, 9);
x_246 = lean_ctor_get_uint8(x_217, sizeof(void*)*10);
x_247 = lean_ctor_get_uint8(x_217, sizeof(void*)*10 + 1);
x_248 = lean_ctor_get_uint8(x_217, sizeof(void*)*10 + 2);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_217);
x_249 = lean_ctor_get(x_218, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_218, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_218, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_218, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_218, 4);
lean_inc(x_253);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 lean_ctor_release(x_218, 4);
 x_254 = x_218;
} else {
 lean_dec_ref(x_218);
 x_254 = lean_box(0);
}
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_add(x_252, x_255);
lean_dec(x_252);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 5, 0);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_249);
lean_ctor_set(x_257, 1, x_250);
lean_ctor_set(x_257, 2, x_251);
lean_ctor_set(x_257, 3, x_256);
lean_ctor_set(x_257, 4, x_253);
x_258 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_237);
lean_ctor_set(x_258, 2, x_238);
lean_ctor_set(x_258, 3, x_239);
lean_ctor_set(x_258, 4, x_240);
lean_ctor_set(x_258, 5, x_241);
lean_ctor_set(x_258, 6, x_242);
lean_ctor_set(x_258, 7, x_243);
lean_ctor_set(x_258, 8, x_244);
lean_ctor_set(x_258, 9, x_245);
lean_ctor_set_uint8(x_258, sizeof(void*)*10, x_246);
lean_ctor_set_uint8(x_258, sizeof(void*)*10 + 1, x_247);
lean_ctor_set_uint8(x_258, sizeof(void*)*10 + 2, x_248);
lean_ctor_set(x_4, 0, x_258);
x_3 = x_215;
x_5 = x_216;
goto _start;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_260 = lean_ctor_get(x_4, 1);
x_261 = lean_ctor_get(x_4, 2);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_4);
x_262 = lean_ctor_get(x_217, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_217, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_217, 3);
lean_inc(x_264);
x_265 = lean_ctor_get(x_217, 4);
lean_inc(x_265);
x_266 = lean_ctor_get(x_217, 5);
lean_inc(x_266);
x_267 = lean_ctor_get(x_217, 6);
lean_inc(x_267);
x_268 = lean_ctor_get(x_217, 7);
lean_inc(x_268);
x_269 = lean_ctor_get(x_217, 8);
lean_inc(x_269);
x_270 = lean_ctor_get(x_217, 9);
lean_inc(x_270);
x_271 = lean_ctor_get_uint8(x_217, sizeof(void*)*10);
x_272 = lean_ctor_get_uint8(x_217, sizeof(void*)*10 + 1);
x_273 = lean_ctor_get_uint8(x_217, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 lean_ctor_release(x_217, 6);
 lean_ctor_release(x_217, 7);
 lean_ctor_release(x_217, 8);
 lean_ctor_release(x_217, 9);
 x_274 = x_217;
} else {
 lean_dec_ref(x_217);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_218, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_218, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_218, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_218, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_218, 4);
lean_inc(x_279);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 lean_ctor_release(x_218, 4);
 x_280 = x_218;
} else {
 lean_dec_ref(x_218);
 x_280 = lean_box(0);
}
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_nat_add(x_278, x_281);
lean_dec(x_278);
if (lean_is_scalar(x_280)) {
 x_283 = lean_alloc_ctor(0, 5, 0);
} else {
 x_283 = x_280;
}
lean_ctor_set(x_283, 0, x_275);
lean_ctor_set(x_283, 1, x_276);
lean_ctor_set(x_283, 2, x_277);
lean_ctor_set(x_283, 3, x_282);
lean_ctor_set(x_283, 4, x_279);
if (lean_is_scalar(x_274)) {
 x_284 = lean_alloc_ctor(0, 10, 3);
} else {
 x_284 = x_274;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_262);
lean_ctor_set(x_284, 2, x_263);
lean_ctor_set(x_284, 3, x_264);
lean_ctor_set(x_284, 4, x_265);
lean_ctor_set(x_284, 5, x_266);
lean_ctor_set(x_284, 6, x_267);
lean_ctor_set(x_284, 7, x_268);
lean_ctor_set(x_284, 8, x_269);
lean_ctor_set(x_284, 9, x_270);
lean_ctor_set_uint8(x_284, sizeof(void*)*10, x_271);
lean_ctor_set_uint8(x_284, sizeof(void*)*10 + 1, x_272);
lean_ctor_set_uint8(x_284, sizeof(void*)*10 + 2, x_273);
x_285 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_260);
lean_ctor_set(x_285, 2, x_261);
x_3 = x_215;
x_4 = x_285;
x_5 = x_216;
goto _start;
}
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
return x_206;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_206, 0);
x_302 = lean_ctor_get(x_206, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_206);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
case 3:
{
lean_object* x_304; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_304 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_304);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_304, 0);
lean_dec(x_307);
x_308 = lean_box(0);
lean_ctor_set(x_304, 0, x_308);
return x_304;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_304, 1);
lean_inc(x_309);
lean_dec(x_304);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_312 = lean_ctor_get(x_304, 1);
lean_inc(x_312);
lean_dec(x_304);
x_313 = lean_ctor_get(x_305, 0);
lean_inc(x_313);
lean_dec(x_305);
x_386 = lean_ctor_get(x_4, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec(x_386);
x_388 = lean_ctor_get(x_387, 3);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 4);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_nat_dec_eq(x_388, x_389);
lean_dec(x_389);
lean_dec(x_388);
if (x_390 == 0)
{
x_314 = x_312;
goto block_385;
}
else
{
lean_object* x_391; lean_object* x_392; 
x_391 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_392 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_391, x_4, x_312);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
lean_dec(x_392);
x_314 = x_393;
goto block_385;
}
else
{
uint8_t x_394; 
lean_dec(x_313);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_394 = !lean_is_exclusive(x_392);
if (x_394 == 0)
{
return x_392;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_392, 0);
x_396 = lean_ctor_get(x_392, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_392);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
block_385:
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_315 = lean_ctor_get(x_4, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = !lean_is_exclusive(x_4);
if (x_317 == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_4, 0);
lean_dec(x_318);
x_319 = !lean_is_exclusive(x_315);
if (x_319 == 0)
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_ctor_get(x_315, 0);
lean_dec(x_320);
x_321 = !lean_is_exclusive(x_316);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_316, 3);
x_323 = lean_unsigned_to_nat(1u);
x_324 = lean_nat_add(x_322, x_323);
lean_dec(x_322);
lean_ctor_set(x_316, 3, x_324);
x_3 = x_313;
x_5 = x_314;
goto _start;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_326 = lean_ctor_get(x_316, 0);
x_327 = lean_ctor_get(x_316, 1);
x_328 = lean_ctor_get(x_316, 2);
x_329 = lean_ctor_get(x_316, 3);
x_330 = lean_ctor_get(x_316, 4);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_316);
x_331 = lean_unsigned_to_nat(1u);
x_332 = lean_nat_add(x_329, x_331);
lean_dec(x_329);
x_333 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_333, 0, x_326);
lean_ctor_set(x_333, 1, x_327);
lean_ctor_set(x_333, 2, x_328);
lean_ctor_set(x_333, 3, x_332);
lean_ctor_set(x_333, 4, x_330);
lean_ctor_set(x_315, 0, x_333);
x_3 = x_313;
x_5 = x_314;
goto _start;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_335 = lean_ctor_get(x_315, 1);
x_336 = lean_ctor_get(x_315, 2);
x_337 = lean_ctor_get(x_315, 3);
x_338 = lean_ctor_get(x_315, 4);
x_339 = lean_ctor_get(x_315, 5);
x_340 = lean_ctor_get(x_315, 6);
x_341 = lean_ctor_get(x_315, 7);
x_342 = lean_ctor_get(x_315, 8);
x_343 = lean_ctor_get(x_315, 9);
x_344 = lean_ctor_get_uint8(x_315, sizeof(void*)*10);
x_345 = lean_ctor_get_uint8(x_315, sizeof(void*)*10 + 1);
x_346 = lean_ctor_get_uint8(x_315, sizeof(void*)*10 + 2);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_315);
x_347 = lean_ctor_get(x_316, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_316, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_316, 2);
lean_inc(x_349);
x_350 = lean_ctor_get(x_316, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_316, 4);
lean_inc(x_351);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 lean_ctor_release(x_316, 2);
 lean_ctor_release(x_316, 3);
 lean_ctor_release(x_316, 4);
 x_352 = x_316;
} else {
 lean_dec_ref(x_316);
 x_352 = lean_box(0);
}
x_353 = lean_unsigned_to_nat(1u);
x_354 = lean_nat_add(x_350, x_353);
lean_dec(x_350);
if (lean_is_scalar(x_352)) {
 x_355 = lean_alloc_ctor(0, 5, 0);
} else {
 x_355 = x_352;
}
lean_ctor_set(x_355, 0, x_347);
lean_ctor_set(x_355, 1, x_348);
lean_ctor_set(x_355, 2, x_349);
lean_ctor_set(x_355, 3, x_354);
lean_ctor_set(x_355, 4, x_351);
x_356 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_335);
lean_ctor_set(x_356, 2, x_336);
lean_ctor_set(x_356, 3, x_337);
lean_ctor_set(x_356, 4, x_338);
lean_ctor_set(x_356, 5, x_339);
lean_ctor_set(x_356, 6, x_340);
lean_ctor_set(x_356, 7, x_341);
lean_ctor_set(x_356, 8, x_342);
lean_ctor_set(x_356, 9, x_343);
lean_ctor_set_uint8(x_356, sizeof(void*)*10, x_344);
lean_ctor_set_uint8(x_356, sizeof(void*)*10 + 1, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*10 + 2, x_346);
lean_ctor_set(x_4, 0, x_356);
x_3 = x_313;
x_5 = x_314;
goto _start;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_358 = lean_ctor_get(x_4, 1);
x_359 = lean_ctor_get(x_4, 2);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_4);
x_360 = lean_ctor_get(x_315, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_315, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_315, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_315, 4);
lean_inc(x_363);
x_364 = lean_ctor_get(x_315, 5);
lean_inc(x_364);
x_365 = lean_ctor_get(x_315, 6);
lean_inc(x_365);
x_366 = lean_ctor_get(x_315, 7);
lean_inc(x_366);
x_367 = lean_ctor_get(x_315, 8);
lean_inc(x_367);
x_368 = lean_ctor_get(x_315, 9);
lean_inc(x_368);
x_369 = lean_ctor_get_uint8(x_315, sizeof(void*)*10);
x_370 = lean_ctor_get_uint8(x_315, sizeof(void*)*10 + 1);
x_371 = lean_ctor_get_uint8(x_315, sizeof(void*)*10 + 2);
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
 x_372 = x_315;
} else {
 lean_dec_ref(x_315);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_316, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_316, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_316, 2);
lean_inc(x_375);
x_376 = lean_ctor_get(x_316, 3);
lean_inc(x_376);
x_377 = lean_ctor_get(x_316, 4);
lean_inc(x_377);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 lean_ctor_release(x_316, 2);
 lean_ctor_release(x_316, 3);
 lean_ctor_release(x_316, 4);
 x_378 = x_316;
} else {
 lean_dec_ref(x_316);
 x_378 = lean_box(0);
}
x_379 = lean_unsigned_to_nat(1u);
x_380 = lean_nat_add(x_376, x_379);
lean_dec(x_376);
if (lean_is_scalar(x_378)) {
 x_381 = lean_alloc_ctor(0, 5, 0);
} else {
 x_381 = x_378;
}
lean_ctor_set(x_381, 0, x_373);
lean_ctor_set(x_381, 1, x_374);
lean_ctor_set(x_381, 2, x_375);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set(x_381, 4, x_377);
if (lean_is_scalar(x_372)) {
 x_382 = lean_alloc_ctor(0, 10, 3);
} else {
 x_382 = x_372;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_360);
lean_ctor_set(x_382, 2, x_361);
lean_ctor_set(x_382, 3, x_362);
lean_ctor_set(x_382, 4, x_363);
lean_ctor_set(x_382, 5, x_364);
lean_ctor_set(x_382, 6, x_365);
lean_ctor_set(x_382, 7, x_366);
lean_ctor_set(x_382, 8, x_367);
lean_ctor_set(x_382, 9, x_368);
lean_ctor_set_uint8(x_382, sizeof(void*)*10, x_369);
lean_ctor_set_uint8(x_382, sizeof(void*)*10 + 1, x_370);
lean_ctor_set_uint8(x_382, sizeof(void*)*10 + 2, x_371);
x_383 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_358);
lean_ctor_set(x_383, 2, x_359);
x_3 = x_313;
x_4 = x_383;
x_5 = x_314;
goto _start;
}
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_398 = !lean_is_exclusive(x_304);
if (x_398 == 0)
{
return x_304;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_304, 0);
x_400 = lean_ctor_get(x_304, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_304);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
}
case 4:
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_402 = lean_ctor_get(x_9, 0);
lean_inc(x_402);
lean_dec(x_9);
lean_inc(x_2);
x_403 = l_Lean_Name_append___main(x_402, x_2);
lean_dec(x_402);
x_404 = l_Lean_Elab_Tactic_getEnv___rarg(x_8);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
lean_inc(x_403);
x_407 = lean_environment_find(x_405, x_403);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
lean_dec(x_403);
lean_inc(x_4);
lean_inc(x_1);
x_408 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_406);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
uint8_t x_410; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_410 = !lean_is_exclusive(x_408);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_408, 0);
lean_dec(x_411);
x_412 = lean_box(0);
lean_ctor_set(x_408, 0, x_412);
return x_408;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_408, 1);
lean_inc(x_413);
lean_dec(x_408);
x_414 = lean_box(0);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_416 = lean_ctor_get(x_408, 1);
lean_inc(x_416);
lean_dec(x_408);
x_417 = lean_ctor_get(x_409, 0);
lean_inc(x_417);
lean_dec(x_409);
x_490 = lean_ctor_get(x_4, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec(x_490);
x_492 = lean_ctor_get(x_491, 3);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 4);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_nat_dec_eq(x_492, x_493);
lean_dec(x_493);
lean_dec(x_492);
if (x_494 == 0)
{
x_418 = x_416;
goto block_489;
}
else
{
lean_object* x_495; lean_object* x_496; 
x_495 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_496 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_495, x_4, x_416);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_418 = x_497;
goto block_489;
}
else
{
uint8_t x_498; 
lean_dec(x_417);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_498 = !lean_is_exclusive(x_496);
if (x_498 == 0)
{
return x_496;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_496, 0);
x_500 = lean_ctor_get(x_496, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_496);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
block_489:
{
lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_419 = lean_ctor_get(x_4, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = !lean_is_exclusive(x_4);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; 
x_422 = lean_ctor_get(x_4, 0);
lean_dec(x_422);
x_423 = !lean_is_exclusive(x_419);
if (x_423 == 0)
{
lean_object* x_424; uint8_t x_425; 
x_424 = lean_ctor_get(x_419, 0);
lean_dec(x_424);
x_425 = !lean_is_exclusive(x_420);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_420, 3);
x_427 = lean_unsigned_to_nat(1u);
x_428 = lean_nat_add(x_426, x_427);
lean_dec(x_426);
lean_ctor_set(x_420, 3, x_428);
x_3 = x_417;
x_5 = x_418;
goto _start;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_430 = lean_ctor_get(x_420, 0);
x_431 = lean_ctor_get(x_420, 1);
x_432 = lean_ctor_get(x_420, 2);
x_433 = lean_ctor_get(x_420, 3);
x_434 = lean_ctor_get(x_420, 4);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_420);
x_435 = lean_unsigned_to_nat(1u);
x_436 = lean_nat_add(x_433, x_435);
lean_dec(x_433);
x_437 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_437, 0, x_430);
lean_ctor_set(x_437, 1, x_431);
lean_ctor_set(x_437, 2, x_432);
lean_ctor_set(x_437, 3, x_436);
lean_ctor_set(x_437, 4, x_434);
lean_ctor_set(x_419, 0, x_437);
x_3 = x_417;
x_5 = x_418;
goto _start;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; uint8_t x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_439 = lean_ctor_get(x_419, 1);
x_440 = lean_ctor_get(x_419, 2);
x_441 = lean_ctor_get(x_419, 3);
x_442 = lean_ctor_get(x_419, 4);
x_443 = lean_ctor_get(x_419, 5);
x_444 = lean_ctor_get(x_419, 6);
x_445 = lean_ctor_get(x_419, 7);
x_446 = lean_ctor_get(x_419, 8);
x_447 = lean_ctor_get(x_419, 9);
x_448 = lean_ctor_get_uint8(x_419, sizeof(void*)*10);
x_449 = lean_ctor_get_uint8(x_419, sizeof(void*)*10 + 1);
x_450 = lean_ctor_get_uint8(x_419, sizeof(void*)*10 + 2);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_419);
x_451 = lean_ctor_get(x_420, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_420, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_420, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_420, 3);
lean_inc(x_454);
x_455 = lean_ctor_get(x_420, 4);
lean_inc(x_455);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 lean_ctor_release(x_420, 4);
 x_456 = x_420;
} else {
 lean_dec_ref(x_420);
 x_456 = lean_box(0);
}
x_457 = lean_unsigned_to_nat(1u);
x_458 = lean_nat_add(x_454, x_457);
lean_dec(x_454);
if (lean_is_scalar(x_456)) {
 x_459 = lean_alloc_ctor(0, 5, 0);
} else {
 x_459 = x_456;
}
lean_ctor_set(x_459, 0, x_451);
lean_ctor_set(x_459, 1, x_452);
lean_ctor_set(x_459, 2, x_453);
lean_ctor_set(x_459, 3, x_458);
lean_ctor_set(x_459, 4, x_455);
x_460 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_439);
lean_ctor_set(x_460, 2, x_440);
lean_ctor_set(x_460, 3, x_441);
lean_ctor_set(x_460, 4, x_442);
lean_ctor_set(x_460, 5, x_443);
lean_ctor_set(x_460, 6, x_444);
lean_ctor_set(x_460, 7, x_445);
lean_ctor_set(x_460, 8, x_446);
lean_ctor_set(x_460, 9, x_447);
lean_ctor_set_uint8(x_460, sizeof(void*)*10, x_448);
lean_ctor_set_uint8(x_460, sizeof(void*)*10 + 1, x_449);
lean_ctor_set_uint8(x_460, sizeof(void*)*10 + 2, x_450);
lean_ctor_set(x_4, 0, x_460);
x_3 = x_417;
x_5 = x_418;
goto _start;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; uint8_t x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_462 = lean_ctor_get(x_4, 1);
x_463 = lean_ctor_get(x_4, 2);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_4);
x_464 = lean_ctor_get(x_419, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_419, 2);
lean_inc(x_465);
x_466 = lean_ctor_get(x_419, 3);
lean_inc(x_466);
x_467 = lean_ctor_get(x_419, 4);
lean_inc(x_467);
x_468 = lean_ctor_get(x_419, 5);
lean_inc(x_468);
x_469 = lean_ctor_get(x_419, 6);
lean_inc(x_469);
x_470 = lean_ctor_get(x_419, 7);
lean_inc(x_470);
x_471 = lean_ctor_get(x_419, 8);
lean_inc(x_471);
x_472 = lean_ctor_get(x_419, 9);
lean_inc(x_472);
x_473 = lean_ctor_get_uint8(x_419, sizeof(void*)*10);
x_474 = lean_ctor_get_uint8(x_419, sizeof(void*)*10 + 1);
x_475 = lean_ctor_get_uint8(x_419, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 lean_ctor_release(x_419, 4);
 lean_ctor_release(x_419, 5);
 lean_ctor_release(x_419, 6);
 lean_ctor_release(x_419, 7);
 lean_ctor_release(x_419, 8);
 lean_ctor_release(x_419, 9);
 x_476 = x_419;
} else {
 lean_dec_ref(x_419);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_420, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_420, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_420, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_420, 3);
lean_inc(x_480);
x_481 = lean_ctor_get(x_420, 4);
lean_inc(x_481);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 lean_ctor_release(x_420, 4);
 x_482 = x_420;
} else {
 lean_dec_ref(x_420);
 x_482 = lean_box(0);
}
x_483 = lean_unsigned_to_nat(1u);
x_484 = lean_nat_add(x_480, x_483);
lean_dec(x_480);
if (lean_is_scalar(x_482)) {
 x_485 = lean_alloc_ctor(0, 5, 0);
} else {
 x_485 = x_482;
}
lean_ctor_set(x_485, 0, x_477);
lean_ctor_set(x_485, 1, x_478);
lean_ctor_set(x_485, 2, x_479);
lean_ctor_set(x_485, 3, x_484);
lean_ctor_set(x_485, 4, x_481);
if (lean_is_scalar(x_476)) {
 x_486 = lean_alloc_ctor(0, 10, 3);
} else {
 x_486 = x_476;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_464);
lean_ctor_set(x_486, 2, x_465);
lean_ctor_set(x_486, 3, x_466);
lean_ctor_set(x_486, 4, x_467);
lean_ctor_set(x_486, 5, x_468);
lean_ctor_set(x_486, 6, x_469);
lean_ctor_set(x_486, 7, x_470);
lean_ctor_set(x_486, 8, x_471);
lean_ctor_set(x_486, 9, x_472);
lean_ctor_set_uint8(x_486, sizeof(void*)*10, x_473);
lean_ctor_set_uint8(x_486, sizeof(void*)*10 + 1, x_474);
lean_ctor_set_uint8(x_486, sizeof(void*)*10 + 2, x_475);
x_487 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_462);
lean_ctor_set(x_487, 2, x_463);
x_3 = x_417;
x_4 = x_487;
x_5 = x_418;
goto _start;
}
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_408);
if (x_502 == 0)
{
return x_408;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_408, 0);
x_504 = lean_ctor_get(x_408, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_408);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_608; 
lean_dec(x_407);
x_506 = l_Lean_Elab_Tactic_save(x_406);
lean_inc(x_4);
lean_inc(x_1);
x_608 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_4, x_406);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_box(0);
x_613 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 4, 2);
lean_closure_set(x_613, 0, x_403);
lean_closure_set(x_613, 1, x_612);
x_614 = l___private_Init_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_615 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_615, 0, x_613);
lean_closure_set(x_615, 1, x_614);
lean_inc(x_1);
x_616 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_616, 0, x_1);
lean_closure_set(x_616, 1, x_615);
lean_inc(x_4);
x_617 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_611, x_616, x_4, x_610);
lean_dec(x_611);
if (lean_obj_tag(x_617) == 0)
{
lean_dec(x_506);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_617;
}
else
{
lean_object* x_618; 
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_507 = x_618;
goto block_607;
}
}
else
{
lean_object* x_619; 
lean_dec(x_403);
x_619 = lean_ctor_get(x_608, 1);
lean_inc(x_619);
lean_dec(x_608);
x_507 = x_619;
goto block_607;
}
block_607:
{
lean_object* x_508; lean_object* x_509; 
x_508 = l_Lean_Elab_Tactic_restore(x_507, x_506);
lean_dec(x_506);
lean_inc(x_4);
lean_inc(x_1);
x_509 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_508);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
uint8_t x_511; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_511 = !lean_is_exclusive(x_509);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_509, 0);
lean_dec(x_512);
x_513 = lean_box(0);
lean_ctor_set(x_509, 0, x_513);
return x_509;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_509, 1);
lean_inc(x_514);
lean_dec(x_509);
x_515 = lean_box(0);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_517 = lean_ctor_get(x_509, 1);
lean_inc(x_517);
lean_dec(x_509);
x_518 = lean_ctor_get(x_510, 0);
lean_inc(x_518);
lean_dec(x_510);
x_591 = lean_ctor_get(x_4, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
lean_dec(x_591);
x_593 = lean_ctor_get(x_592, 3);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 4);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_nat_dec_eq(x_593, x_594);
lean_dec(x_594);
lean_dec(x_593);
if (x_595 == 0)
{
x_519 = x_517;
goto block_590;
}
else
{
lean_object* x_596; lean_object* x_597; 
x_596 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_597 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_596, x_4, x_517);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; 
x_598 = lean_ctor_get(x_597, 1);
lean_inc(x_598);
lean_dec(x_597);
x_519 = x_598;
goto block_590;
}
else
{
uint8_t x_599; 
lean_dec(x_518);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_597);
if (x_599 == 0)
{
return x_597;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_597, 0);
x_601 = lean_ctor_get(x_597, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_597);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
block_590:
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_520 = lean_ctor_get(x_4, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = !lean_is_exclusive(x_4);
if (x_522 == 0)
{
lean_object* x_523; uint8_t x_524; 
x_523 = lean_ctor_get(x_4, 0);
lean_dec(x_523);
x_524 = !lean_is_exclusive(x_520);
if (x_524 == 0)
{
lean_object* x_525; uint8_t x_526; 
x_525 = lean_ctor_get(x_520, 0);
lean_dec(x_525);
x_526 = !lean_is_exclusive(x_521);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_521, 3);
x_528 = lean_unsigned_to_nat(1u);
x_529 = lean_nat_add(x_527, x_528);
lean_dec(x_527);
lean_ctor_set(x_521, 3, x_529);
x_3 = x_518;
x_5 = x_519;
goto _start;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_531 = lean_ctor_get(x_521, 0);
x_532 = lean_ctor_get(x_521, 1);
x_533 = lean_ctor_get(x_521, 2);
x_534 = lean_ctor_get(x_521, 3);
x_535 = lean_ctor_get(x_521, 4);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_521);
x_536 = lean_unsigned_to_nat(1u);
x_537 = lean_nat_add(x_534, x_536);
lean_dec(x_534);
x_538 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_538, 0, x_531);
lean_ctor_set(x_538, 1, x_532);
lean_ctor_set(x_538, 2, x_533);
lean_ctor_set(x_538, 3, x_537);
lean_ctor_set(x_538, 4, x_535);
lean_ctor_set(x_520, 0, x_538);
x_3 = x_518;
x_5 = x_519;
goto _start;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; uint8_t x_550; uint8_t x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_540 = lean_ctor_get(x_520, 1);
x_541 = lean_ctor_get(x_520, 2);
x_542 = lean_ctor_get(x_520, 3);
x_543 = lean_ctor_get(x_520, 4);
x_544 = lean_ctor_get(x_520, 5);
x_545 = lean_ctor_get(x_520, 6);
x_546 = lean_ctor_get(x_520, 7);
x_547 = lean_ctor_get(x_520, 8);
x_548 = lean_ctor_get(x_520, 9);
x_549 = lean_ctor_get_uint8(x_520, sizeof(void*)*10);
x_550 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 1);
x_551 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 2);
lean_inc(x_548);
lean_inc(x_547);
lean_inc(x_546);
lean_inc(x_545);
lean_inc(x_544);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
lean_inc(x_540);
lean_dec(x_520);
x_552 = lean_ctor_get(x_521, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_521, 1);
lean_inc(x_553);
x_554 = lean_ctor_get(x_521, 2);
lean_inc(x_554);
x_555 = lean_ctor_get(x_521, 3);
lean_inc(x_555);
x_556 = lean_ctor_get(x_521, 4);
lean_inc(x_556);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 lean_ctor_release(x_521, 2);
 lean_ctor_release(x_521, 3);
 lean_ctor_release(x_521, 4);
 x_557 = x_521;
} else {
 lean_dec_ref(x_521);
 x_557 = lean_box(0);
}
x_558 = lean_unsigned_to_nat(1u);
x_559 = lean_nat_add(x_555, x_558);
lean_dec(x_555);
if (lean_is_scalar(x_557)) {
 x_560 = lean_alloc_ctor(0, 5, 0);
} else {
 x_560 = x_557;
}
lean_ctor_set(x_560, 0, x_552);
lean_ctor_set(x_560, 1, x_553);
lean_ctor_set(x_560, 2, x_554);
lean_ctor_set(x_560, 3, x_559);
lean_ctor_set(x_560, 4, x_556);
x_561 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_540);
lean_ctor_set(x_561, 2, x_541);
lean_ctor_set(x_561, 3, x_542);
lean_ctor_set(x_561, 4, x_543);
lean_ctor_set(x_561, 5, x_544);
lean_ctor_set(x_561, 6, x_545);
lean_ctor_set(x_561, 7, x_546);
lean_ctor_set(x_561, 8, x_547);
lean_ctor_set(x_561, 9, x_548);
lean_ctor_set_uint8(x_561, sizeof(void*)*10, x_549);
lean_ctor_set_uint8(x_561, sizeof(void*)*10 + 1, x_550);
lean_ctor_set_uint8(x_561, sizeof(void*)*10 + 2, x_551);
lean_ctor_set(x_4, 0, x_561);
x_3 = x_518;
x_5 = x_519;
goto _start;
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; uint8_t x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_563 = lean_ctor_get(x_4, 1);
x_564 = lean_ctor_get(x_4, 2);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_4);
x_565 = lean_ctor_get(x_520, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_520, 2);
lean_inc(x_566);
x_567 = lean_ctor_get(x_520, 3);
lean_inc(x_567);
x_568 = lean_ctor_get(x_520, 4);
lean_inc(x_568);
x_569 = lean_ctor_get(x_520, 5);
lean_inc(x_569);
x_570 = lean_ctor_get(x_520, 6);
lean_inc(x_570);
x_571 = lean_ctor_get(x_520, 7);
lean_inc(x_571);
x_572 = lean_ctor_get(x_520, 8);
lean_inc(x_572);
x_573 = lean_ctor_get(x_520, 9);
lean_inc(x_573);
x_574 = lean_ctor_get_uint8(x_520, sizeof(void*)*10);
x_575 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 1);
x_576 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 2);
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
 x_577 = x_520;
} else {
 lean_dec_ref(x_520);
 x_577 = lean_box(0);
}
x_578 = lean_ctor_get(x_521, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_521, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_521, 2);
lean_inc(x_580);
x_581 = lean_ctor_get(x_521, 3);
lean_inc(x_581);
x_582 = lean_ctor_get(x_521, 4);
lean_inc(x_582);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 lean_ctor_release(x_521, 2);
 lean_ctor_release(x_521, 3);
 lean_ctor_release(x_521, 4);
 x_583 = x_521;
} else {
 lean_dec_ref(x_521);
 x_583 = lean_box(0);
}
x_584 = lean_unsigned_to_nat(1u);
x_585 = lean_nat_add(x_581, x_584);
lean_dec(x_581);
if (lean_is_scalar(x_583)) {
 x_586 = lean_alloc_ctor(0, 5, 0);
} else {
 x_586 = x_583;
}
lean_ctor_set(x_586, 0, x_578);
lean_ctor_set(x_586, 1, x_579);
lean_ctor_set(x_586, 2, x_580);
lean_ctor_set(x_586, 3, x_585);
lean_ctor_set(x_586, 4, x_582);
if (lean_is_scalar(x_577)) {
 x_587 = lean_alloc_ctor(0, 10, 3);
} else {
 x_587 = x_577;
}
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_565);
lean_ctor_set(x_587, 2, x_566);
lean_ctor_set(x_587, 3, x_567);
lean_ctor_set(x_587, 4, x_568);
lean_ctor_set(x_587, 5, x_569);
lean_ctor_set(x_587, 6, x_570);
lean_ctor_set(x_587, 7, x_571);
lean_ctor_set(x_587, 8, x_572);
lean_ctor_set(x_587, 9, x_573);
lean_ctor_set_uint8(x_587, sizeof(void*)*10, x_574);
lean_ctor_set_uint8(x_587, sizeof(void*)*10 + 1, x_575);
lean_ctor_set_uint8(x_587, sizeof(void*)*10 + 2, x_576);
x_588 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_563);
lean_ctor_set(x_588, 2, x_564);
x_3 = x_518;
x_4 = x_588;
x_5 = x_519;
goto _start;
}
}
}
}
else
{
uint8_t x_603; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_603 = !lean_is_exclusive(x_509);
if (x_603 == 0)
{
return x_509;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_509, 0);
x_605 = lean_ctor_get(x_509, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_509);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
}
}
}
case 5:
{
lean_object* x_620; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_620 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
if (lean_obj_tag(x_621) == 0)
{
uint8_t x_622; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_622 = !lean_is_exclusive(x_620);
if (x_622 == 0)
{
lean_object* x_623; lean_object* x_624; 
x_623 = lean_ctor_get(x_620, 0);
lean_dec(x_623);
x_624 = lean_box(0);
lean_ctor_set(x_620, 0, x_624);
return x_620;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_620, 1);
lean_inc(x_625);
lean_dec(x_620);
x_626 = lean_box(0);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; uint8_t x_706; 
x_628 = lean_ctor_get(x_620, 1);
lean_inc(x_628);
lean_dec(x_620);
x_629 = lean_ctor_get(x_621, 0);
lean_inc(x_629);
lean_dec(x_621);
x_702 = lean_ctor_get(x_4, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
lean_dec(x_702);
x_704 = lean_ctor_get(x_703, 3);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 4);
lean_inc(x_705);
lean_dec(x_703);
x_706 = lean_nat_dec_eq(x_704, x_705);
lean_dec(x_705);
lean_dec(x_704);
if (x_706 == 0)
{
x_630 = x_628;
goto block_701;
}
else
{
lean_object* x_707; lean_object* x_708; 
x_707 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_708 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_707, x_4, x_628);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; 
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
lean_dec(x_708);
x_630 = x_709;
goto block_701;
}
else
{
uint8_t x_710; 
lean_dec(x_629);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_710 = !lean_is_exclusive(x_708);
if (x_710 == 0)
{
return x_708;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_708, 0);
x_712 = lean_ctor_get(x_708, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_708);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set(x_713, 1, x_712);
return x_713;
}
}
}
block_701:
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; 
x_631 = lean_ctor_get(x_4, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = !lean_is_exclusive(x_4);
if (x_633 == 0)
{
lean_object* x_634; uint8_t x_635; 
x_634 = lean_ctor_get(x_4, 0);
lean_dec(x_634);
x_635 = !lean_is_exclusive(x_631);
if (x_635 == 0)
{
lean_object* x_636; uint8_t x_637; 
x_636 = lean_ctor_get(x_631, 0);
lean_dec(x_636);
x_637 = !lean_is_exclusive(x_632);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_632, 3);
x_639 = lean_unsigned_to_nat(1u);
x_640 = lean_nat_add(x_638, x_639);
lean_dec(x_638);
lean_ctor_set(x_632, 3, x_640);
x_3 = x_629;
x_5 = x_630;
goto _start;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_642 = lean_ctor_get(x_632, 0);
x_643 = lean_ctor_get(x_632, 1);
x_644 = lean_ctor_get(x_632, 2);
x_645 = lean_ctor_get(x_632, 3);
x_646 = lean_ctor_get(x_632, 4);
lean_inc(x_646);
lean_inc(x_645);
lean_inc(x_644);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_632);
x_647 = lean_unsigned_to_nat(1u);
x_648 = lean_nat_add(x_645, x_647);
lean_dec(x_645);
x_649 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_649, 0, x_642);
lean_ctor_set(x_649, 1, x_643);
lean_ctor_set(x_649, 2, x_644);
lean_ctor_set(x_649, 3, x_648);
lean_ctor_set(x_649, 4, x_646);
lean_ctor_set(x_631, 0, x_649);
x_3 = x_629;
x_5 = x_630;
goto _start;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; uint8_t x_661; uint8_t x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_651 = lean_ctor_get(x_631, 1);
x_652 = lean_ctor_get(x_631, 2);
x_653 = lean_ctor_get(x_631, 3);
x_654 = lean_ctor_get(x_631, 4);
x_655 = lean_ctor_get(x_631, 5);
x_656 = lean_ctor_get(x_631, 6);
x_657 = lean_ctor_get(x_631, 7);
x_658 = lean_ctor_get(x_631, 8);
x_659 = lean_ctor_get(x_631, 9);
x_660 = lean_ctor_get_uint8(x_631, sizeof(void*)*10);
x_661 = lean_ctor_get_uint8(x_631, sizeof(void*)*10 + 1);
x_662 = lean_ctor_get_uint8(x_631, sizeof(void*)*10 + 2);
lean_inc(x_659);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_631);
x_663 = lean_ctor_get(x_632, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_632, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_632, 2);
lean_inc(x_665);
x_666 = lean_ctor_get(x_632, 3);
lean_inc(x_666);
x_667 = lean_ctor_get(x_632, 4);
lean_inc(x_667);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 lean_ctor_release(x_632, 2);
 lean_ctor_release(x_632, 3);
 lean_ctor_release(x_632, 4);
 x_668 = x_632;
} else {
 lean_dec_ref(x_632);
 x_668 = lean_box(0);
}
x_669 = lean_unsigned_to_nat(1u);
x_670 = lean_nat_add(x_666, x_669);
lean_dec(x_666);
if (lean_is_scalar(x_668)) {
 x_671 = lean_alloc_ctor(0, 5, 0);
} else {
 x_671 = x_668;
}
lean_ctor_set(x_671, 0, x_663);
lean_ctor_set(x_671, 1, x_664);
lean_ctor_set(x_671, 2, x_665);
lean_ctor_set(x_671, 3, x_670);
lean_ctor_set(x_671, 4, x_667);
x_672 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_651);
lean_ctor_set(x_672, 2, x_652);
lean_ctor_set(x_672, 3, x_653);
lean_ctor_set(x_672, 4, x_654);
lean_ctor_set(x_672, 5, x_655);
lean_ctor_set(x_672, 6, x_656);
lean_ctor_set(x_672, 7, x_657);
lean_ctor_set(x_672, 8, x_658);
lean_ctor_set(x_672, 9, x_659);
lean_ctor_set_uint8(x_672, sizeof(void*)*10, x_660);
lean_ctor_set_uint8(x_672, sizeof(void*)*10 + 1, x_661);
lean_ctor_set_uint8(x_672, sizeof(void*)*10 + 2, x_662);
lean_ctor_set(x_4, 0, x_672);
x_3 = x_629;
x_5 = x_630;
goto _start;
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; uint8_t x_686; uint8_t x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_674 = lean_ctor_get(x_4, 1);
x_675 = lean_ctor_get(x_4, 2);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_4);
x_676 = lean_ctor_get(x_631, 1);
lean_inc(x_676);
x_677 = lean_ctor_get(x_631, 2);
lean_inc(x_677);
x_678 = lean_ctor_get(x_631, 3);
lean_inc(x_678);
x_679 = lean_ctor_get(x_631, 4);
lean_inc(x_679);
x_680 = lean_ctor_get(x_631, 5);
lean_inc(x_680);
x_681 = lean_ctor_get(x_631, 6);
lean_inc(x_681);
x_682 = lean_ctor_get(x_631, 7);
lean_inc(x_682);
x_683 = lean_ctor_get(x_631, 8);
lean_inc(x_683);
x_684 = lean_ctor_get(x_631, 9);
lean_inc(x_684);
x_685 = lean_ctor_get_uint8(x_631, sizeof(void*)*10);
x_686 = lean_ctor_get_uint8(x_631, sizeof(void*)*10 + 1);
x_687 = lean_ctor_get_uint8(x_631, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 lean_ctor_release(x_631, 2);
 lean_ctor_release(x_631, 3);
 lean_ctor_release(x_631, 4);
 lean_ctor_release(x_631, 5);
 lean_ctor_release(x_631, 6);
 lean_ctor_release(x_631, 7);
 lean_ctor_release(x_631, 8);
 lean_ctor_release(x_631, 9);
 x_688 = x_631;
} else {
 lean_dec_ref(x_631);
 x_688 = lean_box(0);
}
x_689 = lean_ctor_get(x_632, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_632, 1);
lean_inc(x_690);
x_691 = lean_ctor_get(x_632, 2);
lean_inc(x_691);
x_692 = lean_ctor_get(x_632, 3);
lean_inc(x_692);
x_693 = lean_ctor_get(x_632, 4);
lean_inc(x_693);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 lean_ctor_release(x_632, 2);
 lean_ctor_release(x_632, 3);
 lean_ctor_release(x_632, 4);
 x_694 = x_632;
} else {
 lean_dec_ref(x_632);
 x_694 = lean_box(0);
}
x_695 = lean_unsigned_to_nat(1u);
x_696 = lean_nat_add(x_692, x_695);
lean_dec(x_692);
if (lean_is_scalar(x_694)) {
 x_697 = lean_alloc_ctor(0, 5, 0);
} else {
 x_697 = x_694;
}
lean_ctor_set(x_697, 0, x_689);
lean_ctor_set(x_697, 1, x_690);
lean_ctor_set(x_697, 2, x_691);
lean_ctor_set(x_697, 3, x_696);
lean_ctor_set(x_697, 4, x_693);
if (lean_is_scalar(x_688)) {
 x_698 = lean_alloc_ctor(0, 10, 3);
} else {
 x_698 = x_688;
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_676);
lean_ctor_set(x_698, 2, x_677);
lean_ctor_set(x_698, 3, x_678);
lean_ctor_set(x_698, 4, x_679);
lean_ctor_set(x_698, 5, x_680);
lean_ctor_set(x_698, 6, x_681);
lean_ctor_set(x_698, 7, x_682);
lean_ctor_set(x_698, 8, x_683);
lean_ctor_set(x_698, 9, x_684);
lean_ctor_set_uint8(x_698, sizeof(void*)*10, x_685);
lean_ctor_set_uint8(x_698, sizeof(void*)*10 + 1, x_686);
lean_ctor_set_uint8(x_698, sizeof(void*)*10 + 2, x_687);
x_699 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_674);
lean_ctor_set(x_699, 2, x_675);
x_3 = x_629;
x_4 = x_699;
x_5 = x_630;
goto _start;
}
}
}
}
else
{
uint8_t x_714; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_714 = !lean_is_exclusive(x_620);
if (x_714 == 0)
{
return x_620;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_620, 0);
x_716 = lean_ctor_get(x_620, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_620);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
case 6:
{
lean_object* x_718; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_718 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
if (lean_obj_tag(x_719) == 0)
{
uint8_t x_720; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_720 = !lean_is_exclusive(x_718);
if (x_720 == 0)
{
lean_object* x_721; lean_object* x_722; 
x_721 = lean_ctor_get(x_718, 0);
lean_dec(x_721);
x_722 = lean_box(0);
lean_ctor_set(x_718, 0, x_722);
return x_718;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_718, 1);
lean_inc(x_723);
lean_dec(x_718);
x_724 = lean_box(0);
x_725 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_723);
return x_725;
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
x_726 = lean_ctor_get(x_718, 1);
lean_inc(x_726);
lean_dec(x_718);
x_727 = lean_ctor_get(x_719, 0);
lean_inc(x_727);
lean_dec(x_719);
x_800 = lean_ctor_get(x_4, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
lean_dec(x_800);
x_802 = lean_ctor_get(x_801, 3);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 4);
lean_inc(x_803);
lean_dec(x_801);
x_804 = lean_nat_dec_eq(x_802, x_803);
lean_dec(x_803);
lean_dec(x_802);
if (x_804 == 0)
{
x_728 = x_726;
goto block_799;
}
else
{
lean_object* x_805; lean_object* x_806; 
x_805 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_806 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_805, x_4, x_726);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; 
x_807 = lean_ctor_get(x_806, 1);
lean_inc(x_807);
lean_dec(x_806);
x_728 = x_807;
goto block_799;
}
else
{
uint8_t x_808; 
lean_dec(x_727);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_808 = !lean_is_exclusive(x_806);
if (x_808 == 0)
{
return x_806;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_806, 0);
x_810 = lean_ctor_get(x_806, 1);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_806);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
}
block_799:
{
lean_object* x_729; lean_object* x_730; uint8_t x_731; 
x_729 = lean_ctor_get(x_4, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = !lean_is_exclusive(x_4);
if (x_731 == 0)
{
lean_object* x_732; uint8_t x_733; 
x_732 = lean_ctor_get(x_4, 0);
lean_dec(x_732);
x_733 = !lean_is_exclusive(x_729);
if (x_733 == 0)
{
lean_object* x_734; uint8_t x_735; 
x_734 = lean_ctor_get(x_729, 0);
lean_dec(x_734);
x_735 = !lean_is_exclusive(x_730);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_730, 3);
x_737 = lean_unsigned_to_nat(1u);
x_738 = lean_nat_add(x_736, x_737);
lean_dec(x_736);
lean_ctor_set(x_730, 3, x_738);
x_3 = x_727;
x_5 = x_728;
goto _start;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_740 = lean_ctor_get(x_730, 0);
x_741 = lean_ctor_get(x_730, 1);
x_742 = lean_ctor_get(x_730, 2);
x_743 = lean_ctor_get(x_730, 3);
x_744 = lean_ctor_get(x_730, 4);
lean_inc(x_744);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_730);
x_745 = lean_unsigned_to_nat(1u);
x_746 = lean_nat_add(x_743, x_745);
lean_dec(x_743);
x_747 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_747, 0, x_740);
lean_ctor_set(x_747, 1, x_741);
lean_ctor_set(x_747, 2, x_742);
lean_ctor_set(x_747, 3, x_746);
lean_ctor_set(x_747, 4, x_744);
lean_ctor_set(x_729, 0, x_747);
x_3 = x_727;
x_5 = x_728;
goto _start;
}
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; uint8_t x_759; uint8_t x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_749 = lean_ctor_get(x_729, 1);
x_750 = lean_ctor_get(x_729, 2);
x_751 = lean_ctor_get(x_729, 3);
x_752 = lean_ctor_get(x_729, 4);
x_753 = lean_ctor_get(x_729, 5);
x_754 = lean_ctor_get(x_729, 6);
x_755 = lean_ctor_get(x_729, 7);
x_756 = lean_ctor_get(x_729, 8);
x_757 = lean_ctor_get(x_729, 9);
x_758 = lean_ctor_get_uint8(x_729, sizeof(void*)*10);
x_759 = lean_ctor_get_uint8(x_729, sizeof(void*)*10 + 1);
x_760 = lean_ctor_get_uint8(x_729, sizeof(void*)*10 + 2);
lean_inc(x_757);
lean_inc(x_756);
lean_inc(x_755);
lean_inc(x_754);
lean_inc(x_753);
lean_inc(x_752);
lean_inc(x_751);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_729);
x_761 = lean_ctor_get(x_730, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_730, 1);
lean_inc(x_762);
x_763 = lean_ctor_get(x_730, 2);
lean_inc(x_763);
x_764 = lean_ctor_get(x_730, 3);
lean_inc(x_764);
x_765 = lean_ctor_get(x_730, 4);
lean_inc(x_765);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 lean_ctor_release(x_730, 2);
 lean_ctor_release(x_730, 3);
 lean_ctor_release(x_730, 4);
 x_766 = x_730;
} else {
 lean_dec_ref(x_730);
 x_766 = lean_box(0);
}
x_767 = lean_unsigned_to_nat(1u);
x_768 = lean_nat_add(x_764, x_767);
lean_dec(x_764);
if (lean_is_scalar(x_766)) {
 x_769 = lean_alloc_ctor(0, 5, 0);
} else {
 x_769 = x_766;
}
lean_ctor_set(x_769, 0, x_761);
lean_ctor_set(x_769, 1, x_762);
lean_ctor_set(x_769, 2, x_763);
lean_ctor_set(x_769, 3, x_768);
lean_ctor_set(x_769, 4, x_765);
x_770 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_749);
lean_ctor_set(x_770, 2, x_750);
lean_ctor_set(x_770, 3, x_751);
lean_ctor_set(x_770, 4, x_752);
lean_ctor_set(x_770, 5, x_753);
lean_ctor_set(x_770, 6, x_754);
lean_ctor_set(x_770, 7, x_755);
lean_ctor_set(x_770, 8, x_756);
lean_ctor_set(x_770, 9, x_757);
lean_ctor_set_uint8(x_770, sizeof(void*)*10, x_758);
lean_ctor_set_uint8(x_770, sizeof(void*)*10 + 1, x_759);
lean_ctor_set_uint8(x_770, sizeof(void*)*10 + 2, x_760);
lean_ctor_set(x_4, 0, x_770);
x_3 = x_727;
x_5 = x_728;
goto _start;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; uint8_t x_784; uint8_t x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_772 = lean_ctor_get(x_4, 1);
x_773 = lean_ctor_get(x_4, 2);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_4);
x_774 = lean_ctor_get(x_729, 1);
lean_inc(x_774);
x_775 = lean_ctor_get(x_729, 2);
lean_inc(x_775);
x_776 = lean_ctor_get(x_729, 3);
lean_inc(x_776);
x_777 = lean_ctor_get(x_729, 4);
lean_inc(x_777);
x_778 = lean_ctor_get(x_729, 5);
lean_inc(x_778);
x_779 = lean_ctor_get(x_729, 6);
lean_inc(x_779);
x_780 = lean_ctor_get(x_729, 7);
lean_inc(x_780);
x_781 = lean_ctor_get(x_729, 8);
lean_inc(x_781);
x_782 = lean_ctor_get(x_729, 9);
lean_inc(x_782);
x_783 = lean_ctor_get_uint8(x_729, sizeof(void*)*10);
x_784 = lean_ctor_get_uint8(x_729, sizeof(void*)*10 + 1);
x_785 = lean_ctor_get_uint8(x_729, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 lean_ctor_release(x_729, 2);
 lean_ctor_release(x_729, 3);
 lean_ctor_release(x_729, 4);
 lean_ctor_release(x_729, 5);
 lean_ctor_release(x_729, 6);
 lean_ctor_release(x_729, 7);
 lean_ctor_release(x_729, 8);
 lean_ctor_release(x_729, 9);
 x_786 = x_729;
} else {
 lean_dec_ref(x_729);
 x_786 = lean_box(0);
}
x_787 = lean_ctor_get(x_730, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_730, 1);
lean_inc(x_788);
x_789 = lean_ctor_get(x_730, 2);
lean_inc(x_789);
x_790 = lean_ctor_get(x_730, 3);
lean_inc(x_790);
x_791 = lean_ctor_get(x_730, 4);
lean_inc(x_791);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 lean_ctor_release(x_730, 2);
 lean_ctor_release(x_730, 3);
 lean_ctor_release(x_730, 4);
 x_792 = x_730;
} else {
 lean_dec_ref(x_730);
 x_792 = lean_box(0);
}
x_793 = lean_unsigned_to_nat(1u);
x_794 = lean_nat_add(x_790, x_793);
lean_dec(x_790);
if (lean_is_scalar(x_792)) {
 x_795 = lean_alloc_ctor(0, 5, 0);
} else {
 x_795 = x_792;
}
lean_ctor_set(x_795, 0, x_787);
lean_ctor_set(x_795, 1, x_788);
lean_ctor_set(x_795, 2, x_789);
lean_ctor_set(x_795, 3, x_794);
lean_ctor_set(x_795, 4, x_791);
if (lean_is_scalar(x_786)) {
 x_796 = lean_alloc_ctor(0, 10, 3);
} else {
 x_796 = x_786;
}
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_774);
lean_ctor_set(x_796, 2, x_775);
lean_ctor_set(x_796, 3, x_776);
lean_ctor_set(x_796, 4, x_777);
lean_ctor_set(x_796, 5, x_778);
lean_ctor_set(x_796, 6, x_779);
lean_ctor_set(x_796, 7, x_780);
lean_ctor_set(x_796, 8, x_781);
lean_ctor_set(x_796, 9, x_782);
lean_ctor_set_uint8(x_796, sizeof(void*)*10, x_783);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 1, x_784);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 2, x_785);
x_797 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_772);
lean_ctor_set(x_797, 2, x_773);
x_3 = x_727;
x_4 = x_797;
x_5 = x_728;
goto _start;
}
}
}
}
else
{
uint8_t x_812; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_812 = !lean_is_exclusive(x_718);
if (x_812 == 0)
{
return x_718;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_718, 0);
x_814 = lean_ctor_get(x_718, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_718);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
}
case 7:
{
lean_object* x_816; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_816 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
if (lean_obj_tag(x_817) == 0)
{
uint8_t x_818; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_818 = !lean_is_exclusive(x_816);
if (x_818 == 0)
{
lean_object* x_819; lean_object* x_820; 
x_819 = lean_ctor_get(x_816, 0);
lean_dec(x_819);
x_820 = lean_box(0);
lean_ctor_set(x_816, 0, x_820);
return x_816;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_816, 1);
lean_inc(x_821);
lean_dec(x_816);
x_822 = lean_box(0);
x_823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_902; 
x_824 = lean_ctor_get(x_816, 1);
lean_inc(x_824);
lean_dec(x_816);
x_825 = lean_ctor_get(x_817, 0);
lean_inc(x_825);
lean_dec(x_817);
x_898 = lean_ctor_get(x_4, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
lean_dec(x_898);
x_900 = lean_ctor_get(x_899, 3);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 4);
lean_inc(x_901);
lean_dec(x_899);
x_902 = lean_nat_dec_eq(x_900, x_901);
lean_dec(x_901);
lean_dec(x_900);
if (x_902 == 0)
{
x_826 = x_824;
goto block_897;
}
else
{
lean_object* x_903; lean_object* x_904; 
x_903 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_904 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_903, x_4, x_824);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; 
x_905 = lean_ctor_get(x_904, 1);
lean_inc(x_905);
lean_dec(x_904);
x_826 = x_905;
goto block_897;
}
else
{
uint8_t x_906; 
lean_dec(x_825);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_906 = !lean_is_exclusive(x_904);
if (x_906 == 0)
{
return x_904;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_904, 0);
x_908 = lean_ctor_get(x_904, 1);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_904);
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_907);
lean_ctor_set(x_909, 1, x_908);
return x_909;
}
}
}
block_897:
{
lean_object* x_827; lean_object* x_828; uint8_t x_829; 
x_827 = lean_ctor_get(x_4, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = !lean_is_exclusive(x_4);
if (x_829 == 0)
{
lean_object* x_830; uint8_t x_831; 
x_830 = lean_ctor_get(x_4, 0);
lean_dec(x_830);
x_831 = !lean_is_exclusive(x_827);
if (x_831 == 0)
{
lean_object* x_832; uint8_t x_833; 
x_832 = lean_ctor_get(x_827, 0);
lean_dec(x_832);
x_833 = !lean_is_exclusive(x_828);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_828, 3);
x_835 = lean_unsigned_to_nat(1u);
x_836 = lean_nat_add(x_834, x_835);
lean_dec(x_834);
lean_ctor_set(x_828, 3, x_836);
x_3 = x_825;
x_5 = x_826;
goto _start;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_838 = lean_ctor_get(x_828, 0);
x_839 = lean_ctor_get(x_828, 1);
x_840 = lean_ctor_get(x_828, 2);
x_841 = lean_ctor_get(x_828, 3);
x_842 = lean_ctor_get(x_828, 4);
lean_inc(x_842);
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_828);
x_843 = lean_unsigned_to_nat(1u);
x_844 = lean_nat_add(x_841, x_843);
lean_dec(x_841);
x_845 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_845, 0, x_838);
lean_ctor_set(x_845, 1, x_839);
lean_ctor_set(x_845, 2, x_840);
lean_ctor_set(x_845, 3, x_844);
lean_ctor_set(x_845, 4, x_842);
lean_ctor_set(x_827, 0, x_845);
x_3 = x_825;
x_5 = x_826;
goto _start;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; uint8_t x_857; uint8_t x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_847 = lean_ctor_get(x_827, 1);
x_848 = lean_ctor_get(x_827, 2);
x_849 = lean_ctor_get(x_827, 3);
x_850 = lean_ctor_get(x_827, 4);
x_851 = lean_ctor_get(x_827, 5);
x_852 = lean_ctor_get(x_827, 6);
x_853 = lean_ctor_get(x_827, 7);
x_854 = lean_ctor_get(x_827, 8);
x_855 = lean_ctor_get(x_827, 9);
x_856 = lean_ctor_get_uint8(x_827, sizeof(void*)*10);
x_857 = lean_ctor_get_uint8(x_827, sizeof(void*)*10 + 1);
x_858 = lean_ctor_get_uint8(x_827, sizeof(void*)*10 + 2);
lean_inc(x_855);
lean_inc(x_854);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_inc(x_849);
lean_inc(x_848);
lean_inc(x_847);
lean_dec(x_827);
x_859 = lean_ctor_get(x_828, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_828, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_828, 2);
lean_inc(x_861);
x_862 = lean_ctor_get(x_828, 3);
lean_inc(x_862);
x_863 = lean_ctor_get(x_828, 4);
lean_inc(x_863);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 lean_ctor_release(x_828, 2);
 lean_ctor_release(x_828, 3);
 lean_ctor_release(x_828, 4);
 x_864 = x_828;
} else {
 lean_dec_ref(x_828);
 x_864 = lean_box(0);
}
x_865 = lean_unsigned_to_nat(1u);
x_866 = lean_nat_add(x_862, x_865);
lean_dec(x_862);
if (lean_is_scalar(x_864)) {
 x_867 = lean_alloc_ctor(0, 5, 0);
} else {
 x_867 = x_864;
}
lean_ctor_set(x_867, 0, x_859);
lean_ctor_set(x_867, 1, x_860);
lean_ctor_set(x_867, 2, x_861);
lean_ctor_set(x_867, 3, x_866);
lean_ctor_set(x_867, 4, x_863);
x_868 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_847);
lean_ctor_set(x_868, 2, x_848);
lean_ctor_set(x_868, 3, x_849);
lean_ctor_set(x_868, 4, x_850);
lean_ctor_set(x_868, 5, x_851);
lean_ctor_set(x_868, 6, x_852);
lean_ctor_set(x_868, 7, x_853);
lean_ctor_set(x_868, 8, x_854);
lean_ctor_set(x_868, 9, x_855);
lean_ctor_set_uint8(x_868, sizeof(void*)*10, x_856);
lean_ctor_set_uint8(x_868, sizeof(void*)*10 + 1, x_857);
lean_ctor_set_uint8(x_868, sizeof(void*)*10 + 2, x_858);
lean_ctor_set(x_4, 0, x_868);
x_3 = x_825;
x_5 = x_826;
goto _start;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; uint8_t x_881; uint8_t x_882; uint8_t x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_870 = lean_ctor_get(x_4, 1);
x_871 = lean_ctor_get(x_4, 2);
lean_inc(x_871);
lean_inc(x_870);
lean_dec(x_4);
x_872 = lean_ctor_get(x_827, 1);
lean_inc(x_872);
x_873 = lean_ctor_get(x_827, 2);
lean_inc(x_873);
x_874 = lean_ctor_get(x_827, 3);
lean_inc(x_874);
x_875 = lean_ctor_get(x_827, 4);
lean_inc(x_875);
x_876 = lean_ctor_get(x_827, 5);
lean_inc(x_876);
x_877 = lean_ctor_get(x_827, 6);
lean_inc(x_877);
x_878 = lean_ctor_get(x_827, 7);
lean_inc(x_878);
x_879 = lean_ctor_get(x_827, 8);
lean_inc(x_879);
x_880 = lean_ctor_get(x_827, 9);
lean_inc(x_880);
x_881 = lean_ctor_get_uint8(x_827, sizeof(void*)*10);
x_882 = lean_ctor_get_uint8(x_827, sizeof(void*)*10 + 1);
x_883 = lean_ctor_get_uint8(x_827, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 lean_ctor_release(x_827, 2);
 lean_ctor_release(x_827, 3);
 lean_ctor_release(x_827, 4);
 lean_ctor_release(x_827, 5);
 lean_ctor_release(x_827, 6);
 lean_ctor_release(x_827, 7);
 lean_ctor_release(x_827, 8);
 lean_ctor_release(x_827, 9);
 x_884 = x_827;
} else {
 lean_dec_ref(x_827);
 x_884 = lean_box(0);
}
x_885 = lean_ctor_get(x_828, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_828, 1);
lean_inc(x_886);
x_887 = lean_ctor_get(x_828, 2);
lean_inc(x_887);
x_888 = lean_ctor_get(x_828, 3);
lean_inc(x_888);
x_889 = lean_ctor_get(x_828, 4);
lean_inc(x_889);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 lean_ctor_release(x_828, 2);
 lean_ctor_release(x_828, 3);
 lean_ctor_release(x_828, 4);
 x_890 = x_828;
} else {
 lean_dec_ref(x_828);
 x_890 = lean_box(0);
}
x_891 = lean_unsigned_to_nat(1u);
x_892 = lean_nat_add(x_888, x_891);
lean_dec(x_888);
if (lean_is_scalar(x_890)) {
 x_893 = lean_alloc_ctor(0, 5, 0);
} else {
 x_893 = x_890;
}
lean_ctor_set(x_893, 0, x_885);
lean_ctor_set(x_893, 1, x_886);
lean_ctor_set(x_893, 2, x_887);
lean_ctor_set(x_893, 3, x_892);
lean_ctor_set(x_893, 4, x_889);
if (lean_is_scalar(x_884)) {
 x_894 = lean_alloc_ctor(0, 10, 3);
} else {
 x_894 = x_884;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_872);
lean_ctor_set(x_894, 2, x_873);
lean_ctor_set(x_894, 3, x_874);
lean_ctor_set(x_894, 4, x_875);
lean_ctor_set(x_894, 5, x_876);
lean_ctor_set(x_894, 6, x_877);
lean_ctor_set(x_894, 7, x_878);
lean_ctor_set(x_894, 8, x_879);
lean_ctor_set(x_894, 9, x_880);
lean_ctor_set_uint8(x_894, sizeof(void*)*10, x_881);
lean_ctor_set_uint8(x_894, sizeof(void*)*10 + 1, x_882);
lean_ctor_set_uint8(x_894, sizeof(void*)*10 + 2, x_883);
x_895 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_870);
lean_ctor_set(x_895, 2, x_871);
x_3 = x_825;
x_4 = x_895;
x_5 = x_826;
goto _start;
}
}
}
}
else
{
uint8_t x_910; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_910 = !lean_is_exclusive(x_816);
if (x_910 == 0)
{
return x_816;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_816, 0);
x_912 = lean_ctor_get(x_816, 1);
lean_inc(x_912);
lean_inc(x_911);
lean_dec(x_816);
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
return x_913;
}
}
}
case 8:
{
lean_object* x_914; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_914 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; 
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
if (lean_obj_tag(x_915) == 0)
{
uint8_t x_916; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_916 = !lean_is_exclusive(x_914);
if (x_916 == 0)
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_914, 0);
lean_dec(x_917);
x_918 = lean_box(0);
lean_ctor_set(x_914, 0, x_918);
return x_914;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_914, 1);
lean_inc(x_919);
lean_dec(x_914);
x_920 = lean_box(0);
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_919);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; 
x_922 = lean_ctor_get(x_914, 1);
lean_inc(x_922);
lean_dec(x_914);
x_923 = lean_ctor_get(x_915, 0);
lean_inc(x_923);
lean_dec(x_915);
x_996 = lean_ctor_get(x_4, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
lean_dec(x_996);
x_998 = lean_ctor_get(x_997, 3);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 4);
lean_inc(x_999);
lean_dec(x_997);
x_1000 = lean_nat_dec_eq(x_998, x_999);
lean_dec(x_999);
lean_dec(x_998);
if (x_1000 == 0)
{
x_924 = x_922;
goto block_995;
}
else
{
lean_object* x_1001; lean_object* x_1002; 
x_1001 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1002 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1001, x_4, x_922);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; 
x_1003 = lean_ctor_get(x_1002, 1);
lean_inc(x_1003);
lean_dec(x_1002);
x_924 = x_1003;
goto block_995;
}
else
{
uint8_t x_1004; 
lean_dec(x_923);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1004 = !lean_is_exclusive(x_1002);
if (x_1004 == 0)
{
return x_1002;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1005 = lean_ctor_get(x_1002, 0);
x_1006 = lean_ctor_get(x_1002, 1);
lean_inc(x_1006);
lean_inc(x_1005);
lean_dec(x_1002);
x_1007 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1007, 0, x_1005);
lean_ctor_set(x_1007, 1, x_1006);
return x_1007;
}
}
}
block_995:
{
lean_object* x_925; lean_object* x_926; uint8_t x_927; 
x_925 = lean_ctor_get(x_4, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = !lean_is_exclusive(x_4);
if (x_927 == 0)
{
lean_object* x_928; uint8_t x_929; 
x_928 = lean_ctor_get(x_4, 0);
lean_dec(x_928);
x_929 = !lean_is_exclusive(x_925);
if (x_929 == 0)
{
lean_object* x_930; uint8_t x_931; 
x_930 = lean_ctor_get(x_925, 0);
lean_dec(x_930);
x_931 = !lean_is_exclusive(x_926);
if (x_931 == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_932 = lean_ctor_get(x_926, 3);
x_933 = lean_unsigned_to_nat(1u);
x_934 = lean_nat_add(x_932, x_933);
lean_dec(x_932);
lean_ctor_set(x_926, 3, x_934);
x_3 = x_923;
x_5 = x_924;
goto _start;
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_936 = lean_ctor_get(x_926, 0);
x_937 = lean_ctor_get(x_926, 1);
x_938 = lean_ctor_get(x_926, 2);
x_939 = lean_ctor_get(x_926, 3);
x_940 = lean_ctor_get(x_926, 4);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_inc(x_936);
lean_dec(x_926);
x_941 = lean_unsigned_to_nat(1u);
x_942 = lean_nat_add(x_939, x_941);
lean_dec(x_939);
x_943 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_943, 0, x_936);
lean_ctor_set(x_943, 1, x_937);
lean_ctor_set(x_943, 2, x_938);
lean_ctor_set(x_943, 3, x_942);
lean_ctor_set(x_943, 4, x_940);
lean_ctor_set(x_925, 0, x_943);
x_3 = x_923;
x_5 = x_924;
goto _start;
}
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; uint8_t x_955; uint8_t x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_945 = lean_ctor_get(x_925, 1);
x_946 = lean_ctor_get(x_925, 2);
x_947 = lean_ctor_get(x_925, 3);
x_948 = lean_ctor_get(x_925, 4);
x_949 = lean_ctor_get(x_925, 5);
x_950 = lean_ctor_get(x_925, 6);
x_951 = lean_ctor_get(x_925, 7);
x_952 = lean_ctor_get(x_925, 8);
x_953 = lean_ctor_get(x_925, 9);
x_954 = lean_ctor_get_uint8(x_925, sizeof(void*)*10);
x_955 = lean_ctor_get_uint8(x_925, sizeof(void*)*10 + 1);
x_956 = lean_ctor_get_uint8(x_925, sizeof(void*)*10 + 2);
lean_inc(x_953);
lean_inc(x_952);
lean_inc(x_951);
lean_inc(x_950);
lean_inc(x_949);
lean_inc(x_948);
lean_inc(x_947);
lean_inc(x_946);
lean_inc(x_945);
lean_dec(x_925);
x_957 = lean_ctor_get(x_926, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_926, 1);
lean_inc(x_958);
x_959 = lean_ctor_get(x_926, 2);
lean_inc(x_959);
x_960 = lean_ctor_get(x_926, 3);
lean_inc(x_960);
x_961 = lean_ctor_get(x_926, 4);
lean_inc(x_961);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 lean_ctor_release(x_926, 2);
 lean_ctor_release(x_926, 3);
 lean_ctor_release(x_926, 4);
 x_962 = x_926;
} else {
 lean_dec_ref(x_926);
 x_962 = lean_box(0);
}
x_963 = lean_unsigned_to_nat(1u);
x_964 = lean_nat_add(x_960, x_963);
lean_dec(x_960);
if (lean_is_scalar(x_962)) {
 x_965 = lean_alloc_ctor(0, 5, 0);
} else {
 x_965 = x_962;
}
lean_ctor_set(x_965, 0, x_957);
lean_ctor_set(x_965, 1, x_958);
lean_ctor_set(x_965, 2, x_959);
lean_ctor_set(x_965, 3, x_964);
lean_ctor_set(x_965, 4, x_961);
x_966 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_966, 0, x_965);
lean_ctor_set(x_966, 1, x_945);
lean_ctor_set(x_966, 2, x_946);
lean_ctor_set(x_966, 3, x_947);
lean_ctor_set(x_966, 4, x_948);
lean_ctor_set(x_966, 5, x_949);
lean_ctor_set(x_966, 6, x_950);
lean_ctor_set(x_966, 7, x_951);
lean_ctor_set(x_966, 8, x_952);
lean_ctor_set(x_966, 9, x_953);
lean_ctor_set_uint8(x_966, sizeof(void*)*10, x_954);
lean_ctor_set_uint8(x_966, sizeof(void*)*10 + 1, x_955);
lean_ctor_set_uint8(x_966, sizeof(void*)*10 + 2, x_956);
lean_ctor_set(x_4, 0, x_966);
x_3 = x_923;
x_5 = x_924;
goto _start;
}
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; uint8_t x_980; uint8_t x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_968 = lean_ctor_get(x_4, 1);
x_969 = lean_ctor_get(x_4, 2);
lean_inc(x_969);
lean_inc(x_968);
lean_dec(x_4);
x_970 = lean_ctor_get(x_925, 1);
lean_inc(x_970);
x_971 = lean_ctor_get(x_925, 2);
lean_inc(x_971);
x_972 = lean_ctor_get(x_925, 3);
lean_inc(x_972);
x_973 = lean_ctor_get(x_925, 4);
lean_inc(x_973);
x_974 = lean_ctor_get(x_925, 5);
lean_inc(x_974);
x_975 = lean_ctor_get(x_925, 6);
lean_inc(x_975);
x_976 = lean_ctor_get(x_925, 7);
lean_inc(x_976);
x_977 = lean_ctor_get(x_925, 8);
lean_inc(x_977);
x_978 = lean_ctor_get(x_925, 9);
lean_inc(x_978);
x_979 = lean_ctor_get_uint8(x_925, sizeof(void*)*10);
x_980 = lean_ctor_get_uint8(x_925, sizeof(void*)*10 + 1);
x_981 = lean_ctor_get_uint8(x_925, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 lean_ctor_release(x_925, 2);
 lean_ctor_release(x_925, 3);
 lean_ctor_release(x_925, 4);
 lean_ctor_release(x_925, 5);
 lean_ctor_release(x_925, 6);
 lean_ctor_release(x_925, 7);
 lean_ctor_release(x_925, 8);
 lean_ctor_release(x_925, 9);
 x_982 = x_925;
} else {
 lean_dec_ref(x_925);
 x_982 = lean_box(0);
}
x_983 = lean_ctor_get(x_926, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_926, 1);
lean_inc(x_984);
x_985 = lean_ctor_get(x_926, 2);
lean_inc(x_985);
x_986 = lean_ctor_get(x_926, 3);
lean_inc(x_986);
x_987 = lean_ctor_get(x_926, 4);
lean_inc(x_987);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 lean_ctor_release(x_926, 2);
 lean_ctor_release(x_926, 3);
 lean_ctor_release(x_926, 4);
 x_988 = x_926;
} else {
 lean_dec_ref(x_926);
 x_988 = lean_box(0);
}
x_989 = lean_unsigned_to_nat(1u);
x_990 = lean_nat_add(x_986, x_989);
lean_dec(x_986);
if (lean_is_scalar(x_988)) {
 x_991 = lean_alloc_ctor(0, 5, 0);
} else {
 x_991 = x_988;
}
lean_ctor_set(x_991, 0, x_983);
lean_ctor_set(x_991, 1, x_984);
lean_ctor_set(x_991, 2, x_985);
lean_ctor_set(x_991, 3, x_990);
lean_ctor_set(x_991, 4, x_987);
if (lean_is_scalar(x_982)) {
 x_992 = lean_alloc_ctor(0, 10, 3);
} else {
 x_992 = x_982;
}
lean_ctor_set(x_992, 0, x_991);
lean_ctor_set(x_992, 1, x_970);
lean_ctor_set(x_992, 2, x_971);
lean_ctor_set(x_992, 3, x_972);
lean_ctor_set(x_992, 4, x_973);
lean_ctor_set(x_992, 5, x_974);
lean_ctor_set(x_992, 6, x_975);
lean_ctor_set(x_992, 7, x_976);
lean_ctor_set(x_992, 8, x_977);
lean_ctor_set(x_992, 9, x_978);
lean_ctor_set_uint8(x_992, sizeof(void*)*10, x_979);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 1, x_980);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 2, x_981);
x_993 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_968);
lean_ctor_set(x_993, 2, x_969);
x_3 = x_923;
x_4 = x_993;
x_5 = x_924;
goto _start;
}
}
}
}
else
{
uint8_t x_1008; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1008 = !lean_is_exclusive(x_914);
if (x_1008 == 0)
{
return x_914;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_914, 0);
x_1010 = lean_ctor_get(x_914, 1);
lean_inc(x_1010);
lean_inc(x_1009);
lean_dec(x_914);
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_1010);
return x_1011;
}
}
}
case 9:
{
lean_object* x_1012; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1012 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
if (lean_obj_tag(x_1013) == 0)
{
uint8_t x_1014; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1014 = !lean_is_exclusive(x_1012);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; 
x_1015 = lean_ctor_get(x_1012, 0);
lean_dec(x_1015);
x_1016 = lean_box(0);
lean_ctor_set(x_1012, 0, x_1016);
return x_1012;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_1012, 1);
lean_inc(x_1017);
lean_dec(x_1012);
x_1018 = lean_box(0);
x_1019 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; uint8_t x_1098; 
x_1020 = lean_ctor_get(x_1012, 1);
lean_inc(x_1020);
lean_dec(x_1012);
x_1021 = lean_ctor_get(x_1013, 0);
lean_inc(x_1021);
lean_dec(x_1013);
x_1094 = lean_ctor_get(x_4, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
lean_dec(x_1094);
x_1096 = lean_ctor_get(x_1095, 3);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1095, 4);
lean_inc(x_1097);
lean_dec(x_1095);
x_1098 = lean_nat_dec_eq(x_1096, x_1097);
lean_dec(x_1097);
lean_dec(x_1096);
if (x_1098 == 0)
{
x_1022 = x_1020;
goto block_1093;
}
else
{
lean_object* x_1099; lean_object* x_1100; 
x_1099 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1100 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1099, x_4, x_1020);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; 
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc(x_1101);
lean_dec(x_1100);
x_1022 = x_1101;
goto block_1093;
}
else
{
uint8_t x_1102; 
lean_dec(x_1021);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1102 = !lean_is_exclusive(x_1100);
if (x_1102 == 0)
{
return x_1100;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1103 = lean_ctor_get(x_1100, 0);
x_1104 = lean_ctor_get(x_1100, 1);
lean_inc(x_1104);
lean_inc(x_1103);
lean_dec(x_1100);
x_1105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1105, 0, x_1103);
lean_ctor_set(x_1105, 1, x_1104);
return x_1105;
}
}
}
block_1093:
{
lean_object* x_1023; lean_object* x_1024; uint8_t x_1025; 
x_1023 = lean_ctor_get(x_4, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
x_1025 = !lean_is_exclusive(x_4);
if (x_1025 == 0)
{
lean_object* x_1026; uint8_t x_1027; 
x_1026 = lean_ctor_get(x_4, 0);
lean_dec(x_1026);
x_1027 = !lean_is_exclusive(x_1023);
if (x_1027 == 0)
{
lean_object* x_1028; uint8_t x_1029; 
x_1028 = lean_ctor_get(x_1023, 0);
lean_dec(x_1028);
x_1029 = !lean_is_exclusive(x_1024);
if (x_1029 == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1024, 3);
x_1031 = lean_unsigned_to_nat(1u);
x_1032 = lean_nat_add(x_1030, x_1031);
lean_dec(x_1030);
lean_ctor_set(x_1024, 3, x_1032);
x_3 = x_1021;
x_5 = x_1022;
goto _start;
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1034 = lean_ctor_get(x_1024, 0);
x_1035 = lean_ctor_get(x_1024, 1);
x_1036 = lean_ctor_get(x_1024, 2);
x_1037 = lean_ctor_get(x_1024, 3);
x_1038 = lean_ctor_get(x_1024, 4);
lean_inc(x_1038);
lean_inc(x_1037);
lean_inc(x_1036);
lean_inc(x_1035);
lean_inc(x_1034);
lean_dec(x_1024);
x_1039 = lean_unsigned_to_nat(1u);
x_1040 = lean_nat_add(x_1037, x_1039);
lean_dec(x_1037);
x_1041 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1041, 0, x_1034);
lean_ctor_set(x_1041, 1, x_1035);
lean_ctor_set(x_1041, 2, x_1036);
lean_ctor_set(x_1041, 3, x_1040);
lean_ctor_set(x_1041, 4, x_1038);
lean_ctor_set(x_1023, 0, x_1041);
x_3 = x_1021;
x_5 = x_1022;
goto _start;
}
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; uint8_t x_1053; uint8_t x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1043 = lean_ctor_get(x_1023, 1);
x_1044 = lean_ctor_get(x_1023, 2);
x_1045 = lean_ctor_get(x_1023, 3);
x_1046 = lean_ctor_get(x_1023, 4);
x_1047 = lean_ctor_get(x_1023, 5);
x_1048 = lean_ctor_get(x_1023, 6);
x_1049 = lean_ctor_get(x_1023, 7);
x_1050 = lean_ctor_get(x_1023, 8);
x_1051 = lean_ctor_get(x_1023, 9);
x_1052 = lean_ctor_get_uint8(x_1023, sizeof(void*)*10);
x_1053 = lean_ctor_get_uint8(x_1023, sizeof(void*)*10 + 1);
x_1054 = lean_ctor_get_uint8(x_1023, sizeof(void*)*10 + 2);
lean_inc(x_1051);
lean_inc(x_1050);
lean_inc(x_1049);
lean_inc(x_1048);
lean_inc(x_1047);
lean_inc(x_1046);
lean_inc(x_1045);
lean_inc(x_1044);
lean_inc(x_1043);
lean_dec(x_1023);
x_1055 = lean_ctor_get(x_1024, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1024, 1);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1024, 2);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1024, 3);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1024, 4);
lean_inc(x_1059);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 lean_ctor_release(x_1024, 1);
 lean_ctor_release(x_1024, 2);
 lean_ctor_release(x_1024, 3);
 lean_ctor_release(x_1024, 4);
 x_1060 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1060 = lean_box(0);
}
x_1061 = lean_unsigned_to_nat(1u);
x_1062 = lean_nat_add(x_1058, x_1061);
lean_dec(x_1058);
if (lean_is_scalar(x_1060)) {
 x_1063 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1063 = x_1060;
}
lean_ctor_set(x_1063, 0, x_1055);
lean_ctor_set(x_1063, 1, x_1056);
lean_ctor_set(x_1063, 2, x_1057);
lean_ctor_set(x_1063, 3, x_1062);
lean_ctor_set(x_1063, 4, x_1059);
x_1064 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1064, 0, x_1063);
lean_ctor_set(x_1064, 1, x_1043);
lean_ctor_set(x_1064, 2, x_1044);
lean_ctor_set(x_1064, 3, x_1045);
lean_ctor_set(x_1064, 4, x_1046);
lean_ctor_set(x_1064, 5, x_1047);
lean_ctor_set(x_1064, 6, x_1048);
lean_ctor_set(x_1064, 7, x_1049);
lean_ctor_set(x_1064, 8, x_1050);
lean_ctor_set(x_1064, 9, x_1051);
lean_ctor_set_uint8(x_1064, sizeof(void*)*10, x_1052);
lean_ctor_set_uint8(x_1064, sizeof(void*)*10 + 1, x_1053);
lean_ctor_set_uint8(x_1064, sizeof(void*)*10 + 2, x_1054);
lean_ctor_set(x_4, 0, x_1064);
x_3 = x_1021;
x_5 = x_1022;
goto _start;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; uint8_t x_1078; uint8_t x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1066 = lean_ctor_get(x_4, 1);
x_1067 = lean_ctor_get(x_4, 2);
lean_inc(x_1067);
lean_inc(x_1066);
lean_dec(x_4);
x_1068 = lean_ctor_get(x_1023, 1);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1023, 2);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1023, 3);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1023, 4);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1023, 5);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1023, 6);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1023, 7);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1023, 8);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1023, 9);
lean_inc(x_1076);
x_1077 = lean_ctor_get_uint8(x_1023, sizeof(void*)*10);
x_1078 = lean_ctor_get_uint8(x_1023, sizeof(void*)*10 + 1);
x_1079 = lean_ctor_get_uint8(x_1023, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 lean_ctor_release(x_1023, 2);
 lean_ctor_release(x_1023, 3);
 lean_ctor_release(x_1023, 4);
 lean_ctor_release(x_1023, 5);
 lean_ctor_release(x_1023, 6);
 lean_ctor_release(x_1023, 7);
 lean_ctor_release(x_1023, 8);
 lean_ctor_release(x_1023, 9);
 x_1080 = x_1023;
} else {
 lean_dec_ref(x_1023);
 x_1080 = lean_box(0);
}
x_1081 = lean_ctor_get(x_1024, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1024, 1);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1024, 2);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1024, 3);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1024, 4);
lean_inc(x_1085);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 lean_ctor_release(x_1024, 1);
 lean_ctor_release(x_1024, 2);
 lean_ctor_release(x_1024, 3);
 lean_ctor_release(x_1024, 4);
 x_1086 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1086 = lean_box(0);
}
x_1087 = lean_unsigned_to_nat(1u);
x_1088 = lean_nat_add(x_1084, x_1087);
lean_dec(x_1084);
if (lean_is_scalar(x_1086)) {
 x_1089 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1089 = x_1086;
}
lean_ctor_set(x_1089, 0, x_1081);
lean_ctor_set(x_1089, 1, x_1082);
lean_ctor_set(x_1089, 2, x_1083);
lean_ctor_set(x_1089, 3, x_1088);
lean_ctor_set(x_1089, 4, x_1085);
if (lean_is_scalar(x_1080)) {
 x_1090 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1090 = x_1080;
}
lean_ctor_set(x_1090, 0, x_1089);
lean_ctor_set(x_1090, 1, x_1068);
lean_ctor_set(x_1090, 2, x_1069);
lean_ctor_set(x_1090, 3, x_1070);
lean_ctor_set(x_1090, 4, x_1071);
lean_ctor_set(x_1090, 5, x_1072);
lean_ctor_set(x_1090, 6, x_1073);
lean_ctor_set(x_1090, 7, x_1074);
lean_ctor_set(x_1090, 8, x_1075);
lean_ctor_set(x_1090, 9, x_1076);
lean_ctor_set_uint8(x_1090, sizeof(void*)*10, x_1077);
lean_ctor_set_uint8(x_1090, sizeof(void*)*10 + 1, x_1078);
lean_ctor_set_uint8(x_1090, sizeof(void*)*10 + 2, x_1079);
x_1091 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1091, 0, x_1090);
lean_ctor_set(x_1091, 1, x_1066);
lean_ctor_set(x_1091, 2, x_1067);
x_3 = x_1021;
x_4 = x_1091;
x_5 = x_1022;
goto _start;
}
}
}
}
else
{
uint8_t x_1106; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1106 = !lean_is_exclusive(x_1012);
if (x_1106 == 0)
{
return x_1012;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1012, 0);
x_1108 = lean_ctor_get(x_1012, 1);
lean_inc(x_1108);
lean_inc(x_1107);
lean_dec(x_1012);
x_1109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1109, 0, x_1107);
lean_ctor_set(x_1109, 1, x_1108);
return x_1109;
}
}
}
case 10:
{
lean_object* x_1110; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1110 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1110) == 0)
{
lean_object* x_1111; 
x_1111 = lean_ctor_get(x_1110, 0);
lean_inc(x_1111);
if (lean_obj_tag(x_1111) == 0)
{
uint8_t x_1112; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1112 = !lean_is_exclusive(x_1110);
if (x_1112 == 0)
{
lean_object* x_1113; lean_object* x_1114; 
x_1113 = lean_ctor_get(x_1110, 0);
lean_dec(x_1113);
x_1114 = lean_box(0);
lean_ctor_set(x_1110, 0, x_1114);
return x_1110;
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1115 = lean_ctor_get(x_1110, 1);
lean_inc(x_1115);
lean_dec(x_1110);
x_1116 = lean_box(0);
x_1117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1115);
return x_1117;
}
}
else
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; 
x_1118 = lean_ctor_get(x_1110, 1);
lean_inc(x_1118);
lean_dec(x_1110);
x_1119 = lean_ctor_get(x_1111, 0);
lean_inc(x_1119);
lean_dec(x_1111);
x_1192 = lean_ctor_get(x_4, 0);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
lean_dec(x_1192);
x_1194 = lean_ctor_get(x_1193, 3);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1193, 4);
lean_inc(x_1195);
lean_dec(x_1193);
x_1196 = lean_nat_dec_eq(x_1194, x_1195);
lean_dec(x_1195);
lean_dec(x_1194);
if (x_1196 == 0)
{
x_1120 = x_1118;
goto block_1191;
}
else
{
lean_object* x_1197; lean_object* x_1198; 
x_1197 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1198 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1197, x_4, x_1118);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; 
x_1199 = lean_ctor_get(x_1198, 1);
lean_inc(x_1199);
lean_dec(x_1198);
x_1120 = x_1199;
goto block_1191;
}
else
{
uint8_t x_1200; 
lean_dec(x_1119);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1200 = !lean_is_exclusive(x_1198);
if (x_1200 == 0)
{
return x_1198;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_1198, 0);
x_1202 = lean_ctor_get(x_1198, 1);
lean_inc(x_1202);
lean_inc(x_1201);
lean_dec(x_1198);
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1201);
lean_ctor_set(x_1203, 1, x_1202);
return x_1203;
}
}
}
block_1191:
{
lean_object* x_1121; lean_object* x_1122; uint8_t x_1123; 
x_1121 = lean_ctor_get(x_4, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = !lean_is_exclusive(x_4);
if (x_1123 == 0)
{
lean_object* x_1124; uint8_t x_1125; 
x_1124 = lean_ctor_get(x_4, 0);
lean_dec(x_1124);
x_1125 = !lean_is_exclusive(x_1121);
if (x_1125 == 0)
{
lean_object* x_1126; uint8_t x_1127; 
x_1126 = lean_ctor_get(x_1121, 0);
lean_dec(x_1126);
x_1127 = !lean_is_exclusive(x_1122);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = lean_ctor_get(x_1122, 3);
x_1129 = lean_unsigned_to_nat(1u);
x_1130 = lean_nat_add(x_1128, x_1129);
lean_dec(x_1128);
lean_ctor_set(x_1122, 3, x_1130);
x_3 = x_1119;
x_5 = x_1120;
goto _start;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1132 = lean_ctor_get(x_1122, 0);
x_1133 = lean_ctor_get(x_1122, 1);
x_1134 = lean_ctor_get(x_1122, 2);
x_1135 = lean_ctor_get(x_1122, 3);
x_1136 = lean_ctor_get(x_1122, 4);
lean_inc(x_1136);
lean_inc(x_1135);
lean_inc(x_1134);
lean_inc(x_1133);
lean_inc(x_1132);
lean_dec(x_1122);
x_1137 = lean_unsigned_to_nat(1u);
x_1138 = lean_nat_add(x_1135, x_1137);
lean_dec(x_1135);
x_1139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1139, 0, x_1132);
lean_ctor_set(x_1139, 1, x_1133);
lean_ctor_set(x_1139, 2, x_1134);
lean_ctor_set(x_1139, 3, x_1138);
lean_ctor_set(x_1139, 4, x_1136);
lean_ctor_set(x_1121, 0, x_1139);
x_3 = x_1119;
x_5 = x_1120;
goto _start;
}
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; uint8_t x_1151; uint8_t x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1141 = lean_ctor_get(x_1121, 1);
x_1142 = lean_ctor_get(x_1121, 2);
x_1143 = lean_ctor_get(x_1121, 3);
x_1144 = lean_ctor_get(x_1121, 4);
x_1145 = lean_ctor_get(x_1121, 5);
x_1146 = lean_ctor_get(x_1121, 6);
x_1147 = lean_ctor_get(x_1121, 7);
x_1148 = lean_ctor_get(x_1121, 8);
x_1149 = lean_ctor_get(x_1121, 9);
x_1150 = lean_ctor_get_uint8(x_1121, sizeof(void*)*10);
x_1151 = lean_ctor_get_uint8(x_1121, sizeof(void*)*10 + 1);
x_1152 = lean_ctor_get_uint8(x_1121, sizeof(void*)*10 + 2);
lean_inc(x_1149);
lean_inc(x_1148);
lean_inc(x_1147);
lean_inc(x_1146);
lean_inc(x_1145);
lean_inc(x_1144);
lean_inc(x_1143);
lean_inc(x_1142);
lean_inc(x_1141);
lean_dec(x_1121);
x_1153 = lean_ctor_get(x_1122, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1122, 1);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1122, 2);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1122, 3);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1122, 4);
lean_inc(x_1157);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 lean_ctor_release(x_1122, 2);
 lean_ctor_release(x_1122, 3);
 lean_ctor_release(x_1122, 4);
 x_1158 = x_1122;
} else {
 lean_dec_ref(x_1122);
 x_1158 = lean_box(0);
}
x_1159 = lean_unsigned_to_nat(1u);
x_1160 = lean_nat_add(x_1156, x_1159);
lean_dec(x_1156);
if (lean_is_scalar(x_1158)) {
 x_1161 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1161 = x_1158;
}
lean_ctor_set(x_1161, 0, x_1153);
lean_ctor_set(x_1161, 1, x_1154);
lean_ctor_set(x_1161, 2, x_1155);
lean_ctor_set(x_1161, 3, x_1160);
lean_ctor_set(x_1161, 4, x_1157);
x_1162 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1162, 0, x_1161);
lean_ctor_set(x_1162, 1, x_1141);
lean_ctor_set(x_1162, 2, x_1142);
lean_ctor_set(x_1162, 3, x_1143);
lean_ctor_set(x_1162, 4, x_1144);
lean_ctor_set(x_1162, 5, x_1145);
lean_ctor_set(x_1162, 6, x_1146);
lean_ctor_set(x_1162, 7, x_1147);
lean_ctor_set(x_1162, 8, x_1148);
lean_ctor_set(x_1162, 9, x_1149);
lean_ctor_set_uint8(x_1162, sizeof(void*)*10, x_1150);
lean_ctor_set_uint8(x_1162, sizeof(void*)*10 + 1, x_1151);
lean_ctor_set_uint8(x_1162, sizeof(void*)*10 + 2, x_1152);
lean_ctor_set(x_4, 0, x_1162);
x_3 = x_1119;
x_5 = x_1120;
goto _start;
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; uint8_t x_1176; uint8_t x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1164 = lean_ctor_get(x_4, 1);
x_1165 = lean_ctor_get(x_4, 2);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_4);
x_1166 = lean_ctor_get(x_1121, 1);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1121, 2);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1121, 3);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1121, 4);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1121, 5);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1121, 6);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1121, 7);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1121, 8);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1121, 9);
lean_inc(x_1174);
x_1175 = lean_ctor_get_uint8(x_1121, sizeof(void*)*10);
x_1176 = lean_ctor_get_uint8(x_1121, sizeof(void*)*10 + 1);
x_1177 = lean_ctor_get_uint8(x_1121, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 lean_ctor_release(x_1121, 2);
 lean_ctor_release(x_1121, 3);
 lean_ctor_release(x_1121, 4);
 lean_ctor_release(x_1121, 5);
 lean_ctor_release(x_1121, 6);
 lean_ctor_release(x_1121, 7);
 lean_ctor_release(x_1121, 8);
 lean_ctor_release(x_1121, 9);
 x_1178 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1178 = lean_box(0);
}
x_1179 = lean_ctor_get(x_1122, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1122, 1);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1122, 2);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1122, 3);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1122, 4);
lean_inc(x_1183);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 lean_ctor_release(x_1122, 2);
 lean_ctor_release(x_1122, 3);
 lean_ctor_release(x_1122, 4);
 x_1184 = x_1122;
} else {
 lean_dec_ref(x_1122);
 x_1184 = lean_box(0);
}
x_1185 = lean_unsigned_to_nat(1u);
x_1186 = lean_nat_add(x_1182, x_1185);
lean_dec(x_1182);
if (lean_is_scalar(x_1184)) {
 x_1187 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1187 = x_1184;
}
lean_ctor_set(x_1187, 0, x_1179);
lean_ctor_set(x_1187, 1, x_1180);
lean_ctor_set(x_1187, 2, x_1181);
lean_ctor_set(x_1187, 3, x_1186);
lean_ctor_set(x_1187, 4, x_1183);
if (lean_is_scalar(x_1178)) {
 x_1188 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1188 = x_1178;
}
lean_ctor_set(x_1188, 0, x_1187);
lean_ctor_set(x_1188, 1, x_1166);
lean_ctor_set(x_1188, 2, x_1167);
lean_ctor_set(x_1188, 3, x_1168);
lean_ctor_set(x_1188, 4, x_1169);
lean_ctor_set(x_1188, 5, x_1170);
lean_ctor_set(x_1188, 6, x_1171);
lean_ctor_set(x_1188, 7, x_1172);
lean_ctor_set(x_1188, 8, x_1173);
lean_ctor_set(x_1188, 9, x_1174);
lean_ctor_set_uint8(x_1188, sizeof(void*)*10, x_1175);
lean_ctor_set_uint8(x_1188, sizeof(void*)*10 + 1, x_1176);
lean_ctor_set_uint8(x_1188, sizeof(void*)*10 + 2, x_1177);
x_1189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1189, 0, x_1188);
lean_ctor_set(x_1189, 1, x_1164);
lean_ctor_set(x_1189, 2, x_1165);
x_3 = x_1119;
x_4 = x_1189;
x_5 = x_1120;
goto _start;
}
}
}
}
else
{
uint8_t x_1204; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1204 = !lean_is_exclusive(x_1110);
if (x_1204 == 0)
{
return x_1110;
}
else
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1205 = lean_ctor_get(x_1110, 0);
x_1206 = lean_ctor_get(x_1110, 1);
lean_inc(x_1206);
lean_inc(x_1205);
lean_dec(x_1110);
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1205);
lean_ctor_set(x_1207, 1, x_1206);
return x_1207;
}
}
}
case 11:
{
lean_object* x_1208; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1208 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1208) == 0)
{
lean_object* x_1209; 
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
if (lean_obj_tag(x_1209) == 0)
{
uint8_t x_1210; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1210 = !lean_is_exclusive(x_1208);
if (x_1210 == 0)
{
lean_object* x_1211; lean_object* x_1212; 
x_1211 = lean_ctor_get(x_1208, 0);
lean_dec(x_1211);
x_1212 = lean_box(0);
lean_ctor_set(x_1208, 0, x_1212);
return x_1208;
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1208, 1);
lean_inc(x_1213);
lean_dec(x_1208);
x_1214 = lean_box(0);
x_1215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1215, 0, x_1214);
lean_ctor_set(x_1215, 1, x_1213);
return x_1215;
}
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; uint8_t x_1294; 
x_1216 = lean_ctor_get(x_1208, 1);
lean_inc(x_1216);
lean_dec(x_1208);
x_1217 = lean_ctor_get(x_1209, 0);
lean_inc(x_1217);
lean_dec(x_1209);
x_1290 = lean_ctor_get(x_4, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1290, 0);
lean_inc(x_1291);
lean_dec(x_1290);
x_1292 = lean_ctor_get(x_1291, 3);
lean_inc(x_1292);
x_1293 = lean_ctor_get(x_1291, 4);
lean_inc(x_1293);
lean_dec(x_1291);
x_1294 = lean_nat_dec_eq(x_1292, x_1293);
lean_dec(x_1293);
lean_dec(x_1292);
if (x_1294 == 0)
{
x_1218 = x_1216;
goto block_1289;
}
else
{
lean_object* x_1295; lean_object* x_1296; 
x_1295 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1296 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1295, x_4, x_1216);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; 
x_1297 = lean_ctor_get(x_1296, 1);
lean_inc(x_1297);
lean_dec(x_1296);
x_1218 = x_1297;
goto block_1289;
}
else
{
uint8_t x_1298; 
lean_dec(x_1217);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1298 = !lean_is_exclusive(x_1296);
if (x_1298 == 0)
{
return x_1296;
}
else
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1299 = lean_ctor_get(x_1296, 0);
x_1300 = lean_ctor_get(x_1296, 1);
lean_inc(x_1300);
lean_inc(x_1299);
lean_dec(x_1296);
x_1301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1301, 0, x_1299);
lean_ctor_set(x_1301, 1, x_1300);
return x_1301;
}
}
}
block_1289:
{
lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; 
x_1219 = lean_ctor_get(x_4, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
x_1221 = !lean_is_exclusive(x_4);
if (x_1221 == 0)
{
lean_object* x_1222; uint8_t x_1223; 
x_1222 = lean_ctor_get(x_4, 0);
lean_dec(x_1222);
x_1223 = !lean_is_exclusive(x_1219);
if (x_1223 == 0)
{
lean_object* x_1224; uint8_t x_1225; 
x_1224 = lean_ctor_get(x_1219, 0);
lean_dec(x_1224);
x_1225 = !lean_is_exclusive(x_1220);
if (x_1225 == 0)
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
x_1226 = lean_ctor_get(x_1220, 3);
x_1227 = lean_unsigned_to_nat(1u);
x_1228 = lean_nat_add(x_1226, x_1227);
lean_dec(x_1226);
lean_ctor_set(x_1220, 3, x_1228);
x_3 = x_1217;
x_5 = x_1218;
goto _start;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1230 = lean_ctor_get(x_1220, 0);
x_1231 = lean_ctor_get(x_1220, 1);
x_1232 = lean_ctor_get(x_1220, 2);
x_1233 = lean_ctor_get(x_1220, 3);
x_1234 = lean_ctor_get(x_1220, 4);
lean_inc(x_1234);
lean_inc(x_1233);
lean_inc(x_1232);
lean_inc(x_1231);
lean_inc(x_1230);
lean_dec(x_1220);
x_1235 = lean_unsigned_to_nat(1u);
x_1236 = lean_nat_add(x_1233, x_1235);
lean_dec(x_1233);
x_1237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1237, 0, x_1230);
lean_ctor_set(x_1237, 1, x_1231);
lean_ctor_set(x_1237, 2, x_1232);
lean_ctor_set(x_1237, 3, x_1236);
lean_ctor_set(x_1237, 4, x_1234);
lean_ctor_set(x_1219, 0, x_1237);
x_3 = x_1217;
x_5 = x_1218;
goto _start;
}
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; uint8_t x_1248; uint8_t x_1249; uint8_t x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1239 = lean_ctor_get(x_1219, 1);
x_1240 = lean_ctor_get(x_1219, 2);
x_1241 = lean_ctor_get(x_1219, 3);
x_1242 = lean_ctor_get(x_1219, 4);
x_1243 = lean_ctor_get(x_1219, 5);
x_1244 = lean_ctor_get(x_1219, 6);
x_1245 = lean_ctor_get(x_1219, 7);
x_1246 = lean_ctor_get(x_1219, 8);
x_1247 = lean_ctor_get(x_1219, 9);
x_1248 = lean_ctor_get_uint8(x_1219, sizeof(void*)*10);
x_1249 = lean_ctor_get_uint8(x_1219, sizeof(void*)*10 + 1);
x_1250 = lean_ctor_get_uint8(x_1219, sizeof(void*)*10 + 2);
lean_inc(x_1247);
lean_inc(x_1246);
lean_inc(x_1245);
lean_inc(x_1244);
lean_inc(x_1243);
lean_inc(x_1242);
lean_inc(x_1241);
lean_inc(x_1240);
lean_inc(x_1239);
lean_dec(x_1219);
x_1251 = lean_ctor_get(x_1220, 0);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1220, 1);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1220, 2);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1220, 3);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1220, 4);
lean_inc(x_1255);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 lean_ctor_release(x_1220, 1);
 lean_ctor_release(x_1220, 2);
 lean_ctor_release(x_1220, 3);
 lean_ctor_release(x_1220, 4);
 x_1256 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1256 = lean_box(0);
}
x_1257 = lean_unsigned_to_nat(1u);
x_1258 = lean_nat_add(x_1254, x_1257);
lean_dec(x_1254);
if (lean_is_scalar(x_1256)) {
 x_1259 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1259 = x_1256;
}
lean_ctor_set(x_1259, 0, x_1251);
lean_ctor_set(x_1259, 1, x_1252);
lean_ctor_set(x_1259, 2, x_1253);
lean_ctor_set(x_1259, 3, x_1258);
lean_ctor_set(x_1259, 4, x_1255);
x_1260 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1260, 0, x_1259);
lean_ctor_set(x_1260, 1, x_1239);
lean_ctor_set(x_1260, 2, x_1240);
lean_ctor_set(x_1260, 3, x_1241);
lean_ctor_set(x_1260, 4, x_1242);
lean_ctor_set(x_1260, 5, x_1243);
lean_ctor_set(x_1260, 6, x_1244);
lean_ctor_set(x_1260, 7, x_1245);
lean_ctor_set(x_1260, 8, x_1246);
lean_ctor_set(x_1260, 9, x_1247);
lean_ctor_set_uint8(x_1260, sizeof(void*)*10, x_1248);
lean_ctor_set_uint8(x_1260, sizeof(void*)*10 + 1, x_1249);
lean_ctor_set_uint8(x_1260, sizeof(void*)*10 + 2, x_1250);
lean_ctor_set(x_4, 0, x_1260);
x_3 = x_1217;
x_5 = x_1218;
goto _start;
}
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; uint8_t x_1274; uint8_t x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1262 = lean_ctor_get(x_4, 1);
x_1263 = lean_ctor_get(x_4, 2);
lean_inc(x_1263);
lean_inc(x_1262);
lean_dec(x_4);
x_1264 = lean_ctor_get(x_1219, 1);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1219, 2);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1219, 3);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1219, 4);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_1219, 5);
lean_inc(x_1268);
x_1269 = lean_ctor_get(x_1219, 6);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1219, 7);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1219, 8);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1219, 9);
lean_inc(x_1272);
x_1273 = lean_ctor_get_uint8(x_1219, sizeof(void*)*10);
x_1274 = lean_ctor_get_uint8(x_1219, sizeof(void*)*10 + 1);
x_1275 = lean_ctor_get_uint8(x_1219, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 lean_ctor_release(x_1219, 2);
 lean_ctor_release(x_1219, 3);
 lean_ctor_release(x_1219, 4);
 lean_ctor_release(x_1219, 5);
 lean_ctor_release(x_1219, 6);
 lean_ctor_release(x_1219, 7);
 lean_ctor_release(x_1219, 8);
 lean_ctor_release(x_1219, 9);
 x_1276 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1276 = lean_box(0);
}
x_1277 = lean_ctor_get(x_1220, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1220, 1);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1220, 2);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1220, 3);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1220, 4);
lean_inc(x_1281);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 lean_ctor_release(x_1220, 1);
 lean_ctor_release(x_1220, 2);
 lean_ctor_release(x_1220, 3);
 lean_ctor_release(x_1220, 4);
 x_1282 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1282 = lean_box(0);
}
x_1283 = lean_unsigned_to_nat(1u);
x_1284 = lean_nat_add(x_1280, x_1283);
lean_dec(x_1280);
if (lean_is_scalar(x_1282)) {
 x_1285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1285 = x_1282;
}
lean_ctor_set(x_1285, 0, x_1277);
lean_ctor_set(x_1285, 1, x_1278);
lean_ctor_set(x_1285, 2, x_1279);
lean_ctor_set(x_1285, 3, x_1284);
lean_ctor_set(x_1285, 4, x_1281);
if (lean_is_scalar(x_1276)) {
 x_1286 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1286 = x_1276;
}
lean_ctor_set(x_1286, 0, x_1285);
lean_ctor_set(x_1286, 1, x_1264);
lean_ctor_set(x_1286, 2, x_1265);
lean_ctor_set(x_1286, 3, x_1266);
lean_ctor_set(x_1286, 4, x_1267);
lean_ctor_set(x_1286, 5, x_1268);
lean_ctor_set(x_1286, 6, x_1269);
lean_ctor_set(x_1286, 7, x_1270);
lean_ctor_set(x_1286, 8, x_1271);
lean_ctor_set(x_1286, 9, x_1272);
lean_ctor_set_uint8(x_1286, sizeof(void*)*10, x_1273);
lean_ctor_set_uint8(x_1286, sizeof(void*)*10 + 1, x_1274);
lean_ctor_set_uint8(x_1286, sizeof(void*)*10 + 2, x_1275);
x_1287 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1287, 0, x_1286);
lean_ctor_set(x_1287, 1, x_1262);
lean_ctor_set(x_1287, 2, x_1263);
x_3 = x_1217;
x_4 = x_1287;
x_5 = x_1218;
goto _start;
}
}
}
}
else
{
uint8_t x_1302; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1302 = !lean_is_exclusive(x_1208);
if (x_1302 == 0)
{
return x_1208;
}
else
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1303 = lean_ctor_get(x_1208, 0);
x_1304 = lean_ctor_get(x_1208, 1);
lean_inc(x_1304);
lean_inc(x_1303);
lean_dec(x_1208);
x_1305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1305, 0, x_1303);
lean_ctor_set(x_1305, 1, x_1304);
return x_1305;
}
}
}
default: 
{
lean_object* x_1306; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_1306 = l_Lean_Elab_Tactic_unfoldDefinition_x3f(x_1, x_7, x_4, x_8);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
if (lean_obj_tag(x_1307) == 0)
{
uint8_t x_1308; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1308 = !lean_is_exclusive(x_1306);
if (x_1308 == 0)
{
lean_object* x_1309; lean_object* x_1310; 
x_1309 = lean_ctor_get(x_1306, 0);
lean_dec(x_1309);
x_1310 = lean_box(0);
lean_ctor_set(x_1306, 0, x_1310);
return x_1306;
}
else
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; 
x_1311 = lean_ctor_get(x_1306, 1);
lean_inc(x_1311);
lean_dec(x_1306);
x_1312 = lean_box(0);
x_1313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1313, 0, x_1312);
lean_ctor_set(x_1313, 1, x_1311);
return x_1313;
}
}
else
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; uint8_t x_1392; 
x_1314 = lean_ctor_get(x_1306, 1);
lean_inc(x_1314);
lean_dec(x_1306);
x_1315 = lean_ctor_get(x_1307, 0);
lean_inc(x_1315);
lean_dec(x_1307);
x_1388 = lean_ctor_get(x_4, 0);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1388, 0);
lean_inc(x_1389);
lean_dec(x_1388);
x_1390 = lean_ctor_get(x_1389, 3);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1389, 4);
lean_inc(x_1391);
lean_dec(x_1389);
x_1392 = lean_nat_dec_eq(x_1390, x_1391);
lean_dec(x_1391);
lean_dec(x_1390);
if (x_1392 == 0)
{
x_1316 = x_1314;
goto block_1387;
}
else
{
lean_object* x_1393; lean_object* x_1394; 
x_1393 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_1394 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_1393, x_4, x_1314);
if (lean_obj_tag(x_1394) == 0)
{
lean_object* x_1395; 
x_1395 = lean_ctor_get(x_1394, 1);
lean_inc(x_1395);
lean_dec(x_1394);
x_1316 = x_1395;
goto block_1387;
}
else
{
uint8_t x_1396; 
lean_dec(x_1315);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1396 = !lean_is_exclusive(x_1394);
if (x_1396 == 0)
{
return x_1394;
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1397 = lean_ctor_get(x_1394, 0);
x_1398 = lean_ctor_get(x_1394, 1);
lean_inc(x_1398);
lean_inc(x_1397);
lean_dec(x_1394);
x_1399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
return x_1399;
}
}
}
block_1387:
{
lean_object* x_1317; lean_object* x_1318; uint8_t x_1319; 
x_1317 = lean_ctor_get(x_4, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1317, 0);
lean_inc(x_1318);
x_1319 = !lean_is_exclusive(x_4);
if (x_1319 == 0)
{
lean_object* x_1320; uint8_t x_1321; 
x_1320 = lean_ctor_get(x_4, 0);
lean_dec(x_1320);
x_1321 = !lean_is_exclusive(x_1317);
if (x_1321 == 0)
{
lean_object* x_1322; uint8_t x_1323; 
x_1322 = lean_ctor_get(x_1317, 0);
lean_dec(x_1322);
x_1323 = !lean_is_exclusive(x_1318);
if (x_1323 == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
x_1324 = lean_ctor_get(x_1318, 3);
x_1325 = lean_unsigned_to_nat(1u);
x_1326 = lean_nat_add(x_1324, x_1325);
lean_dec(x_1324);
lean_ctor_set(x_1318, 3, x_1326);
x_3 = x_1315;
x_5 = x_1316;
goto _start;
}
else
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1328 = lean_ctor_get(x_1318, 0);
x_1329 = lean_ctor_get(x_1318, 1);
x_1330 = lean_ctor_get(x_1318, 2);
x_1331 = lean_ctor_get(x_1318, 3);
x_1332 = lean_ctor_get(x_1318, 4);
lean_inc(x_1332);
lean_inc(x_1331);
lean_inc(x_1330);
lean_inc(x_1329);
lean_inc(x_1328);
lean_dec(x_1318);
x_1333 = lean_unsigned_to_nat(1u);
x_1334 = lean_nat_add(x_1331, x_1333);
lean_dec(x_1331);
x_1335 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1335, 0, x_1328);
lean_ctor_set(x_1335, 1, x_1329);
lean_ctor_set(x_1335, 2, x_1330);
lean_ctor_set(x_1335, 3, x_1334);
lean_ctor_set(x_1335, 4, x_1332);
lean_ctor_set(x_1317, 0, x_1335);
x_3 = x_1315;
x_5 = x_1316;
goto _start;
}
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; uint8_t x_1346; uint8_t x_1347; uint8_t x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1337 = lean_ctor_get(x_1317, 1);
x_1338 = lean_ctor_get(x_1317, 2);
x_1339 = lean_ctor_get(x_1317, 3);
x_1340 = lean_ctor_get(x_1317, 4);
x_1341 = lean_ctor_get(x_1317, 5);
x_1342 = lean_ctor_get(x_1317, 6);
x_1343 = lean_ctor_get(x_1317, 7);
x_1344 = lean_ctor_get(x_1317, 8);
x_1345 = lean_ctor_get(x_1317, 9);
x_1346 = lean_ctor_get_uint8(x_1317, sizeof(void*)*10);
x_1347 = lean_ctor_get_uint8(x_1317, sizeof(void*)*10 + 1);
x_1348 = lean_ctor_get_uint8(x_1317, sizeof(void*)*10 + 2);
lean_inc(x_1345);
lean_inc(x_1344);
lean_inc(x_1343);
lean_inc(x_1342);
lean_inc(x_1341);
lean_inc(x_1340);
lean_inc(x_1339);
lean_inc(x_1338);
lean_inc(x_1337);
lean_dec(x_1317);
x_1349 = lean_ctor_get(x_1318, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1318, 1);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1318, 2);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1318, 3);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1318, 4);
lean_inc(x_1353);
if (lean_is_exclusive(x_1318)) {
 lean_ctor_release(x_1318, 0);
 lean_ctor_release(x_1318, 1);
 lean_ctor_release(x_1318, 2);
 lean_ctor_release(x_1318, 3);
 lean_ctor_release(x_1318, 4);
 x_1354 = x_1318;
} else {
 lean_dec_ref(x_1318);
 x_1354 = lean_box(0);
}
x_1355 = lean_unsigned_to_nat(1u);
x_1356 = lean_nat_add(x_1352, x_1355);
lean_dec(x_1352);
if (lean_is_scalar(x_1354)) {
 x_1357 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1357 = x_1354;
}
lean_ctor_set(x_1357, 0, x_1349);
lean_ctor_set(x_1357, 1, x_1350);
lean_ctor_set(x_1357, 2, x_1351);
lean_ctor_set(x_1357, 3, x_1356);
lean_ctor_set(x_1357, 4, x_1353);
x_1358 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1358, 0, x_1357);
lean_ctor_set(x_1358, 1, x_1337);
lean_ctor_set(x_1358, 2, x_1338);
lean_ctor_set(x_1358, 3, x_1339);
lean_ctor_set(x_1358, 4, x_1340);
lean_ctor_set(x_1358, 5, x_1341);
lean_ctor_set(x_1358, 6, x_1342);
lean_ctor_set(x_1358, 7, x_1343);
lean_ctor_set(x_1358, 8, x_1344);
lean_ctor_set(x_1358, 9, x_1345);
lean_ctor_set_uint8(x_1358, sizeof(void*)*10, x_1346);
lean_ctor_set_uint8(x_1358, sizeof(void*)*10 + 1, x_1347);
lean_ctor_set_uint8(x_1358, sizeof(void*)*10 + 2, x_1348);
lean_ctor_set(x_4, 0, x_1358);
x_3 = x_1315;
x_5 = x_1316;
goto _start;
}
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; uint8_t x_1371; uint8_t x_1372; uint8_t x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1360 = lean_ctor_get(x_4, 1);
x_1361 = lean_ctor_get(x_4, 2);
lean_inc(x_1361);
lean_inc(x_1360);
lean_dec(x_4);
x_1362 = lean_ctor_get(x_1317, 1);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_1317, 2);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1317, 3);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1317, 4);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1317, 5);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1317, 6);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1317, 7);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1317, 8);
lean_inc(x_1369);
x_1370 = lean_ctor_get(x_1317, 9);
lean_inc(x_1370);
x_1371 = lean_ctor_get_uint8(x_1317, sizeof(void*)*10);
x_1372 = lean_ctor_get_uint8(x_1317, sizeof(void*)*10 + 1);
x_1373 = lean_ctor_get_uint8(x_1317, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 lean_ctor_release(x_1317, 1);
 lean_ctor_release(x_1317, 2);
 lean_ctor_release(x_1317, 3);
 lean_ctor_release(x_1317, 4);
 lean_ctor_release(x_1317, 5);
 lean_ctor_release(x_1317, 6);
 lean_ctor_release(x_1317, 7);
 lean_ctor_release(x_1317, 8);
 lean_ctor_release(x_1317, 9);
 x_1374 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1374 = lean_box(0);
}
x_1375 = lean_ctor_get(x_1318, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1318, 1);
lean_inc(x_1376);
x_1377 = lean_ctor_get(x_1318, 2);
lean_inc(x_1377);
x_1378 = lean_ctor_get(x_1318, 3);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1318, 4);
lean_inc(x_1379);
if (lean_is_exclusive(x_1318)) {
 lean_ctor_release(x_1318, 0);
 lean_ctor_release(x_1318, 1);
 lean_ctor_release(x_1318, 2);
 lean_ctor_release(x_1318, 3);
 lean_ctor_release(x_1318, 4);
 x_1380 = x_1318;
} else {
 lean_dec_ref(x_1318);
 x_1380 = lean_box(0);
}
x_1381 = lean_unsigned_to_nat(1u);
x_1382 = lean_nat_add(x_1378, x_1381);
lean_dec(x_1378);
if (lean_is_scalar(x_1380)) {
 x_1383 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1383 = x_1380;
}
lean_ctor_set(x_1383, 0, x_1375);
lean_ctor_set(x_1383, 1, x_1376);
lean_ctor_set(x_1383, 2, x_1377);
lean_ctor_set(x_1383, 3, x_1382);
lean_ctor_set(x_1383, 4, x_1379);
if (lean_is_scalar(x_1374)) {
 x_1384 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1384 = x_1374;
}
lean_ctor_set(x_1384, 0, x_1383);
lean_ctor_set(x_1384, 1, x_1362);
lean_ctor_set(x_1384, 2, x_1363);
lean_ctor_set(x_1384, 3, x_1364);
lean_ctor_set(x_1384, 4, x_1365);
lean_ctor_set(x_1384, 5, x_1366);
lean_ctor_set(x_1384, 6, x_1367);
lean_ctor_set(x_1384, 7, x_1368);
lean_ctor_set(x_1384, 8, x_1369);
lean_ctor_set(x_1384, 9, x_1370);
lean_ctor_set_uint8(x_1384, sizeof(void*)*10, x_1371);
lean_ctor_set_uint8(x_1384, sizeof(void*)*10 + 1, x_1372);
lean_ctor_set_uint8(x_1384, sizeof(void*)*10 + 2, x_1373);
x_1385 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1385, 0, x_1384);
lean_ctor_set(x_1385, 1, x_1360);
lean_ctor_set(x_1385, 2, x_1361);
x_3 = x_1315;
x_4 = x_1385;
x_5 = x_1316;
goto _start;
}
}
}
}
else
{
uint8_t x_1400; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1400 = !lean_is_exclusive(x_1306);
if (x_1400 == 0)
{
return x_1306;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1306, 0);
x_1402 = lean_ctor_get(x_1306, 1);
lean_inc(x_1402);
lean_inc(x_1401);
lean_dec(x_1306);
x_1403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1403, 0, x_1401);
lean_ctor_set(x_1403, 1, x_1402);
return x_1403;
}
}
}
}
}
else
{
uint8_t x_1404; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1404 = !lean_is_exclusive(x_6);
if (x_1404 == 0)
{
return x_6;
}
else
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1405 = lean_ctor_get(x_6, 0);
x_1406 = lean_ctor_get(x_6, 1);
lean_inc(x_1406);
lean_inc(x_1405);
lean_dec(x_6);
x_1407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1407, 0, x_1405);
lean_ctor_set(x_1407, 1, x_1406);
return x_1407;
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
x_55 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
x_63 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
x_19 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
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
lean_object* l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__1(x_5);
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
x_11 = l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Array_toList___rarg(x_1);
x_5 = l_List_map___main___at_Lean_Elab_Tactic_evalInduction___spec__1(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = 0;
x_22 = lean_box(x_21);
lean_inc(x_16);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_induction___boxed), 7, 5);
lean_closure_set(x_23, 0, x_16);
lean_closure_set(x_23, 1, x_18);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_22);
x_24 = l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1;
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_27 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_29, 0, x_17);
x_30 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_16, x_30, x_3, x_15);
lean_dec(x_16);
return x_31;
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
x_4 = l___private_Init_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
x_5 = l___private_Init_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Tactic_Induction_3__elabMajor), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__2), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Tactic_focusAux___rarg(x_1, x_8, x_2, x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalInduction___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1);
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
