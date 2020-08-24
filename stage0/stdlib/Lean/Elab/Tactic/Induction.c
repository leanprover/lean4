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
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts___boxed(lean_object*);
lean_object* l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__1;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__7;
extern lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4;
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnf___at_Lean_Meta_isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__5;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1___closed__1;
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName___boxed(lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__5;
lean_object* l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_15__isTermRHS___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_7__getAlts(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inferType___at_Lean_Elab_Tactic_elabAsFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
lean_object* l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__7;
lean_object* l___private_Lean_Elab_Tactic_Induction_10__getAltRHS___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_cases___elambda__1___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__5;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
lean_object* l_Lean_Meta_generalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___closed__1;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__3;
uint8_t l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9;
lean_object* l_Lean_getMVarDecl___at_Lean_Elab_Tactic_withMVarContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__3;
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__2;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
lean_object* l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__4;
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__4;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__4;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames___boxed(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__1;
lean_object* l_Lean_Meta_getParamNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Elab_Tactic_evalExact___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_2__getMajor___boxed(lean_object*);
lean_object* l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__8;
lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_8__getAltName___boxed(lean_object*);
extern lean_object* l_List_forM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__5;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__8;
extern lean_object* l_Lean_Parser_Tactic_induction___elambda__1___closed__1;
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
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
lean_object* l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1___closed__1;
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_apply_7(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_16);
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
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1___rarg), 7, 0);
return x_3;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_local_ctx_find_from_user_name(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___closed__3;
x_14 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_LocalDecl_toExpr(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_14 = lean_local_ctx_get_unused_name(x_3, x_13);
x_15 = lean_box(0);
x_16 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Elab_Tactic_elabTerm(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_20 = l_Lean_Elab_Tactic_evalGeneralizeAux(x_2, x_18, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___boxed), 11, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTerm___boxed), 12, 3);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2), 12, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
x_18 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__2___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
lean_object* l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getLCtx___at___private_Lean_Elab_Tactic_Induction_3__elabMajor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_3__elabMajor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Meta_intro1(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_mkFVar(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_14);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Lean_mkFVar(x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_28 = l_Lean_mkFVar(x_25);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___lambda__1), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_box(0);
x_11 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_12; 
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_17 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_inc(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_generalize), 8, 3);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_17);
x_19 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor___closed__1;
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_22, 0, x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_15, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_24;
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_getFVarIds(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_replaceRef(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_ctor_set(x_8, 3, x_18);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed), 2, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_trace___boxed), 11, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2___boxed), 11, 1);
lean_closure_set(x_22, 0, x_12);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_29 = l_Lean_replaceRef(x_1, x_28);
x_30 = l_Lean_replaceRef(x_29, x_28);
lean_dec(x_29);
x_31 = l_Lean_replaceRef(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
lean_inc(x_12);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed), 2, 1);
lean_closure_set(x_33, 0, x_12);
x_34 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___closed__1;
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_trace___boxed), 11, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_33);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2___boxed), 11, 1);
lean_closure_set(x_36, 0, x_12);
x_37 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_32, x_9, x_10);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = l_Array_empty___closed__1;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_Expr_fvarId_x21(x_1);
x_13 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_10, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_14 = lean_array_get_size(x_10);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_3);
lean_dec(x_11);
lean_dec(x_10);
x_18 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_19 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
x_20 = lean_box(0);
x_21 = l_Lean_Meta_throwTacticEx___rarg(x_18, x_2, x_19, x_20, x_4, x_5, x_6, x_7, x_8);
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
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = l_Lean_Expr_fvarId_x21(x_1);
x_29 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_30 = lean_array_get_size(x_26);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
lean_dec(x_26);
x_35 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_36 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__4;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_35, x_2, x_36, x_37, x_4, x_5, x_6, x_7, x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Tactic_Induction_5__getGeneralizingFVarIds(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_20 = 0;
x_21 = lean_box(x_20);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_revert___boxed), 8, 3);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_13);
lean_closure_set(x_22, 2, x_21);
lean_inc(x_18);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed), 8, 2);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_18);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_18, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_10);
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
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
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
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor name '");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkAlt");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_12 = l___private_Lean_Elab_Tactic_Induction_8__getAltName(x_1);
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 3);
lean_inc(x_37);
x_38 = l_Lean_replaceRef(x_1, x_37);
x_39 = l_Lean_replaceRef(x_38, x_37);
lean_dec(x_38);
x_40 = l_Lean_replaceRef(x_39, x_37);
lean_dec(x_37);
lean_dec(x_39);
lean_inc(x_34);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_40);
x_42 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__5;
x_43 = l_Lean_checkTraceOption(x_34, x_42);
lean_dec(x_34);
if (x_43 == 0)
{
lean_dec(x_41);
x_13 = x_11;
goto block_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_12);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_12);
x_45 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_1);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_49 = l_Lean_Elab_Term_logTrace(x_42, x_48, x_5, x_6, x_7, x_8, x_41, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_13 = x_50;
goto block_33;
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_33:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_mkThunk___closed__1;
x_15 = lean_name_eq(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = 0;
x_17 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__1(x_12, x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_System_FilePath_dirName___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_12);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__3;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_19, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_2, x_3, x_4, x_5, x_17, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_10(x_18, lean_box(0), x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_4, x_5);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_6);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed), 11, 3);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_6);
x_24 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__2___boxed), 15, 6);
lean_closure_set(x_24, 0, x_5);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_6);
x_25 = lean_apply_12(x_22, lean_box(0), lean_box(0), x_23, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3;
x_13 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2(x_2, x_12, x_13, x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_1);
return x_16;
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
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_whnf___at_Lean_Meta_isClassExpensive_x3f___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_20 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_6, x_10);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_36 = lean_environment_find(x_26, x_21);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_free_object(x_22);
x_37 = lean_box(0);
x_27 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
if (lean_obj_tag(x_38) == 5)
{
lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
else
{
lean_object* x_40; 
lean_dec(x_38);
lean_free_object(x_22);
x_40 = lean_box(0);
x_27 = x_40;
goto block_35;
}
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_9);
x_29 = l_Lean_indentExpr(x_28);
x_30 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_33 = lean_box(0);
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_1, x_31, x_33, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_53; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_53 = lean_environment_find(x_43, x_21);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_44 = x_54;
goto block_52;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
if (lean_obj_tag(x_55) == 5)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_42);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_55);
x_58 = lean_box(0);
x_44 = x_58;
goto block_52;
}
}
block_52:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_9);
x_46 = l_Lean_indentExpr(x_45);
x_47 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_50 = lean_box(0);
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_49, x_1, x_48, x_50, x_3, x_4, x_5, x_6, x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_51;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_20);
x_59 = lean_box(0);
x_11 = x_59;
goto block_19;
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_13 = l_Lean_indentExpr(x_12);
x_14 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_1, x_15, x_17, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
return x_8;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_8, 0);
x_62 = lean_ctor_get(x_8, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_8);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1), 6, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1), 7, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_14, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1___closed__1;
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_7(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Expr_getAppFn___main(x_21);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_1);
x_27 = l_Lean_Name_append___main(x_26, x_1);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_10, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_27);
x_32 = lean_environment_find(x_31, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = lean_apply_7(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_21, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_9, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_9, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_9, 3);
lean_inc(x_53);
x_54 = lean_nat_dec_eq(x_51, x_52);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_9, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 0);
lean_dec(x_59);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_51, x_60);
lean_dec(x_51);
lean_ctor_set(x_9, 1, x_61);
x_2 = x_49;
x_11 = x_48;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_9);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_51, x_63);
lean_dec(x_51);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_52);
lean_ctor_set(x_65, 3, x_53);
x_2 = x_49;
x_9 = x_65;
x_11 = x_48;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_1);
x_67 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_68 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_41);
if (x_73 == 0)
{
return x_41;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_41, 0);
x_75 = lean_ctor_get(x_41, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_ctor_get(x_38, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 1);
lean_inc(x_78);
lean_dec(x_38);
x_79 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_77);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_79);
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
uint8_t x_88; 
lean_dec(x_34);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_36);
if (x_88 == 0)
{
return x_36;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_36, 0);
x_90 = lean_ctor_get(x_36, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_36);
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
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_96; 
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_96 = l_Lean_Elab_Tactic_saveBacktrackableState(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_170; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_170 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_98);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_box(0);
x_175 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 7, 2);
lean_closure_set(x_175, 0, x_27);
lean_closure_set(x_175, 1, x_174);
x_176 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___closed__1;
x_177 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_177, 0, x_175);
lean_closure_set(x_177, 1, x_176);
x_178 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_178, 0, x_177);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_179 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_173, x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_172);
if (lean_obj_tag(x_179) == 0)
{
lean_dec(x_97);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_179;
}
else
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_99 = x_180;
goto block_169;
}
}
else
{
lean_object* x_181; 
lean_dec(x_27);
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
lean_dec(x_170);
x_99 = x_181;
goto block_169;
}
block_169:
{
lean_object* x_100; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = lean_apply_7(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_105 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_107 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_21, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_110 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_103, x_5, x_6, x_7, x_8, x_9, x_10, x_109);
if (lean_obj_tag(x_110) == 0)
{
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_111; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
x_113 = lean_box(0);
lean_ctor_set(x_110, 0, x_113);
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_118 = lean_ctor_get(x_108, 0);
lean_inc(x_118);
lean_dec(x_108);
x_119 = lean_ctor_get(x_9, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_9, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_9, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_9, 3);
lean_inc(x_122);
x_123 = lean_nat_dec_eq(x_120, x_121);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_9);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_9, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_9, 2);
lean_dec(x_126);
x_127 = lean_ctor_get(x_9, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_9, 0);
lean_dec(x_128);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_add(x_120, x_129);
lean_dec(x_120);
lean_ctor_set(x_9, 1, x_130);
x_2 = x_118;
x_11 = x_117;
goto _start;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_9);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_add(x_120, x_132);
lean_dec(x_120);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_119);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_121);
lean_ctor_set(x_134, 3, x_122);
x_2 = x_118;
x_9 = x_134;
x_11 = x_117;
goto _start;
}
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_1);
x_136 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_137 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_117);
lean_dec(x_4);
lean_dec(x_3);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_108);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_110);
if (x_142 == 0)
{
return x_110;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_110, 0);
x_144 = lean_ctor_get(x_110, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_110);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_ctor_get(x_107, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_107, 1);
lean_inc(x_147);
lean_dec(x_107);
x_148 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_103, x_5, x_6, x_7, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_148, 0);
lean_dec(x_150);
lean_ctor_set_tag(x_148, 1);
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec(x_146);
x_153 = !lean_is_exclusive(x_148);
if (x_153 == 0)
{
return x_148;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_148, 0);
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_148);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_103);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_105);
if (x_157 == 0)
{
return x_105;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_105, 0);
x_159 = lean_ctor_get(x_105, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_105);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_102);
if (x_161 == 0)
{
return x_102;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_102, 0);
x_163 = lean_ctor_get(x_102, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_102);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_100);
if (x_165 == 0)
{
return x_100;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_100, 0);
x_167 = lean_ctor_get(x_100, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_100);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_96);
if (x_182 == 0)
{
return x_96;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_96, 0);
x_184 = lean_ctor_get(x_96, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_96);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_186 = lean_apply_7(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_189 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_191 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_21, x_7, x_8, x_9, x_10, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_194 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_187, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
if (lean_obj_tag(x_194) == 0)
{
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_195; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_194, 0);
lean_dec(x_196);
x_197 = lean_box(0);
lean_ctor_set(x_194, 0, x_197);
return x_194;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_dec(x_194);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_201 = lean_ctor_get(x_194, 1);
lean_inc(x_201);
lean_dec(x_194);
x_202 = lean_ctor_get(x_192, 0);
lean_inc(x_202);
lean_dec(x_192);
x_203 = lean_ctor_get(x_9, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_9, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_9, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_9, 3);
lean_inc(x_206);
x_207 = lean_nat_dec_eq(x_204, x_205);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_9);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_9, 3);
lean_dec(x_209);
x_210 = lean_ctor_get(x_9, 2);
lean_dec(x_210);
x_211 = lean_ctor_get(x_9, 1);
lean_dec(x_211);
x_212 = lean_ctor_get(x_9, 0);
lean_dec(x_212);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_204, x_213);
lean_dec(x_204);
lean_ctor_set(x_9, 1, x_214);
x_2 = x_202;
x_11 = x_201;
goto _start;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_9);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_nat_add(x_204, x_216);
lean_dec(x_204);
x_218 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_218, 0, x_203);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_205);
lean_ctor_set(x_218, 3, x_206);
x_2 = x_202;
x_9 = x_218;
x_11 = x_201;
goto _start;
}
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_1);
x_220 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_221 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_220, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_201);
lean_dec(x_4);
lean_dec(x_3);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
return x_221;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_221);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_192);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_194);
if (x_226 == 0)
{
return x_194;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_194, 0);
x_228 = lean_ctor_get(x_194, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_194);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_230 = lean_ctor_get(x_191, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_191, 1);
lean_inc(x_231);
lean_dec(x_191);
x_232 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_187, x_5, x_6, x_7, x_8, x_9, x_10, x_231);
if (lean_obj_tag(x_232) == 0)
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_232, 0);
lean_dec(x_234);
lean_ctor_set_tag(x_232, 1);
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_230);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
else
{
uint8_t x_237; 
lean_dec(x_230);
x_237 = !lean_is_exclusive(x_232);
if (x_237 == 0)
{
return x_232;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_232, 0);
x_239 = lean_ctor_get(x_232, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_232);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_187);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_189);
if (x_241 == 0)
{
return x_189;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_189, 0);
x_243 = lean_ctor_get(x_189, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_189);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_245 = !lean_is_exclusive(x_186);
if (x_245 == 0)
{
return x_186;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_186, 0);
x_247 = lean_ctor_get(x_186, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_186);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_23);
if (x_249 == 0)
{
return x_23;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_23, 0);
x_251 = lean_ctor_get(x_23, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_23);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_253 = lean_ctor_get(x_20, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_20, 1);
lean_inc(x_254);
lean_dec(x_20);
x_255 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_254);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_255, 0);
lean_dec(x_257);
lean_ctor_set_tag(x_255, 1);
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
lean_dec(x_255);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
else
{
uint8_t x_260; 
lean_dec(x_253);
x_260 = !lean_is_exclusive(x_255);
if (x_260 == 0)
{
return x_255;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_255, 0);
x_262 = lean_ctor_get(x_255, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_255);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_15);
lean_dec(x_13);
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
x_264 = !lean_is_exclusive(x_18);
if (x_264 == 0)
{
return x_18;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_18, 0);
x_266 = lean_ctor_get(x_18, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_18);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_13);
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
x_268 = !lean_is_exclusive(x_14);
if (x_268 == 0)
{
return x_14;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_14, 0);
x_270 = lean_ctor_get(x_14, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_14);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
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
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_inferType___at_Lean_Elab_Tactic_elabAsFVar___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l___private_Lean_Elab_Tactic_Induction_12__getRecFromUsingLoop___main(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_resolveGlobalName(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_21 = x_42;
goto block_28;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_19);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_47 = l_Lean_Elab_Tactic_saveBacktrackableState(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 7, 2);
lean_closure_set(x_55, 0, x_46);
lean_closure_set(x_55, 1, x_54);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_56, 0, x_55);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_53, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_2);
x_62 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_46);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
lean_dec(x_50);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_72 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_74, 0, x_2);
x_75 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_4);
lean_dec(x_3);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
return x_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_47);
if (x_84 == 0)
{
return x_47;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_47, 0);
x_86 = lean_ctor_get(x_47, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_47);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_45);
lean_dec(x_43);
x_88 = lean_box(0);
x_29 = x_88;
goto block_41;
}
}
else
{
lean_object* x_89; 
lean_dec(x_44);
lean_dec(x_43);
x_89 = lean_ctor_get(x_19, 1);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
lean_dec(x_19);
x_90 = lean_box(0);
x_21 = x_90;
goto block_28;
}
else
{
lean_object* x_91; 
lean_dec(x_89);
x_91 = lean_box(0);
x_29 = x_91;
goto block_41;
}
}
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = l_Lean_Elab_Tactic_getRecFromUsing___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_4);
lean_dec(x_3);
return x_27;
}
block_41:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_Lean_Elab_Tactic_getRecFromUsing___closed__6;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_forM___main___at___private_Lean_Parser_Extension_12__ParserAttribute_add___spec__1___closed__5;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_map___main___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_19);
x_36 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
}
else
{
uint8_t x_92; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_15, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_16, 0);
lean_inc(x_94);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_94);
return x_15;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_dec(x_15);
x_96 = lean_ctor_get(x_16, 0);
lean_inc(x_96);
lean_dec(x_16);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_15);
if (x_98 == 0)
{
return x_15;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_15, 0);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_15);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_12);
if (x_102 == 0)
{
return x_12;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_12, 0);
x_104 = lean_ctor_get(x_12, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
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
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for constructor '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_2, x_21, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_21, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
if (x_3 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_13);
lean_dec(x_19);
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_14);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_2);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_array_push(x_16, x_35);
x_37 = lean_box(0);
x_38 = lean_array_push(x_19, x_37);
lean_ctor_set(x_13, 0, x_38);
lean_ctor_set(x_1, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
lean_dec(x_22);
x_41 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_40);
x_42 = l_Array_toList___rarg(x_41);
lean_dec(x_41);
x_43 = lean_array_push(x_16, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = l_Lean_Syntax_getArg(x_40, x_44);
lean_dec(x_40);
x_46 = lean_array_push(x_19, x_45);
lean_ctor_set(x_13, 0, x_46);
lean_ctor_set(x_1, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_12);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_14, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_14, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_25);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_25, 0);
x_53 = l_Lean_Syntax_inhabited;
x_54 = lean_array_get(x_53, x_21, x_52);
x_55 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_54);
x_56 = l_Array_toList___rarg(x_55);
lean_dec(x_55);
x_57 = lean_array_push(x_16, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = l_Lean_Syntax_getArg(x_54, x_58);
x_60 = lean_array_push(x_19, x_59);
x_61 = l_Array_eraseIdx___rarg(x_21, x_52);
lean_dec(x_52);
lean_ctor_set(x_25, 0, x_54);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_61);
lean_ctor_set(x_13, 0, x_60);
lean_ctor_set(x_1, 0, x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_12);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
lean_dec(x_25);
x_64 = l_Lean_Syntax_inhabited;
x_65 = lean_array_get(x_64, x_21, x_63);
x_66 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_65);
x_67 = l_Array_toList___rarg(x_66);
lean_dec(x_66);
x_68 = lean_array_push(x_16, x_67);
x_69 = lean_unsigned_to_nat(3u);
x_70 = l_Lean_Syntax_getArg(x_65, x_69);
x_71 = lean_array_push(x_19, x_70);
x_72 = l_Array_eraseIdx___rarg(x_21, x_63);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_14, 1, x_73);
lean_ctor_set(x_14, 0, x_72);
lean_ctor_set(x_13, 0, x_71);
lean_ctor_set(x_1, 0, x_68);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_12);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_14);
x_75 = lean_ctor_get(x_25, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_76 = x_25;
} else {
 lean_dec_ref(x_25);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Syntax_inhabited;
x_78 = lean_array_get(x_77, x_21, x_75);
x_79 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_78);
x_80 = l_Array_toList___rarg(x_79);
lean_dec(x_79);
x_81 = lean_array_push(x_16, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = l_Lean_Syntax_getArg(x_78, x_82);
x_84 = lean_array_push(x_19, x_83);
x_85 = l_Array_eraseIdx___rarg(x_21, x_75);
lean_dec(x_75);
if (lean_is_scalar(x_76)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_76;
}
lean_ctor_set(x_86, 0, x_78);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_13, 1, x_87);
lean_ctor_set(x_13, 0, x_84);
lean_ctor_set(x_1, 0, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_12);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_14);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_90 = lean_ctor_get(x_14, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_14, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_24, 0);
lean_inc(x_92);
lean_dec(x_24);
x_93 = l_Lean_Syntax_inhabited;
x_94 = lean_array_get(x_93, x_21, x_92);
x_95 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_94);
x_96 = l_Array_toList___rarg(x_95);
lean_dec(x_95);
x_97 = lean_array_push(x_16, x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = l_Lean_Syntax_getArg(x_94, x_98);
lean_dec(x_94);
x_100 = lean_array_push(x_19, x_99);
x_101 = l_Array_eraseIdx___rarg(x_21, x_92);
lean_dec(x_92);
lean_ctor_set(x_14, 0, x_101);
lean_ctor_set(x_13, 0, x_100);
lean_ctor_set(x_1, 0, x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_12);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_14);
x_103 = lean_ctor_get(x_24, 0);
lean_inc(x_103);
lean_dec(x_24);
x_104 = l_Lean_Syntax_inhabited;
x_105 = lean_array_get(x_104, x_21, x_103);
x_106 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_105);
x_107 = l_Array_toList___rarg(x_106);
lean_dec(x_106);
x_108 = lean_array_push(x_16, x_107);
x_109 = lean_unsigned_to_nat(3u);
x_110 = l_Lean_Syntax_getArg(x_105, x_109);
lean_dec(x_105);
x_111 = lean_array_push(x_19, x_110);
x_112 = l_Array_eraseIdx___rarg(x_21, x_103);
lean_dec(x_103);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_22);
lean_ctor_set(x_13, 1, x_113);
lean_ctor_set(x_13, 0, x_111);
lean_ctor_set(x_1, 0, x_108);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_12);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_13, 0);
lean_inc(x_115);
lean_dec(x_13);
x_116 = lean_ctor_get(x_14, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_14, 1);
lean_inc(x_117);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_2, x_116, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_116, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
if (x_3 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_115);
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_14);
x_121 = l_System_FilePath_dirName___closed__1;
x_122 = l_Lean_Name_toStringWithSep___main(x_121, x_2);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3;
x_126 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
x_128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_130 = lean_box(0);
x_131 = lean_array_push(x_16, x_130);
x_132 = lean_box(0);
x_133 = lean_array_push(x_115, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_14);
lean_ctor_set(x_1, 1, x_134);
lean_ctor_set(x_1, 0, x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_12);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_136);
x_138 = l_Array_toList___rarg(x_137);
lean_dec(x_137);
x_139 = lean_array_push(x_16, x_138);
x_140 = lean_unsigned_to_nat(3u);
x_141 = l_Lean_Syntax_getArg(x_136, x_140);
lean_dec(x_136);
x_142 = lean_array_push(x_115, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_14);
lean_ctor_set(x_1, 1, x_143);
lean_ctor_set(x_1, 0, x_139);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_12);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_117);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_145 = x_14;
} else {
 lean_dec_ref(x_14);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_120, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_147 = x_120;
} else {
 lean_dec_ref(x_120);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Syntax_inhabited;
x_149 = lean_array_get(x_148, x_116, x_146);
x_150 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_149);
x_151 = l_Array_toList___rarg(x_150);
lean_dec(x_150);
x_152 = lean_array_push(x_16, x_151);
x_153 = lean_unsigned_to_nat(3u);
x_154 = l_Lean_Syntax_getArg(x_149, x_153);
x_155 = lean_array_push(x_115, x_154);
x_156 = l_Array_eraseIdx___rarg(x_116, x_146);
lean_dec(x_146);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_149);
if (lean_is_scalar(x_145)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_145;
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_1, 1, x_159);
lean_ctor_set(x_1, 0, x_152);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_1);
lean_ctor_set(x_160, 1, x_12);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_161 = x_14;
} else {
 lean_dec_ref(x_14);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_119, 0);
lean_inc(x_162);
lean_dec(x_119);
x_163 = l_Lean_Syntax_inhabited;
x_164 = lean_array_get(x_163, x_116, x_162);
x_165 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_164);
x_166 = l_Array_toList___rarg(x_165);
lean_dec(x_165);
x_167 = lean_array_push(x_16, x_166);
x_168 = lean_unsigned_to_nat(3u);
x_169 = l_Lean_Syntax_getArg(x_164, x_168);
lean_dec(x_164);
x_170 = lean_array_push(x_115, x_169);
x_171 = l_Array_eraseIdx___rarg(x_116, x_162);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_161;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_117);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_1, 1, x_173);
lean_ctor_set(x_1, 0, x_167);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_1);
lean_ctor_set(x_174, 1, x_12);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_1, 0);
lean_inc(x_175);
lean_dec(x_1);
x_176 = lean_ctor_get(x_13, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_177 = x_13;
} else {
 lean_dec_ref(x_13);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_14, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_14, 1);
lean_inc(x_179);
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__1(x_2, x_178, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_178, x_180);
if (lean_obj_tag(x_182) == 0)
{
lean_dec(x_178);
if (lean_obj_tag(x_179) == 0)
{
if (x_3 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_14);
x_183 = l_System_FilePath_dirName___closed__1;
x_184 = l_Lean_Name_toStringWithSep___main(x_183, x_2);
x_185 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_187 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3;
x_188 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
x_189 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
x_190 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_192 = lean_box(0);
x_193 = lean_array_push(x_175, x_192);
x_194 = lean_box(0);
x_195 = lean_array_push(x_176, x_194);
if (lean_is_scalar(x_177)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_177;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_14);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_12);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_199 = lean_ctor_get(x_179, 0);
lean_inc(x_199);
lean_dec(x_179);
x_200 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_199);
x_201 = l_Array_toList___rarg(x_200);
lean_dec(x_200);
x_202 = lean_array_push(x_175, x_201);
x_203 = lean_unsigned_to_nat(3u);
x_204 = l_Lean_Syntax_getArg(x_199, x_203);
lean_dec(x_199);
x_205 = lean_array_push(x_176, x_204);
if (lean_is_scalar(x_177)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_177;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_14);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_12);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_179);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_209 = x_14;
} else {
 lean_dec_ref(x_14);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_182, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_211 = x_182;
} else {
 lean_dec_ref(x_182);
 x_211 = lean_box(0);
}
x_212 = l_Lean_Syntax_inhabited;
x_213 = lean_array_get(x_212, x_178, x_210);
x_214 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_213);
x_215 = l_Array_toList___rarg(x_214);
lean_dec(x_214);
x_216 = lean_array_push(x_175, x_215);
x_217 = lean_unsigned_to_nat(3u);
x_218 = l_Lean_Syntax_getArg(x_213, x_217);
x_219 = lean_array_push(x_176, x_218);
x_220 = l_Array_eraseIdx___rarg(x_178, x_210);
lean_dec(x_210);
if (lean_is_scalar(x_211)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_211;
}
lean_ctor_set(x_221, 0, x_213);
if (lean_is_scalar(x_209)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_209;
}
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
if (lean_is_scalar(x_177)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_177;
}
lean_ctor_set(x_223, 0, x_219);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_216);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_12);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_226 = x_14;
} else {
 lean_dec_ref(x_14);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_181, 0);
lean_inc(x_227);
lean_dec(x_181);
x_228 = l_Lean_Syntax_inhabited;
x_229 = lean_array_get(x_228, x_178, x_227);
x_230 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_229);
x_231 = l_Array_toList___rarg(x_230);
lean_dec(x_230);
x_232 = lean_array_push(x_175, x_231);
x_233 = lean_unsigned_to_nat(3u);
x_234 = l_Lean_Syntax_getArg(x_229, x_233);
lean_dec(x_229);
x_235 = lean_array_push(x_176, x_234);
x_236 = l_Array_eraseIdx___rarg(x_178, x_227);
lean_dec(x_227);
if (lean_is_scalar(x_226)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_226;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_179);
if (lean_is_scalar(x_177)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_177;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_232);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_12);
return x_240;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_1, x_2, x_3, x_6, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_2);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_10(x_16, lean_box(0), x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_box(x_1);
lean_inc(x_6);
x_22 = lean_alloc_closure((void*)(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___boxed), 12, 4);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_18);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_6);
x_23 = lean_box(x_1);
x_24 = lean_alloc_closure((void*)(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__2___boxed), 14, 5);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_19);
lean_closure_set(x_24, 4, x_6);
x_25 = lean_apply_12(x_20, lean_box(0), lean_box(0), x_22, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_getInductiveValFromMajor(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_mkRecFor___closed__1;
x_20 = lean_name_mk_string(x_18, x_19);
x_21 = l_Lean_Syntax_isNone(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_13);
x_22 = lean_ctor_get(x_15, 4);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_22);
lean_inc(x_23);
x_24 = l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(x_23, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3;
x_32 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_22);
x_33 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_3, x_31, x_32, x_30, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_dec(x_44);
x_45 = l_Array_isEmpty___rarg(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_free_object(x_36);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_33);
lean_dec(x_22);
lean_dec(x_20);
x_46 = l_Lean_Syntax_inhabited;
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get(x_46, x_43, x_47);
lean_dec(x_43);
x_49 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_50 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_48, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_20);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_41);
x_56 = l_List_redLength___main___rarg(x_22);
x_57 = lean_mk_empty_array_with_capacity(x_56);
lean_dec(x_56);
x_58 = l_List_toArrayAux___main___rarg(x_22, x_57);
lean_ctor_set(x_36, 1, x_58);
lean_ctor_set(x_36, 0, x_55);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
lean_dec(x_36);
x_60 = l_Array_isEmpty___rarg(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_33);
lean_dec(x_22);
lean_dec(x_20);
x_61 = l_Lean_Syntax_inhabited;
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_array_get(x_61, x_59, x_62);
lean_dec(x_59);
x_64 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_65 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_63, x_64, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_63);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_59);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_40);
lean_ctor_set(x_70, 2, x_41);
x_71 = l_List_redLength___main___rarg(x_22);
x_72 = lean_mk_empty_array_with_capacity(x_71);
lean_dec(x_71);
x_73 = l_List_toArrayAux___main___rarg(x_22, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_33, 0, x_74);
return x_33;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_33, 1);
lean_inc(x_75);
lean_dec(x_33);
x_76 = lean_ctor_get(x_34, 0);
lean_inc(x_76);
lean_dec(x_34);
x_77 = lean_ctor_get(x_35, 0);
lean_inc(x_77);
lean_dec(x_35);
x_78 = lean_ctor_get(x_36, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_79 = x_36;
} else {
 lean_dec_ref(x_36);
 x_79 = lean_box(0);
}
x_80 = l_Array_isEmpty___rarg(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_20);
x_81 = l_Lean_Syntax_inhabited;
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get(x_81, x_78, x_82);
lean_dec(x_78);
x_84 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_85 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_83, x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_75);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_78);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_20);
lean_ctor_set(x_90, 1, x_76);
lean_ctor_set(x_90, 2, x_77);
x_91 = l_List_redLength___main___rarg(x_22);
x_92 = lean_mk_empty_array_with_capacity(x_91);
lean_dec(x_91);
x_93 = l_List_toArrayAux___main___rarg(x_22, x_92);
if (lean_is_scalar(x_79)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_79;
}
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_75);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_33);
if (x_96 == 0)
{
return x_33;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_33, 0);
x_98 = lean_ctor_get(x_33, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_33);
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
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_104 = l_Array_empty___closed__1;
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_20);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_13, 0, x_106);
return x_13;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = lean_ctor_get(x_13, 0);
x_108 = lean_ctor_get(x_13, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_13);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_mkRecFor___closed__1;
x_112 = lean_name_mk_string(x_110, x_111);
x_113 = l_Lean_Syntax_isNone(x_2);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_107, 4);
lean_inc(x_114);
lean_dec(x_107);
x_115 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_114);
lean_inc(x_115);
x_116 = l___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames(x_115, x_114, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_108);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Array_empty___closed__1;
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3;
x_124 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_114);
x_125 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_3, x_123, x_124, x_122, x_114, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_117);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
x_135 = l_Array_isEmpty___rarg(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_114);
lean_dec(x_112);
x_136 = l_Lean_Syntax_inhabited;
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_array_get(x_136, x_133, x_137);
lean_dec(x_133);
x_139 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_140 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_138, x_139, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_129);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
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
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_133);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_112);
lean_ctor_set(x_145, 1, x_131);
lean_ctor_set(x_145, 2, x_132);
x_146 = l_List_redLength___main___rarg(x_114);
x_147 = lean_mk_empty_array_with_capacity(x_146);
lean_dec(x_146);
x_148 = l_List_toArrayAux___main___rarg(x_114, x_147);
if (lean_is_scalar(x_134)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_134;
}
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_130)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_130;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_129);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_151 = lean_ctor_get(x_125, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_125, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_153 = x_125;
} else {
 lean_dec_ref(x_125);
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
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_155 = lean_ctor_get(x_116, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_116, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_157 = x_116;
} else {
 lean_dec_ref(x_116);
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
lean_dec(x_107);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_159 = l_Array_empty___closed__1;
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_112);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_108);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_13);
if (x_163 == 0)
{
return x_13;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_13, 0);
x_165 = lean_ctor_get(x_13, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_13);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_19 = lean_nat_sub(x_3, x_18);
x_20 = lean_nat_sub(x_19, x_17);
lean_dec(x_19);
x_21 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Name_inhabited;
x_24 = lean_array_get(x_23, x_2, x_20);
lean_dec(x_20);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
x_35 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_24, x_33, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_33, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_18);
x_37 = l_System_FilePath_dirName___closed__1;
x_38 = l_Lean_Name_toStringWithSep___main(x_37, x_24);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_24);
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
x_51 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_50);
x_52 = l_Array_toList___rarg(x_51);
lean_dec(x_51);
x_53 = lean_array_push(x_28, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = l_Lean_Syntax_getArg(x_50, x_54);
lean_dec(x_50);
x_56 = lean_array_push(x_31, x_55);
lean_ctor_set(x_25, 0, x_56);
lean_ctor_set(x_5, 0, x_53);
x_4 = x_18;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_34);
lean_dec(x_24);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_26, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_26, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = l_Lean_Syntax_inhabited;
x_64 = lean_array_get(x_63, x_33, x_62);
x_65 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_64);
x_66 = l_Array_toList___rarg(x_65);
lean_dec(x_65);
x_67 = lean_array_push(x_28, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = l_Lean_Syntax_getArg(x_64, x_68);
x_70 = lean_array_push(x_31, x_69);
x_71 = l_Array_eraseIdx___rarg(x_33, x_62);
lean_dec(x_62);
lean_ctor_set(x_36, 0, x_64);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_71);
lean_ctor_set(x_25, 0, x_70);
lean_ctor_set(x_5, 0, x_67);
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_36, 0);
lean_inc(x_73);
lean_dec(x_36);
x_74 = l_Lean_Syntax_inhabited;
x_75 = lean_array_get(x_74, x_33, x_73);
x_76 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_75);
x_77 = l_Array_toList___rarg(x_76);
lean_dec(x_76);
x_78 = lean_array_push(x_28, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = l_Lean_Syntax_getArg(x_75, x_79);
x_81 = lean_array_push(x_31, x_80);
x_82 = l_Array_eraseIdx___rarg(x_33, x_73);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_26, 1, x_83);
lean_ctor_set(x_26, 0, x_82);
lean_ctor_set(x_25, 0, x_81);
lean_ctor_set(x_5, 0, x_78);
x_4 = x_18;
goto _start;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_26);
x_85 = lean_ctor_get(x_36, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_86 = x_36;
} else {
 lean_dec_ref(x_36);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Syntax_inhabited;
x_88 = lean_array_get(x_87, x_33, x_85);
x_89 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_88);
x_90 = l_Array_toList___rarg(x_89);
lean_dec(x_89);
x_91 = lean_array_push(x_28, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = l_Lean_Syntax_getArg(x_88, x_92);
x_94 = lean_array_push(x_31, x_93);
x_95 = l_Array_eraseIdx___rarg(x_33, x_85);
lean_dec(x_85);
if (lean_is_scalar(x_86)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_86;
}
lean_ctor_set(x_96, 0, x_88);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_25, 1, x_97);
lean_ctor_set(x_25, 0, x_94);
lean_ctor_set(x_5, 0, x_91);
x_4 = x_18;
goto _start;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_24);
x_99 = !lean_is_exclusive(x_26);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_100 = lean_ctor_get(x_26, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_26, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_35, 0);
lean_inc(x_102);
lean_dec(x_35);
x_103 = l_Lean_Syntax_inhabited;
x_104 = lean_array_get(x_103, x_33, x_102);
x_105 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_104);
x_106 = l_Array_toList___rarg(x_105);
lean_dec(x_105);
x_107 = lean_array_push(x_28, x_106);
x_108 = lean_unsigned_to_nat(3u);
x_109 = l_Lean_Syntax_getArg(x_104, x_108);
lean_dec(x_104);
x_110 = lean_array_push(x_31, x_109);
x_111 = l_Array_eraseIdx___rarg(x_33, x_102);
lean_dec(x_102);
lean_ctor_set(x_26, 0, x_111);
lean_ctor_set(x_25, 0, x_110);
lean_ctor_set(x_5, 0, x_107);
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_26);
x_113 = lean_ctor_get(x_35, 0);
lean_inc(x_113);
lean_dec(x_35);
x_114 = l_Lean_Syntax_inhabited;
x_115 = lean_array_get(x_114, x_33, x_113);
x_116 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_115);
x_117 = l_Array_toList___rarg(x_116);
lean_dec(x_116);
x_118 = lean_array_push(x_28, x_117);
x_119 = lean_unsigned_to_nat(3u);
x_120 = l_Lean_Syntax_getArg(x_115, x_119);
lean_dec(x_115);
x_121 = lean_array_push(x_31, x_120);
x_122 = l_Array_eraseIdx___rarg(x_33, x_113);
lean_dec(x_113);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_34);
lean_ctor_set(x_25, 1, x_123);
lean_ctor_set(x_25, 0, x_121);
lean_ctor_set(x_5, 0, x_118);
x_4 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_25, 0);
lean_inc(x_125);
lean_dec(x_25);
x_126 = lean_ctor_get(x_26, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_26, 1);
lean_inc(x_127);
x_128 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_24, x_126, x_15);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_126, x_15);
if (lean_obj_tag(x_129) == 0)
{
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_125);
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_18);
x_130 = l_System_FilePath_dirName___closed__1;
x_131 = l_Lean_Name_toStringWithSep___main(x_130, x_24);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_137, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
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
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_24);
x_143 = lean_ctor_get(x_127, 0);
lean_inc(x_143);
lean_dec(x_127);
x_144 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_143);
x_145 = l_Array_toList___rarg(x_144);
lean_dec(x_144);
x_146 = lean_array_push(x_28, x_145);
x_147 = lean_unsigned_to_nat(3u);
x_148 = l_Lean_Syntax_getArg(x_143, x_147);
lean_dec(x_143);
x_149 = lean_array_push(x_125, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_26);
lean_ctor_set(x_5, 1, x_150);
lean_ctor_set(x_5, 0, x_146);
x_4 = x_18;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_127);
lean_dec(x_24);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_152 = x_26;
} else {
 lean_dec_ref(x_26);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_129, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_154 = x_129;
} else {
 lean_dec_ref(x_129);
 x_154 = lean_box(0);
}
x_155 = l_Lean_Syntax_inhabited;
x_156 = lean_array_get(x_155, x_126, x_153);
x_157 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_156);
x_158 = l_Array_toList___rarg(x_157);
lean_dec(x_157);
x_159 = lean_array_push(x_28, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = l_Lean_Syntax_getArg(x_156, x_160);
x_162 = lean_array_push(x_125, x_161);
x_163 = l_Array_eraseIdx___rarg(x_126, x_153);
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
lean_ctor_set(x_5, 1, x_166);
lean_ctor_set(x_5, 0, x_159);
x_4 = x_18;
goto _start;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_24);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_168 = x_26;
} else {
 lean_dec_ref(x_26);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_128, 0);
lean_inc(x_169);
lean_dec(x_128);
x_170 = l_Lean_Syntax_inhabited;
x_171 = lean_array_get(x_170, x_126, x_169);
x_172 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_171);
x_173 = l_Array_toList___rarg(x_172);
lean_dec(x_172);
x_174 = lean_array_push(x_28, x_173);
x_175 = lean_unsigned_to_nat(3u);
x_176 = l_Lean_Syntax_getArg(x_171, x_175);
lean_dec(x_171);
x_177 = lean_array_push(x_125, x_176);
x_178 = l_Array_eraseIdx___rarg(x_126, x_169);
lean_dec(x_169);
if (lean_is_scalar(x_168)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_168;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_127);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_5, 1, x_180);
lean_ctor_set(x_5, 0, x_174);
x_4 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_5, 0);
lean_inc(x_182);
lean_dec(x_5);
x_183 = lean_ctor_get(x_25, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_184 = x_25;
} else {
 lean_dec_ref(x_25);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_26, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_26, 1);
lean_inc(x_186);
x_187 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__1(x_24, x_185, x_15);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__2(x_185, x_15);
if (lean_obj_tag(x_188) == 0)
{
lean_dec(x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_26);
lean_dec(x_18);
x_189 = l_System_FilePath_dirName___closed__1;
x_190 = l_Lean_Name_toStringWithSep___main(x_189, x_24);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___closed__3;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6;
x_196 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_196, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_24);
x_202 = lean_ctor_get(x_186, 0);
lean_inc(x_202);
lean_dec(x_186);
x_203 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_202);
x_204 = l_Array_toList___rarg(x_203);
lean_dec(x_203);
x_205 = lean_array_push(x_182, x_204);
x_206 = lean_unsigned_to_nat(3u);
x_207 = l_Lean_Syntax_getArg(x_202, x_206);
lean_dec(x_202);
x_208 = lean_array_push(x_183, x_207);
if (lean_is_scalar(x_184)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_184;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_26);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_205);
lean_ctor_set(x_210, 1, x_209);
x_4 = x_18;
x_5 = x_210;
goto _start;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_186);
lean_dec(x_24);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_212 = x_26;
} else {
 lean_dec_ref(x_26);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_188, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_214 = x_188;
} else {
 lean_dec_ref(x_188);
 x_214 = lean_box(0);
}
x_215 = l_Lean_Syntax_inhabited;
x_216 = lean_array_get(x_215, x_185, x_213);
x_217 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_216);
x_218 = l_Array_toList___rarg(x_217);
lean_dec(x_217);
x_219 = lean_array_push(x_182, x_218);
x_220 = lean_unsigned_to_nat(3u);
x_221 = l_Lean_Syntax_getArg(x_216, x_220);
x_222 = lean_array_push(x_183, x_221);
x_223 = l_Array_eraseIdx___rarg(x_185, x_213);
lean_dec(x_213);
if (lean_is_scalar(x_214)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_214;
}
lean_ctor_set(x_224, 0, x_216);
if (lean_is_scalar(x_212)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_212;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_184)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_184;
}
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_226);
x_4 = x_18;
x_5 = x_227;
goto _start;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_24);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_229 = x_26;
} else {
 lean_dec_ref(x_26);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_187, 0);
lean_inc(x_230);
lean_dec(x_187);
x_231 = l_Lean_Syntax_inhabited;
x_232 = lean_array_get(x_231, x_185, x_230);
x_233 = l___private_Lean_Elab_Tactic_Induction_9__getAltVarNames(x_232);
x_234 = l_Array_toList___rarg(x_233);
lean_dec(x_233);
x_235 = lean_array_push(x_182, x_234);
x_236 = lean_unsigned_to_nat(3u);
x_237 = l_Lean_Syntax_getArg(x_232, x_236);
lean_dec(x_232);
x_238 = lean_array_push(x_183, x_237);
x_239 = l_Array_eraseIdx___rarg(x_185, x_230);
lean_dec(x_230);
if (lean_is_scalar(x_229)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_229;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_186);
if (lean_is_scalar(x_184)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_184;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_235);
lean_ctor_set(x_242, 1, x_241);
x_4 = x_18;
x_5 = x_242;
goto _start;
}
}
}
}
else
{
lean_object* x_244; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_5);
lean_ctor_set(x_244, 1, x_14);
return x_244;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(4u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_13);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 3);
x_19 = l_Lean_replaceRef(x_1, x_18);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_9, 3, x_21);
if (x_16 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getIdAt(x_13, x_22);
lean_dec(x_13);
x_24 = l_Lean_Name_eraseMacroScopes(x_23);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = l_Lean_Syntax_isNone(x_15);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_25);
x_31 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_15);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
lean_inc(x_29);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 6, 1);
lean_closure_set(x_38, 0, x_29);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_39, 0, x_38);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_36, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(0);
lean_ctor_set(x_33, 1, x_43);
lean_ctor_set(x_33, 0, x_31);
x_44 = l_Array_empty___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_get_size(x_41);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_47);
x_48 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_27, x_41, x_47, x_47, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_27);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_Array_isEmpty___rarg(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_56);
lean_dec(x_55);
lean_free_object(x_48);
lean_dec(x_29);
x_59 = l_Lean_Syntax_inhabited;
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get(x_59, x_57, x_60);
lean_dec(x_57);
x_62 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_63 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_61, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_61);
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
else
{
lean_object* x_68; 
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_29);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_48, 0, x_68);
return x_48;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
lean_dec(x_48);
x_70 = lean_ctor_get(x_49, 0);
lean_inc(x_70);
lean_dec(x_49);
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
lean_dec(x_50);
x_72 = lean_ctor_get(x_51, 0);
lean_inc(x_72);
lean_dec(x_51);
x_73 = l_Array_isEmpty___rarg(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_29);
x_74 = l_Lean_Syntax_inhabited;
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_get(x_74, x_72, x_75);
lean_dec(x_72);
x_77 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_78 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_76, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
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
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_72);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_29);
lean_ctor_set(x_83, 1, x_70);
lean_ctor_set(x_83, 2, x_71);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_69);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_48);
if (x_85 == 0)
{
return x_48;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_48, 0);
x_87 = lean_ctor_get(x_48, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_48);
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
lean_free_object(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_40);
if (x_89 == 0)
{
return x_40;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_40, 0);
x_91 = lean_ctor_get(x_40, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_40);
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
x_93 = lean_ctor_get(x_33, 0);
lean_inc(x_93);
lean_dec(x_33);
lean_inc(x_29);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 6, 1);
lean_closure_set(x_94, 0, x_29);
x_95 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_95, 0, x_94);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_96 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_93, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
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
lean_ctor_set(x_100, 0, x_31);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Array_empty___closed__1;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_get_size(x_97);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_104);
x_105 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_27, x_97, x_104, x_104, x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_98);
lean_dec(x_104);
lean_dec(x_97);
lean_dec(x_27);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
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
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_29);
x_115 = l_Lean_Syntax_inhabited;
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_array_get(x_115, x_113, x_116);
lean_dec(x_113);
x_118 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_119 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_117, x_118, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_117);
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
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_29);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_124, 2, x_112);
if (lean_is_scalar(x_110)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_110;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_109);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_105, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_128 = x_105;
} else {
 lean_dec_ref(x_105);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = lean_ctor_get(x_96, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_96, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_132 = x_96;
} else {
 lean_dec_ref(x_96);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = !lean_is_exclusive(x_32);
if (x_134 == 0)
{
return x_32;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_32, 0);
x_136 = lean_ctor_get(x_32, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_32);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = l_Array_empty___closed__1;
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_29);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_25, 0, x_139);
return x_25;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = lean_ctor_get(x_25, 0);
x_141 = lean_ctor_get(x_25, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_25);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = l_Lean_Syntax_isNone(x_15);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_15);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_145 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_141);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
lean_inc(x_142);
x_150 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 6, 1);
lean_closure_set(x_150, 0, x_142);
x_151 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_151, 0, x_150);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_152 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_148, x_151, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_149;
}
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Array_empty___closed__1;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_array_get_size(x_153);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_160);
x_161 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_140, x_153, x_160, x_160, x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_154);
lean_dec(x_160);
lean_dec(x_153);
lean_dec(x_140);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_166 = x_161;
} else {
 lean_dec_ref(x_161);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
lean_dec(x_162);
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
lean_dec(x_164);
x_170 = l_Array_isEmpty___rarg(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_142);
x_171 = l_Lean_Syntax_inhabited;
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_array_get(x_171, x_169, x_172);
lean_dec(x_169);
x_174 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_175 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_173, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_165);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_173);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_169);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_142);
lean_ctor_set(x_180, 1, x_167);
lean_ctor_set(x_180, 2, x_168);
if (lean_is_scalar(x_166)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_166;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_165);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_142);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_182 = lean_ctor_get(x_161, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_161, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_184 = x_161;
} else {
 lean_dec_ref(x_161);
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
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_149);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_186 = lean_ctor_get(x_152, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_152, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_188 = x_152;
} else {
 lean_dec_ref(x_152);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_145, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_145, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_192 = x_145;
} else {
 lean_dec_ref(x_145);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = l_Array_empty___closed__1;
x_195 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_195, 0, x_142);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_141);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = !lean_is_exclusive(x_25);
if (x_197 == 0)
{
return x_25;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_25, 0);
x_199 = lean_ctor_get(x_25, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_25);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
uint8_t x_201; lean_object* x_202; 
lean_dec(x_13);
x_201 = 0;
x_202 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_15, x_201, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec(x_204);
lean_ctor_set(x_202, 0, x_205);
return x_202;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_202, 0);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_202);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_202);
if (x_210 == 0)
{
return x_202;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_202, 0);
x_212 = lean_ctor_get(x_202, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_202);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_214 = lean_ctor_get(x_9, 0);
x_215 = lean_ctor_get(x_9, 1);
x_216 = lean_ctor_get(x_9, 2);
x_217 = lean_ctor_get(x_9, 3);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_9);
x_218 = l_Lean_replaceRef(x_1, x_217);
x_219 = l_Lean_replaceRef(x_218, x_217);
lean_dec(x_218);
x_220 = l_Lean_replaceRef(x_219, x_217);
lean_dec(x_217);
lean_dec(x_219);
x_221 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_221, 0, x_214);
lean_ctor_set(x_221, 1, x_215);
lean_ctor_set(x_221, 2, x_216);
lean_ctor_set(x_221, 3, x_220);
if (x_16 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_unsigned_to_nat(1u);
x_223 = l_Lean_Syntax_getIdAt(x_13, x_222);
lean_dec(x_13);
x_224 = l_Lean_Name_eraseMacroScopes(x_223);
lean_dec(x_223);
lean_inc(x_10);
lean_inc(x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_225 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_224, x_3, x_4, x_5, x_6, x_7, x_8, x_221, x_10, x_11);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_226, 0);
lean_inc(x_229);
x_230 = l_Lean_Syntax_isNone(x_15);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_228);
x_231 = l___private_Lean_Elab_Tactic_Induction_7__getAlts(x_15);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_232 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_221, x_10, x_227);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
lean_inc(x_229);
x_237 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames), 6, 1);
lean_closure_set(x_237, 0, x_229);
x_238 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_238, 0, x_237);
lean_inc(x_10);
lean_inc(x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_239 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_235, x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_221, x_10, x_234);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_box(0);
if (lean_is_scalar(x_236)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_236;
}
lean_ctor_set(x_243, 0, x_231);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Array_empty___closed__1;
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_array_get_size(x_240);
lean_inc(x_10);
lean_inc(x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_247);
x_248 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_226, x_240, x_247, x_247, x_246, x_3, x_4, x_5, x_6, x_7, x_8, x_221, x_10, x_241);
lean_dec(x_247);
lean_dec(x_240);
lean_dec(x_226);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_248, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_253 = x_248;
} else {
 lean_dec_ref(x_248);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_249, 0);
lean_inc(x_254);
lean_dec(x_249);
x_255 = lean_ctor_get(x_250, 0);
lean_inc(x_255);
lean_dec(x_250);
x_256 = lean_ctor_get(x_251, 0);
lean_inc(x_256);
lean_dec(x_251);
x_257 = l_Array_isEmpty___rarg(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_229);
x_258 = l_Lean_Syntax_inhabited;
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_array_get(x_258, x_256, x_259);
lean_dec(x_256);
x_261 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___closed__3;
x_262 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_260, x_261, x_3, x_4, x_5, x_6, x_7, x_8, x_221, x_10, x_252);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_260);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_256);
lean_dec(x_221);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_267 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_267, 0, x_229);
lean_ctor_set(x_267, 1, x_254);
lean_ctor_set(x_267, 2, x_255);
if (lean_is_scalar(x_253)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_253;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_252);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_229);
lean_dec(x_221);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_269 = lean_ctor_get(x_248, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_248, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_271 = x_248;
} else {
 lean_dec_ref(x_248);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_236);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_273 = lean_ctor_get(x_239, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_239, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_275 = x_239;
} else {
 lean_dec_ref(x_239);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_277 = lean_ctor_get(x_232, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_232, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_279 = x_232;
} else {
 lean_dec_ref(x_232);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_281 = l_Array_empty___closed__1;
x_282 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_282, 0, x_229);
lean_ctor_set(x_282, 1, x_281);
lean_ctor_set(x_282, 2, x_281);
if (lean_is_scalar(x_228)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_228;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_227);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_221);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = lean_ctor_get(x_225, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_225, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_286 = x_225;
} else {
 lean_dec_ref(x_225);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
uint8_t x_288; lean_object* x_289; 
lean_dec(x_13);
x_288 = 0;
x_289 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_2, x_15, x_288, x_3, x_4, x_5, x_6, x_7, x_8, x_221, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
x_293 = lean_ctor_get(x_290, 0);
lean_inc(x_293);
lean_dec(x_290);
if (lean_is_scalar(x_292)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_292;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_289, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_289, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_297 = x_289;
} else {
 lean_dec_ref(x_289);
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_14__getRecInfo___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_14__getRecInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_replaceRef(x_1, x_4);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 3);
x_17 = l_Lean_replaceRef(x_14, x_16);
lean_dec(x_14);
x_18 = l_Lean_replaceRef(x_17, x_16);
lean_dec(x_16);
lean_dec(x_17);
lean_ctor_set(x_11, 3, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_19 = l_Lean_getMVarDecl___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
x_25 = l_Lean_Elab_Tactic_elabTerm(x_1, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Elab_Term_ensureHasType(x_23, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_31 = l_Lean_assignExprMVar___at_Lean_Elab_Tactic_evalExact___spec__1(x_2, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_33 = l_Lean_Elab_Tactic_collectMVars(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
lean_dec(x_20);
x_37 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_inc(x_34);
x_38 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_36, x_37, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_List_append___rarg(x_3, x_34);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_List_append___rarg(x_3, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_34);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
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
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
else
{
uint8_t x_53; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
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
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_28);
if (x_57 == 0)
{
return x_28;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_28, 0);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_28);
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
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_25);
if (x_61 == 0)
{
return x_25;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_25, 0);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_25);
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
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_11, 0);
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get(x_11, 2);
x_72 = lean_ctor_get(x_11, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_11);
x_73 = l_Lean_replaceRef(x_14, x_72);
lean_dec(x_14);
x_74 = l_Lean_replaceRef(x_73, x_72);
lean_dec(x_72);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_74);
lean_inc(x_12);
lean_inc(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_76 = l_Lean_getMVarDecl___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_75, x_12, x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 2);
lean_inc(x_79);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = 0;
lean_inc(x_12);
lean_inc(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_80);
x_82 = l_Lean_Elab_Tactic_elabTerm(x_1, x_80, x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_75, x_12, x_78);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_12);
lean_inc(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_85 = l_Lean_Elab_Term_ensureHasType(x_80, x_83, x_7, x_8, x_9, x_10, x_75, x_12, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_12);
lean_inc(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_86);
x_88 = l_Lean_assignExprMVar___at_Lean_Elab_Tactic_evalExact___spec__1(x_2, x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_75, x_12, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_12);
lean_inc(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_90 = l_Lean_Elab_Tactic_collectMVars(x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_75, x_12, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_77, 0);
lean_inc(x_93);
lean_dec(x_77);
x_94 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars___lambda__1___closed__1;
lean_inc(x_91);
x_95 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_93, x_94, x_91, x_5, x_6, x_7, x_8, x_9, x_10, x_75, x_12, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_List_append___rarg(x_3, x_91);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_91);
lean_dec(x_3);
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_104 = lean_ctor_get(x_90, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_90, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_106 = x_90;
} else {
 lean_dec_ref(x_90);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_108 = lean_ctor_get(x_88, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_88, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_110 = x_88;
} else {
 lean_dec_ref(x_88);
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
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_85, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_85, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_114 = x_85;
} else {
 lean_dec_ref(x_85);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_82, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_82, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_118 = x_82;
} else {
 lean_dec_ref(x_82);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_76, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_122 = x_76;
} else {
 lean_dec_ref(x_76);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_19 = lean_nat_sub(x_3, x_18);
x_20 = lean_nat_sub(x_19, x_17);
lean_dec(x_19);
x_21 = l_Lean_Meta_InductionSubgoal_inhabited;
x_22 = lean_array_get(x_21, x_2, x_20);
x_23 = l_Lean_Syntax_inhabited;
x_24 = lean_array_get(x_23, x_1, x_20);
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_24);
x_26 = l___private_Lean_Elab_Tactic_Induction_15__isTermRHS(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_setGoals(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Lean_Elab_Tactic_evalTactic___main(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Elab_Tactic_done(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_4 = x_18;
x_14 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_25);
x_44 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__2___boxed), 13, 3);
lean_closure_set(x_44, 0, x_24);
lean_closure_set(x_44, 1, x_25);
lean_closure_set(x_44, 2, x_5);
x_45 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___closed__1;
x_46 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_46, 0, x_45);
lean_closure_set(x_46, 1, x_44);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_25, x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_4 = x_18;
x_5 = x_48;
x_14 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
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
lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_14);
return x_55;
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
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Array_isEmpty___rarg(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_26; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_array_get_size(x_2);
x_26 = lean_nat_dec_eq(x_13, x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_27 = l_Nat_repr(x_14);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__6;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_Tactic_Induction_16__processResult___closed__9;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Nat_repr(x_13);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_dec(x_13);
x_15 = x_11;
goto block_25;
}
block_25:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_17 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(x_1, x_2, x_14, x_14, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Tactic_setGoals(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Array_toList___rarg(x_2);
x_48 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__2(x_47);
x_49 = l_Lean_Elab_Tactic_setGoals(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_16__processResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_15 = l___private_Lean_Elab_Tactic_Induction_6__generalizeVars(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_17 = l___private_Lean_Elab_Tactic_Induction_14__getRecInfo(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_fvarId_x21(x_13);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
x_27 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1___closed__1;
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = lean_apply_7(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Meta_induction(x_23, x_24, x_25, x_26, x_35, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_18, 2);
lean_inc(x_41);
lean_dec(x_18);
x_42 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_41, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_37);
lean_dec(x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_37);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_47);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
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
uint8_t x_58; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_29);
if (x_62 == 0)
{
return x_29;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_29, 0);
x_64 = lean_ctor_get(x_29, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_29);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_20);
if (x_66 == 0)
{
return x_20;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_20, 0);
x_68 = lean_ctor_get(x_20, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_20);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_17);
if (x_70 == 0)
{
return x_17;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_17, 0);
x_72 = lean_ctor_get(x_17, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_17);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_15);
if (x_74 == 0)
{
return x_15;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_15, 0);
x_76 = lean_ctor_get(x_15, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_15);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
return x_12;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
x_12 = l___private_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 11, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed), 11, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_focusAux___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalInduction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction), 10, 0);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_4, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_array_fget(x_1, x_4);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_array_fget(x_3, x_5);
x_30 = l_Lean_Syntax_isMissing(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_Lean_Name_inhabited;
x_32 = lean_array_get(x_31, x_2, x_5);
x_33 = lean_array_get_size(x_1);
x_34 = lean_nat_dec_lt(x_4, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__9;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_array_fget(x_1, x_4);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_name_eq(x_32, x_42);
lean_dec(x_32);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_4);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_42);
x_45 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__3;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___closed__6;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_4, x_50);
lean_dec(x_4);
x_52 = lean_nat_add(x_5, x_50);
lean_dec(x_5);
x_4 = x_51;
x_5 = x_52;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_5, x_54);
lean_dec(x_5);
x_5 = x_55;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Array_isEmpty___rarg(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Tactic_Induction_17__checkCasesResultAux___main(x_1, x_2, x_3, x_14, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
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
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Tactic_Induction_4__generalizeMajor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_22 = l___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault(x_13, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_fvarId_x21(x_13);
lean_dec(x_13);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1___closed__1;
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = lean_apply_7(x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Lean_setTraceState___at___private_Lean_Elab_Term_4__liftMetaMFinalizer___spec__1(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_Cases_cases(x_18, x_27, x_28, x_37, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_25, 2);
lean_inc(x_43);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l___private_Lean_Elab_Tactic_Induction_18__checkCasesResult(x_39, x_26, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_26);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = x_39;
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(x_47, x_46);
x_49 = x_48;
x_50 = l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(x_43, x_47, x_47);
x_51 = l___private_Lean_Elab_Tactic_Induction_16__processResult(x_50, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_49);
lean_dec(x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_39);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
return x_41;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_3);
x_60 = lean_ctor_get(x_38, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_dec(x_38);
x_62 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_60);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_35);
if (x_71 == 0)
{
return x_35;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_35, 0);
x_73 = lean_ctor_get(x_35, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_35);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_31);
if (x_75 == 0)
{
return x_31;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_31, 0);
x_77 = lean_ctor_get(x_31, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_31);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_22, 0);
x_81 = lean_ctor_get(x_22, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_22);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
return x_15;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_12);
if (x_87 == 0)
{
return x_12;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_12, 0);
x_89 = lean_ctor_get(x_12, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_12);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l___private_Lean_Elab_Tactic_Induction_1__getAuxHypothesisName(x_1);
x_12 = l___private_Lean_Elab_Tactic_Induction_2__getMajor(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_3__elabMajor), 11, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__1___boxed), 11, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg), 11, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_focusAux___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalCases___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases), 10, 0);
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
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__4 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__4();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__4);
l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__5 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__5();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Tactic_Induction_11__checkAltCtorNames___spec__2___lambda__1___closed__5);
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
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__2);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__3);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__4 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__4);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__5 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__5();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__5);
l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6 = _init_l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_Tactic_Induction_13__getRecInfoDefault___spec__3___lambda__1___closed__6);
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
l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___closed__1 = _init_l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Elab_Tactic_Induction_16__processResult___spec__1___closed__1);
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
