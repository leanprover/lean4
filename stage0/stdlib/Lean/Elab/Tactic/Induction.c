// Lean compiler output
// Module: Lean.Elab.Tactic.Induction
// Imports: Init Lean.Meta.RecursorInfo Lean.Meta.CollectMVars Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Cases Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Generalize
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
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2;
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4;
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__1;
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__1;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__3(lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__1;
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__5___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__2;
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars_match__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__6;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(lean_object*);
lean_object* l_Lean_Meta_getParamNamesImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___closed__1;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_RecInfo_altRHSs___default;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__2(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction_match__1___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_isHoleRHS(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__3(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__2(lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_getRecFromUsing___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS___boxed(lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__6(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__4(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__4;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_getRecFromUsing___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_getRecFromUsing___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases_match__2(lean_object*);
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_getRecFromUsing___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Tactic_evalExact___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___boxed(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__1(lean_object*);
lean_object* l_Lean_Meta_getParamNames___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__5(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__5;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__2(lean_object*);
extern lean_object* l_Lean_mkSimpleThunk___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__6;
extern lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayedImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__1(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__3;
lean_object* l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Tactic_getInductiveValFromMajor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__4(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralizeFinalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__6;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGeneralizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Tactic_elabAsFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__1(lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
extern lean_object* l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__1;
lean_object* l_List_filterAux___main___at_Lean_resolveGlobalConst___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__5(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
extern lean_object* l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__5;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__3(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__5;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__4(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___boxed(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__2(lean_object*);
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_getRecFromUsing___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2;
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_isHoleRHS___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_RecInfo_altVars___default;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
lean_object* l_List_map___main___at_Lean_resolveGlobalConst___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__1(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__3(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2;
extern lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getRecFromUsing_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__1;
lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCases_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__3;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName(lean_object* x_1) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Syntax_getArg(x_5, x_4);
lean_dec(x_5);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generalize");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_local_ctx_find_from_user_name(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__3;
x_14 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_15 = lean_local_ctx_get_unused_name(x_4, x_14);
x_16 = lean_box(0);
x_17 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Elab_Tactic_elabTerm(x_1, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_21 = l_Lean_Elab_Tactic_evalGeneralizeAux(x_2, x_19, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___boxed), 11, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_17 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__2;
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__2), 13, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_12 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_generalize(x_1, x_2, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_intro1Core(x_14, x_12, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Lean_mkFVar(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_22);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = l_Lean_mkFVar(x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = l_Lean_mkFVar(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor___lambda__1___boxed), 10, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_1);
x_18 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__2___boxed), 11, 1);
lean_closure_set(x_19, 0, x_16);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_15, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_inc(x_1);
x_13 = l_Lean_checkTraceOption(x_3, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___spec__7(x_1, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_replaceRef(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_ctor_set(x_8, 3, x_18);
x_19 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1;
lean_inc(x_12);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2___boxed), 12, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_12);
x_21 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3;
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3___boxed), 11, 1);
lean_closure_set(x_23, 0, x_12);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_8, 2);
x_29 = lean_ctor_get(x_8, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_30 = l_Lean_replaceRef(x_1, x_29);
x_31 = l_Lean_replaceRef(x_30, x_29);
lean_dec(x_30);
x_32 = l_Lean_replaceRef(x_31, x_29);
lean_dec(x_29);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
x_34 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1;
lean_inc(x_12);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2___boxed), 12, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_12);
x_36 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3;
x_37 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_35);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3___boxed), 11, 1);
lean_closure_set(x_38, 0, x_12);
x_39 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_10);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = l_Array_empty___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
return x_42;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise depends on variable being generalized");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Lean_Meta_revert(x_1, x_2, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lean_Expr_fvarId_x21(x_3);
x_21 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_22 = lean_array_get_size(x_18);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_22);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_13);
x_25 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_26 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3;
x_27 = lean_box(0);
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_27, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_13, 1);
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = l_Lean_Expr_fvarId_x21(x_3);
x_37 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_34, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_38 = lean_array_get_size(x_34);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
x_42 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_43 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3;
x_44 = lean_box(0);
x_45 = l_Lean_Meta_throwTacticEx___rarg(x_42, x_1, x_43, x_44, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Expr_fvarId_x21(x_3);
x_56 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_52, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_57 = lean_array_get_size(x_52);
lean_dec(x_52);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_62 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_63 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3;
x_64 = lean_box(0);
x_65 = l_Lean_Meta_throwTacticEx___rarg(x_62, x_1, x_63, x_64, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
}
else
{
uint8_t x_70; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_13);
if (x_70 == 0)
{
return x_13;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_13, 0);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_13);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___boxed), 11, 3);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_13);
lean_closure_set(x_20, 2, x_2);
x_21 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__2___boxed), 11, 1);
lean_closure_set(x_22, 0, x_19);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_18, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_24;
}
else
{
uint8_t x_25; 
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
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getSepArgs(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
x_5 = lean_erase_macro_scopes(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1(x_1, x_2, x_5);
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
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
lean_inc(x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_PersistentArray_push___rarg(x_23, x_25);
lean_ctor_set(x_18, 0, x_26);
x_27 = lean_st_ref_set(x_10, x_17, x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_14);
lean_inc(x_12);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_PersistentArray_push___rarg(x_35, x_37);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_34);
lean_ctor_set(x_17, 3, x_39);
x_40 = lean_st_ref_set(x_10, x_17, x_19);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
x_47 = lean_ctor_get(x_17, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_48 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_14);
lean_inc(x_12);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Std_PersistentArray_push___rarg(x_49, x_52);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_48);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_st_ref_set(x_10, x_55, x_19);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_checkTraceOption(x_11, x_1);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor name '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkAlt");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" , ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_4 < x_3;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_4);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_17);
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 3);
lean_inc(x_47);
x_48 = l_Lean_replaceRef(x_17, x_47);
x_49 = l_Lean_replaceRef(x_48, x_47);
lean_dec(x_48);
x_50 = l_Lean_replaceRef(x_49, x_47);
lean_dec(x_47);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_50);
x_66 = lean_st_ref_get(x_13, x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_ctor_get_uint8(x_68, sizeof(void*)*1);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = 0;
x_52 = x_71;
x_53 = x_70;
goto block_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4;
x_74 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__3(x_73, x_6, x_7, x_8, x_9, x_10, x_11, x_51, x_13, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_unbox(x_75);
lean_dec(x_75);
x_52 = x_77;
x_53 = x_76;
goto block_65;
}
block_43:
{
uint8_t x_20; lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_mkSimpleThunk___closed__1;
x_39 = lean_name_eq(x_18, x_38);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; 
x_40 = 0;
x_41 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1(x_18, x_40, x_1);
x_20 = x_41;
goto block_37;
}
else
{
uint8_t x_42; 
x_42 = 1;
x_20 = x_42;
goto block_37;
}
block_37:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_17, x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_22, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec(x_18);
lean_dec(x_17);
x_33 = 1;
x_34 = x_4 + x_33;
x_35 = lean_box(0);
x_4 = x_34;
x_5 = x_35;
x_14 = x_19;
goto _start;
}
}
}
block_65:
{
if (x_52 == 0)
{
lean_dec(x_51);
x_19 = x_53;
goto block_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_inc(x_18);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_18);
x_55 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__6;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_17);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_17);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4;
x_63 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__2(x_62, x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_51, x_13, x_53);
lean_dec(x_51);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_19 = x_64;
goto block_43;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4(x_2, x_1, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RecInfo_altVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RecInfo_altRHSs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Tactic_getInductiveValFromMajor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_whnfRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_whnfRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is not an inductive type ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
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
x_8 = l_Lean_Meta_whnf___at_Lean_Elab_Tactic_getInductiveValFromMajor___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_6, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_environment_find(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_13);
x_19 = l_Lean_indentExpr(x_9);
x_20 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_25 = lean_box(0);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_24, x_1, x_23, x_25, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
if (lean_obj_tag(x_27) == 5)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_free_object(x_13);
x_29 = l_Lean_indentExpr(x_9);
x_30 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_35 = lean_box(0);
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_34, x_1, x_33, x_35, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_environment_find(x_39, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = l_Lean_indentExpr(x_9);
x_42 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_47 = lean_box(0);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_46, x_1, x_45, x_47, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
if (lean_obj_tag(x_49) == 5)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
x_52 = l_Lean_indentExpr(x_9);
x_53 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_58 = lean_box(0);
x_59 = l_Lean_Meta_throwTacticEx___rarg(x_57, x_1, x_56, x_58, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
x_60 = l_Lean_indentExpr(x_9);
x_61 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_66 = lean_box(0);
x_67 = l_Lean_Meta_throwTacticEx___rarg(x_65, x_1, x_64, x_66, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_8);
if (x_68 == 0)
{
return x_8;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_8, 0);
x_70 = lean_ctor_get(x_8, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_8);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
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
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralizeFinalize___spec__1), 6, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1), 7, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_getAppFn___main(x_13);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_Name_append___main(x_16, x_1);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_10, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
x_22 = lean_environment_find(x_21, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_13, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_9, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_9, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 3);
lean_inc(x_36);
x_37 = lean_nat_dec_eq(x_34, x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_9, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_9, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_9, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_9, 0);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_34, x_43);
lean_dec(x_34);
lean_ctor_set(x_9, 1, x_44);
x_2 = x_32;
x_11 = x_31;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_34, x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
x_2 = x_32;
x_9 = x_48;
x_11 = x_31;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_1);
x_50 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_51 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
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
uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
return x_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_23, 0);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_23);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_104; 
lean_dec(x_22);
x_60 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_104 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_box(0);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 7, 2);
lean_closure_set(x_109, 0, x_17);
lean_closure_set(x_109, 1, x_108);
x_110 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___closed__1;
x_111 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_112, 0, x_111);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_107, x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_113) == 0)
{
lean_dec(x_61);
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
return x_113;
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_63 = x_114;
goto block_103;
}
}
else
{
lean_object* x_115; 
lean_dec(x_17);
x_115 = lean_ctor_get(x_104, 1);
lean_inc(x_115);
lean_dec(x_104);
x_63 = x_115;
goto block_103;
}
block_103:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_66 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_13, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_ctor_get(x_9, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_9, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_9, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_9, 3);
lean_inc(x_79);
x_80 = lean_nat_dec_eq(x_77, x_78);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_9);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_9, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_9, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_9, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_9, 0);
lean_dec(x_85);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_77, x_86);
lean_dec(x_77);
lean_ctor_set(x_9, 1, x_87);
x_2 = x_75;
x_11 = x_74;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_9);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_77, x_89);
lean_dec(x_77);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_76);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_78);
lean_ctor_set(x_91, 3, x_79);
x_2 = x_75;
x_9 = x_91;
x_11 = x_74;
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_1);
x_93 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_94 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_93, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
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
uint8_t x_99; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_66);
if (x_99 == 0)
{
return x_66;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_66, 0);
x_101 = lean_ctor_get(x_66, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_66);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_116 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_116, 1);
lean_inc(x_124);
lean_dec(x_116);
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
lean_dec(x_117);
x_126 = lean_ctor_get(x_9, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_9, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_9, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_9, 3);
lean_inc(x_129);
x_130 = lean_nat_dec_eq(x_127, x_128);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_9);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_9, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_9, 2);
lean_dec(x_133);
x_134 = lean_ctor_get(x_9, 1);
lean_dec(x_134);
x_135 = lean_ctor_get(x_9, 0);
lean_dec(x_135);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_127, x_136);
lean_dec(x_127);
lean_ctor_set(x_9, 1, x_137);
x_2 = x_125;
x_11 = x_124;
goto _start;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_9);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_127, x_139);
lean_dec(x_127);
x_141 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_141, 0, x_126);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_128);
lean_ctor_set(x_141, 3, x_129);
x_2 = x_125;
x_9 = x_141;
x_11 = x_124;
goto _start;
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_1);
x_143 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_144 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_116);
if (x_149 == 0)
{
return x_116;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_116, 0);
x_151 = lean_ctor_get(x_116, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_116);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_12);
if (x_153 == 0)
{
return x_12;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_12, 0);
x_155 = lean_ctor_get(x_12, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_12);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_getRecFromUsing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Tactic_getRecFromUsing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getRecFromUsing_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_getRecFromUsing___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_14, x_15, x_16, x_1);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 5);
lean_inc(x_22);
lean_dec(x_4);
x_23 = l_Lean_ResolveName_resolveGlobalName(x_20, x_21, x_22, x_1);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_getRecFromUsing___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_getRecFromUsing___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_box(0);
x_16 = l_List_filterAux___main___at_Lean_resolveGlobalConst___spec__1(x_13, x_15);
x_17 = l_List_isEmpty___rarg(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = l_List_map___main___at_Lean_resolveGlobalConst___spec__2(x_16);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
lean_free_object(x_11);
x_19 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = l_List_filterAux___main___at_Lean_resolveGlobalConst___spec__1(x_24, x_26);
x_28 = l_List_isEmpty___rarg(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_1);
x_29 = l_List_map___main___at_Lean_resolveGlobalConst___spec__2(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
x_31 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_getRecFromUsing___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_mkConst(x_1, x_14);
x_16 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_17 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_List_map___main___at_Lean_resolveGlobalConstNoOverload___spec__1(x_14, x_12);
x_22 = l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_4);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_11, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_32);
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_29);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_box(0);
x_38 = l_Lean_mkConst(x_1, x_37);
x_39 = lean_expr_dbg_to_string(x_38);
lean_dec(x_38);
x_40 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_List_map___main___at_Lean_resolveGlobalConstNoOverload___spec__1(x_37, x_12);
x_45 = l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(x_44);
lean_dec(x_44);
x_46 = lean_string_append(x_43, x_45);
lean_dec(x_45);
x_47 = l_String_splitAux___main___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_4);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_4);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid recursor name '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getRecFromUsing___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
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
x_12 = l_Lean_Meta_inferType___at_Lean_Elab_Tactic_elabAsFVar___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_15 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_2);
x_18 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorInfo), 7, 2);
lean_closure_set(x_29, 0, x_19);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_27, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__6;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_19);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = l_Lean_Elab_Tactic_getRecFromUsing___closed__2;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__6;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
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
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_15, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_16, 0);
lean_inc(x_56);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_56);
return x_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_ctor_get(x_16, 0);
lean_inc(x_58);
lean_dec(x_16);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_12);
if (x_64 == 0)
{
return x_12;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_getRecFromUsing___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_getRecFromUsing___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_getRecFromUsing___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_getRecFromUsing___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_getRecFromUsing___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_getRecFromUsing___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_getRecFromUsing___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_7);
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_6);
lean_dec(x_6);
x_8 = l_Lean_mkSimpleThunk___closed__1;
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
static lean_object* _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for constructor '");
return x_1;
}
}
static lean_object* _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
return x_1;
}
}
static lean_object* _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(x_17, x_22, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_22, x_27);
if (lean_obj_tag(x_29) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
if (x_1 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_free_object(x_15);
lean_dec(x_25);
lean_free_object(x_14);
lean_dec(x_22);
lean_free_object(x_3);
lean_dec(x_19);
lean_inc(x_17);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_17);
x_31 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = lean_array_push(x_19, x_40);
x_42 = lean_box(0);
x_43 = lean_array_push(x_25, x_42);
lean_ctor_set(x_15, 0, x_43);
lean_ctor_set(x_3, 0, x_41);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_26, 0);
lean_inc(x_45);
x_46 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_45);
x_47 = l_Array_toList___rarg(x_46);
lean_dec(x_46);
x_48 = lean_array_push(x_19, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = l_Lean_Syntax_getArg(x_45, x_49);
lean_dec(x_45);
x_51 = lean_array_push(x_25, x_50);
lean_ctor_set(x_15, 0, x_51);
lean_ctor_set(x_3, 0, x_48);
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_26);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_29, 0);
x_55 = l_Lean_Syntax_inhabited;
x_56 = lean_array_get(x_55, x_22, x_54);
x_57 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_56);
x_58 = l_Array_toList___rarg(x_57);
lean_dec(x_57);
x_59 = lean_array_push(x_19, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = l_Lean_Syntax_getArg(x_56, x_60);
x_62 = lean_array_push(x_25, x_61);
x_63 = l_Array_eraseIdx___rarg(x_22, x_54);
lean_dec(x_54);
lean_ctor_set(x_29, 0, x_56);
lean_ctor_set(x_15, 1, x_29);
lean_ctor_set(x_15, 0, x_62);
lean_ctor_set(x_14, 0, x_63);
lean_ctor_set(x_3, 0, x_59);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_29, 0);
lean_inc(x_65);
lean_dec(x_29);
x_66 = l_Lean_Syntax_inhabited;
x_67 = lean_array_get(x_66, x_22, x_65);
x_68 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_67);
x_69 = l_Array_toList___rarg(x_68);
lean_dec(x_68);
x_70 = lean_array_push(x_19, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = l_Lean_Syntax_getArg(x_67, x_71);
x_73 = lean_array_push(x_25, x_72);
x_74 = l_Array_eraseIdx___rarg(x_22, x_65);
lean_dec(x_65);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_15, 1, x_75);
lean_ctor_set(x_15, 0, x_73);
lean_ctor_set(x_14, 0, x_74);
lean_ctor_set(x_3, 0, x_70);
x_2 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_28, 0);
lean_inc(x_77);
lean_dec(x_28);
x_78 = l_Lean_Syntax_inhabited;
x_79 = lean_array_get(x_78, x_22, x_77);
x_80 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_79);
x_81 = l_Array_toList___rarg(x_80);
lean_dec(x_80);
x_82 = lean_array_push(x_19, x_81);
x_83 = lean_unsigned_to_nat(3u);
x_84 = l_Lean_Syntax_getArg(x_79, x_83);
lean_dec(x_79);
x_85 = lean_array_push(x_25, x_84);
x_86 = l_Array_eraseIdx___rarg(x_22, x_77);
lean_dec(x_77);
lean_ctor_set(x_15, 0, x_85);
lean_ctor_set(x_14, 0, x_86);
lean_ctor_set(x_3, 0, x_82);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_15, 0);
x_89 = lean_ctor_get(x_15, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_15);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(x_17, x_22, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_22, x_90);
if (lean_obj_tag(x_92) == 0)
{
if (lean_obj_tag(x_89) == 0)
{
if (x_1 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_88);
lean_free_object(x_14);
lean_dec(x_22);
lean_free_object(x_3);
lean_dec(x_19);
lean_inc(x_17);
x_93 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_93, 0, x_17);
x_94 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_97, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_box(0);
x_104 = lean_array_push(x_19, x_103);
x_105 = lean_box(0);
x_106 = lean_array_push(x_88, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_89);
lean_ctor_set(x_14, 1, x_107);
lean_ctor_set(x_3, 0, x_104);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_89, 0);
lean_inc(x_109);
x_110 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_109);
x_111 = l_Array_toList___rarg(x_110);
lean_dec(x_110);
x_112 = lean_array_push(x_19, x_111);
x_113 = lean_unsigned_to_nat(3u);
x_114 = l_Lean_Syntax_getArg(x_109, x_113);
lean_dec(x_109);
x_115 = lean_array_push(x_88, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_89);
lean_ctor_set(x_14, 1, x_116);
lean_ctor_set(x_3, 0, x_112);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_89);
x_118 = lean_ctor_get(x_92, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_119 = x_92;
} else {
 lean_dec_ref(x_92);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Syntax_inhabited;
x_121 = lean_array_get(x_120, x_22, x_118);
x_122 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_121);
x_123 = l_Array_toList___rarg(x_122);
lean_dec(x_122);
x_124 = lean_array_push(x_19, x_123);
x_125 = lean_unsigned_to_nat(3u);
x_126 = l_Lean_Syntax_getArg(x_121, x_125);
x_127 = lean_array_push(x_88, x_126);
x_128 = l_Array_eraseIdx___rarg(x_22, x_118);
lean_dec(x_118);
if (lean_is_scalar(x_119)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_119;
}
lean_ctor_set(x_129, 0, x_121);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_14, 1, x_130);
lean_ctor_set(x_14, 0, x_128);
lean_ctor_set(x_3, 0, x_124);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_91, 0);
lean_inc(x_132);
lean_dec(x_91);
x_133 = l_Lean_Syntax_inhabited;
x_134 = lean_array_get(x_133, x_22, x_132);
x_135 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_134);
x_136 = l_Array_toList___rarg(x_135);
lean_dec(x_135);
x_137 = lean_array_push(x_19, x_136);
x_138 = lean_unsigned_to_nat(3u);
x_139 = l_Lean_Syntax_getArg(x_134, x_138);
lean_dec(x_134);
x_140 = lean_array_push(x_88, x_139);
x_141 = l_Array_eraseIdx___rarg(x_22, x_132);
lean_dec(x_132);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_89);
lean_ctor_set(x_14, 1, x_142);
lean_ctor_set(x_14, 0, x_141);
lean_ctor_set(x_3, 0, x_137);
x_2 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_14, 0);
lean_inc(x_144);
lean_dec(x_14);
x_145 = lean_ctor_get(x_15, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_15, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_147 = x_15;
} else {
 lean_dec_ref(x_15);
 x_147 = lean_box(0);
}
x_148 = lean_unsigned_to_nat(0u);
x_149 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(x_17, x_144, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_144, x_148);
if (lean_obj_tag(x_150) == 0)
{
if (lean_obj_tag(x_146) == 0)
{
if (x_1 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_144);
lean_free_object(x_3);
lean_dec(x_19);
lean_inc(x_17);
x_151 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_151, 0, x_17);
x_152 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2;
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_155 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_155, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_box(0);
x_162 = lean_array_push(x_19, x_161);
x_163 = lean_box(0);
x_164 = lean_array_push(x_145, x_163);
if (lean_is_scalar(x_147)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_147;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_146);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_144);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_3, 1, x_166);
lean_ctor_set(x_3, 0, x_162);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_146, 0);
lean_inc(x_168);
x_169 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_168);
x_170 = l_Array_toList___rarg(x_169);
lean_dec(x_169);
x_171 = lean_array_push(x_19, x_170);
x_172 = lean_unsigned_to_nat(3u);
x_173 = l_Lean_Syntax_getArg(x_168, x_172);
lean_dec(x_168);
x_174 = lean_array_push(x_145, x_173);
if (lean_is_scalar(x_147)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_147;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_146);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_144);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_3, 1, x_176);
lean_ctor_set(x_3, 0, x_171);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_146);
x_178 = lean_ctor_get(x_150, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_179 = x_150;
} else {
 lean_dec_ref(x_150);
 x_179 = lean_box(0);
}
x_180 = l_Lean_Syntax_inhabited;
x_181 = lean_array_get(x_180, x_144, x_178);
x_182 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_181);
x_183 = l_Array_toList___rarg(x_182);
lean_dec(x_182);
x_184 = lean_array_push(x_19, x_183);
x_185 = lean_unsigned_to_nat(3u);
x_186 = l_Lean_Syntax_getArg(x_181, x_185);
x_187 = lean_array_push(x_145, x_186);
x_188 = l_Array_eraseIdx___rarg(x_144, x_178);
lean_dec(x_178);
if (lean_is_scalar(x_179)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_179;
}
lean_ctor_set(x_189, 0, x_181);
if (lean_is_scalar(x_147)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_147;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set(x_3, 1, x_191);
lean_ctor_set(x_3, 0, x_184);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_193 = lean_ctor_get(x_149, 0);
lean_inc(x_193);
lean_dec(x_149);
x_194 = l_Lean_Syntax_inhabited;
x_195 = lean_array_get(x_194, x_144, x_193);
x_196 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_195);
x_197 = l_Array_toList___rarg(x_196);
lean_dec(x_196);
x_198 = lean_array_push(x_19, x_197);
x_199 = lean_unsigned_to_nat(3u);
x_200 = l_Lean_Syntax_getArg(x_195, x_199);
lean_dec(x_195);
x_201 = lean_array_push(x_145, x_200);
x_202 = l_Array_eraseIdx___rarg(x_144, x_193);
lean_dec(x_193);
if (lean_is_scalar(x_147)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_147;
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_146);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_3, 1, x_204);
lean_ctor_set(x_3, 0, x_198);
x_2 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_206 = lean_ctor_get(x_2, 0);
x_207 = lean_ctor_get(x_2, 1);
x_208 = lean_ctor_get(x_3, 0);
lean_inc(x_208);
lean_dec(x_3);
x_209 = lean_ctor_get(x_14, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_210 = x_14;
} else {
 lean_dec_ref(x_14);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_15, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_15, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_213 = x_15;
} else {
 lean_dec_ref(x_15);
 x_213 = lean_box(0);
}
x_214 = lean_unsigned_to_nat(0u);
x_215 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(x_206, x_209, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; 
x_216 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_209, x_214);
if (lean_obj_tag(x_216) == 0)
{
if (lean_obj_tag(x_212) == 0)
{
if (x_1 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_inc(x_206);
x_217 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_217, 0, x_206);
x_218 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2;
x_219 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_221 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_221, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_227 = lean_box(0);
x_228 = lean_array_push(x_208, x_227);
x_229 = lean_box(0);
x_230 = lean_array_push(x_211, x_229);
if (lean_is_scalar(x_213)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_213;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_212);
if (lean_is_scalar(x_210)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_210;
}
lean_ctor_set(x_232, 0, x_209);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_228);
lean_ctor_set(x_233, 1, x_232);
x_2 = x_207;
x_3 = x_233;
goto _start;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_235 = lean_ctor_get(x_212, 0);
lean_inc(x_235);
x_236 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_235);
x_237 = l_Array_toList___rarg(x_236);
lean_dec(x_236);
x_238 = lean_array_push(x_208, x_237);
x_239 = lean_unsigned_to_nat(3u);
x_240 = l_Lean_Syntax_getArg(x_235, x_239);
lean_dec(x_235);
x_241 = lean_array_push(x_211, x_240);
if (lean_is_scalar(x_213)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_213;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_212);
if (lean_is_scalar(x_210)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_210;
}
lean_ctor_set(x_243, 0, x_209);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_243);
x_2 = x_207;
x_3 = x_244;
goto _start;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_212);
x_246 = lean_ctor_get(x_216, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_247 = x_216;
} else {
 lean_dec_ref(x_216);
 x_247 = lean_box(0);
}
x_248 = l_Lean_Syntax_inhabited;
x_249 = lean_array_get(x_248, x_209, x_246);
x_250 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_249);
x_251 = l_Array_toList___rarg(x_250);
lean_dec(x_250);
x_252 = lean_array_push(x_208, x_251);
x_253 = lean_unsigned_to_nat(3u);
x_254 = l_Lean_Syntax_getArg(x_249, x_253);
x_255 = lean_array_push(x_211, x_254);
x_256 = l_Array_eraseIdx___rarg(x_209, x_246);
lean_dec(x_246);
if (lean_is_scalar(x_247)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_247;
}
lean_ctor_set(x_257, 0, x_249);
if (lean_is_scalar(x_213)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_213;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_257);
if (lean_is_scalar(x_210)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_210;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_259);
x_2 = x_207;
x_3 = x_260;
goto _start;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_262 = lean_ctor_get(x_215, 0);
lean_inc(x_262);
lean_dec(x_215);
x_263 = l_Lean_Syntax_inhabited;
x_264 = lean_array_get(x_263, x_209, x_262);
x_265 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_264);
x_266 = l_Array_toList___rarg(x_265);
lean_dec(x_265);
x_267 = lean_array_push(x_208, x_266);
x_268 = lean_unsigned_to_nat(3u);
x_269 = l_Lean_Syntax_getArg(x_264, x_268);
lean_dec(x_264);
x_270 = lean_array_push(x_211, x_269);
x_271 = l_Array_eraseIdx___rarg(x_209, x_262);
lean_dec(x_262);
if (lean_is_scalar(x_213)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_213;
}
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_212);
if (lean_is_scalar(x_210)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_210;
}
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_273);
x_2 = x_207;
x_3 = x_274;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unused alternative");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_23 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(x_2);
lean_inc(x_10);
x_24 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames(x_23, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3(x_3, x_22, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_30, 1);
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_dec(x_41);
x_42 = l_Array_isEmpty___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_33);
lean_dec(x_40);
lean_dec(x_37);
lean_free_object(x_30);
lean_dec(x_22);
lean_dec(x_20);
x_43 = l_Lean_Syntax_inhabited;
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get(x_43, x_38, x_44);
lean_dec(x_38);
x_46 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_47 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_45, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_20);
lean_ctor_set(x_52, 1, x_37);
lean_ctor_set(x_52, 2, x_40);
x_53 = l_List_redLength___main___rarg(x_22);
x_54 = lean_mk_empty_array_with_capacity(x_53);
lean_dec(x_53);
x_55 = l_List_toArrayAux___main___rarg(x_22, x_54);
lean_ctor_set(x_33, 1, x_55);
lean_ctor_set(x_33, 0, x_52);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_33, 0);
lean_inc(x_56);
lean_dec(x_33);
x_57 = l_Array_isEmpty___rarg(x_38);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_56);
lean_dec(x_37);
lean_free_object(x_30);
lean_dec(x_22);
lean_dec(x_20);
x_58 = l_Lean_Syntax_inhabited;
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get(x_58, x_38, x_59);
lean_dec(x_38);
x_61 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_62 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_60, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
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
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_37);
lean_ctor_set(x_67, 2, x_56);
x_68 = l_List_redLength___main___rarg(x_22);
x_69 = lean_mk_empty_array_with_capacity(x_68);
lean_dec(x_68);
x_70 = l_List_toArrayAux___main___rarg(x_22, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_30, 0, x_71);
return x_30;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
lean_dec(x_30);
x_73 = lean_ctor_get(x_31, 0);
lean_inc(x_73);
lean_dec(x_31);
x_74 = lean_ctor_get(x_32, 0);
lean_inc(x_74);
lean_dec(x_32);
x_75 = lean_ctor_get(x_33, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_76 = x_33;
} else {
 lean_dec_ref(x_33);
 x_76 = lean_box(0);
}
x_77 = l_Array_isEmpty___rarg(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_20);
x_78 = l_Lean_Syntax_inhabited;
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_array_get(x_78, x_74, x_79);
lean_dec(x_74);
x_81 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_82 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_80, x_81, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_74);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_20);
lean_ctor_set(x_87, 1, x_73);
lean_ctor_set(x_87, 2, x_75);
x_88 = l_List_redLength___main___rarg(x_22);
x_89 = lean_mk_empty_array_with_capacity(x_88);
lean_dec(x_88);
x_90 = l_List_toArrayAux___main___rarg(x_22, x_89);
if (lean_is_scalar(x_76)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_76;
}
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_72);
return x_92;
}
}
}
else
{
uint8_t x_93; 
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
x_93 = !lean_is_exclusive(x_30);
if (x_93 == 0)
{
return x_30;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_30, 0);
x_95 = lean_ctor_get(x_30, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_30);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
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
x_97 = !lean_is_exclusive(x_24);
if (x_97 == 0)
{
return x_24;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_24, 0);
x_99 = lean_ctor_get(x_24, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_24);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = l_Array_empty___closed__1;
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_20);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_13, 0, x_103);
return x_13;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_13, 0);
x_105 = lean_ctor_get(x_13, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_13);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_mkRecFor___closed__1;
x_109 = lean_name_mk_string(x_107, x_108);
x_110 = l_Lean_Syntax_isNone(x_2);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_104, 4);
lean_inc(x_111);
lean_dec(x_104);
x_112 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(x_2);
lean_inc(x_10);
x_113 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames(x_112, x_111, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_105);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Array_empty___closed__1;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3(x_3, x_111, x_118, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_114);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
x_129 = l_Array_isEmpty___rarg(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_111);
lean_dec(x_109);
x_130 = l_Lean_Syntax_inhabited;
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_array_get(x_130, x_126, x_131);
lean_dec(x_126);
x_133 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_134 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_132, x_133, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_123);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_126);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_109);
lean_ctor_set(x_139, 1, x_125);
lean_ctor_set(x_139, 2, x_127);
x_140 = l_List_redLength___main___rarg(x_111);
x_141 = lean_mk_empty_array_with_capacity(x_140);
lean_dec(x_140);
x_142 = l_List_toArrayAux___main___rarg(x_111, x_141);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
if (lean_is_scalar(x_124)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_124;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_123);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_ctor_get(x_119, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_119, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_147 = x_119;
} else {
 lean_dec_ref(x_119);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_149 = lean_ctor_get(x_113, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_113, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_151 = x_113;
} else {
 lean_dec_ref(x_113);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_104);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_153 = l_Array_empty___closed__1;
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_109);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_105);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = !lean_is_exclusive(x_13);
if (x_157 == 0)
{
return x_13;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_13);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo_match__6___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getParamNames___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getParamNamesImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_7);
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
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for minor premise '");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_nat_dec_le(x_16, x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_4, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_4, x_20);
lean_dec(x_4);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
x_40 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_5);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_6);
x_22 = x_41;
x_23 = x_15;
goto block_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Name_inhabited;
x_43 = lean_array_get(x_42, x_2, x_5);
x_44 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(x_43, x_35, x_18);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_35, x_18);
if (lean_obj_tag(x_45) == 0)
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_29);
lean_dec(x_35);
lean_free_object(x_6);
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_5);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_43);
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
x_57 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_56);
x_58 = l_Array_toList___rarg(x_57);
lean_dec(x_57);
x_59 = lean_array_push(x_32, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = l_Lean_Syntax_getArg(x_56, x_60);
lean_dec(x_56);
x_62 = lean_array_push(x_38, x_61);
lean_ctor_set(x_30, 0, x_62);
lean_ctor_set(x_6, 0, x_59);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_6);
x_22 = x_63;
x_23 = x_15;
goto block_28;
}
}
else
{
uint8_t x_64; 
lean_dec(x_43);
lean_dec(x_39);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = l_Lean_Syntax_inhabited;
x_67 = lean_array_get(x_66, x_35, x_65);
x_68 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_67);
x_69 = l_Array_toList___rarg(x_68);
lean_dec(x_68);
x_70 = lean_array_push(x_32, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = l_Lean_Syntax_getArg(x_67, x_71);
x_73 = lean_array_push(x_38, x_72);
x_74 = l_Array_eraseIdx___rarg(x_35, x_65);
lean_dec(x_65);
lean_ctor_set(x_45, 0, x_67);
lean_ctor_set(x_30, 1, x_45);
lean_ctor_set(x_30, 0, x_73);
lean_ctor_set(x_29, 0, x_74);
lean_ctor_set(x_6, 0, x_70);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_6);
x_22 = x_75;
x_23 = x_15;
goto block_28;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
lean_dec(x_45);
x_77 = l_Lean_Syntax_inhabited;
x_78 = lean_array_get(x_77, x_35, x_76);
x_79 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_78);
x_80 = l_Array_toList___rarg(x_79);
lean_dec(x_79);
x_81 = lean_array_push(x_32, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = l_Lean_Syntax_getArg(x_78, x_82);
x_84 = lean_array_push(x_38, x_83);
x_85 = l_Array_eraseIdx___rarg(x_35, x_76);
lean_dec(x_76);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_30, 1, x_86);
lean_ctor_set(x_30, 0, x_84);
lean_ctor_set(x_29, 0, x_85);
lean_ctor_set(x_6, 0, x_81);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_6);
x_22 = x_87;
x_23 = x_15;
goto block_28;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_43);
x_88 = lean_ctor_get(x_44, 0);
lean_inc(x_88);
lean_dec(x_44);
x_89 = l_Lean_Syntax_inhabited;
x_90 = lean_array_get(x_89, x_35, x_88);
x_91 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_90);
x_92 = l_Array_toList___rarg(x_91);
lean_dec(x_91);
x_93 = lean_array_push(x_32, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = l_Lean_Syntax_getArg(x_90, x_94);
lean_dec(x_90);
x_96 = lean_array_push(x_38, x_95);
x_97 = l_Array_eraseIdx___rarg(x_35, x_88);
lean_dec(x_88);
lean_ctor_set(x_30, 0, x_96);
lean_ctor_set(x_29, 0, x_97);
lean_ctor_set(x_6, 0, x_93);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_6);
x_22 = x_98;
x_23 = x_15;
goto block_28;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_30, 0);
x_100 = lean_ctor_get(x_30, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_30);
x_101 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_5);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_29, 1, x_102);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_6);
x_22 = x_103;
x_23 = x_15;
goto block_28;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = l_Lean_Name_inhabited;
x_105 = lean_array_get(x_104, x_2, x_5);
x_106 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(x_105, x_35, x_18);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_35, x_18);
if (lean_obj_tag(x_107) == 0)
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_99);
lean_free_object(x_29);
lean_dec(x_35);
lean_free_object(x_6);
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_5);
x_108 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_109 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_112, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
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
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_105);
x_118 = lean_ctor_get(x_100, 0);
lean_inc(x_118);
x_119 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_118);
x_120 = l_Array_toList___rarg(x_119);
lean_dec(x_119);
x_121 = lean_array_push(x_32, x_120);
x_122 = lean_unsigned_to_nat(3u);
x_123 = l_Lean_Syntax_getArg(x_118, x_122);
lean_dec(x_118);
x_124 = lean_array_push(x_99, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_100);
lean_ctor_set(x_29, 1, x_125);
lean_ctor_set(x_6, 0, x_121);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_6);
x_22 = x_126;
x_23 = x_15;
goto block_28;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_105);
lean_dec(x_100);
x_127 = lean_ctor_get(x_107, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_128 = x_107;
} else {
 lean_dec_ref(x_107);
 x_128 = lean_box(0);
}
x_129 = l_Lean_Syntax_inhabited;
x_130 = lean_array_get(x_129, x_35, x_127);
x_131 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_130);
x_132 = l_Array_toList___rarg(x_131);
lean_dec(x_131);
x_133 = lean_array_push(x_32, x_132);
x_134 = lean_unsigned_to_nat(3u);
x_135 = l_Lean_Syntax_getArg(x_130, x_134);
x_136 = lean_array_push(x_99, x_135);
x_137 = l_Array_eraseIdx___rarg(x_35, x_127);
lean_dec(x_127);
if (lean_is_scalar(x_128)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_128;
}
lean_ctor_set(x_138, 0, x_130);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_29, 1, x_139);
lean_ctor_set(x_29, 0, x_137);
lean_ctor_set(x_6, 0, x_133);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_6);
x_22 = x_140;
x_23 = x_15;
goto block_28;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_105);
x_141 = lean_ctor_get(x_106, 0);
lean_inc(x_141);
lean_dec(x_106);
x_142 = l_Lean_Syntax_inhabited;
x_143 = lean_array_get(x_142, x_35, x_141);
x_144 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_143);
x_145 = l_Array_toList___rarg(x_144);
lean_dec(x_144);
x_146 = lean_array_push(x_32, x_145);
x_147 = lean_unsigned_to_nat(3u);
x_148 = l_Lean_Syntax_getArg(x_143, x_147);
lean_dec(x_143);
x_149 = lean_array_push(x_99, x_148);
x_150 = l_Array_eraseIdx___rarg(x_35, x_141);
lean_dec(x_141);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_100);
lean_ctor_set(x_29, 1, x_151);
lean_ctor_set(x_29, 0, x_150);
lean_ctor_set(x_6, 0, x_146);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_6);
x_22 = x_152;
x_23 = x_15;
goto block_28;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_29, 0);
lean_inc(x_153);
lean_dec(x_29);
x_154 = lean_ctor_get(x_30, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_30, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_156 = x_30;
} else {
 lean_dec_ref(x_30);
 x_156 = lean_box(0);
}
x_157 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_5);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_155);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_153);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_6, 1, x_159);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_6);
x_22 = x_160;
x_23 = x_15;
goto block_28;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = l_Lean_Name_inhabited;
x_162 = lean_array_get(x_161, x_2, x_5);
x_163 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(x_162, x_153, x_18);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_153, x_18);
if (lean_obj_tag(x_164) == 0)
{
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_free_object(x_6);
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_5);
x_165 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_165, 0, x_162);
x_166 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2;
x_167 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_169 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_169, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_162);
x_175 = lean_ctor_get(x_155, 0);
lean_inc(x_175);
x_176 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_175);
x_177 = l_Array_toList___rarg(x_176);
lean_dec(x_176);
x_178 = lean_array_push(x_32, x_177);
x_179 = lean_unsigned_to_nat(3u);
x_180 = l_Lean_Syntax_getArg(x_175, x_179);
lean_dec(x_175);
x_181 = lean_array_push(x_154, x_180);
if (lean_is_scalar(x_156)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_156;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_155);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_153);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_6, 1, x_183);
lean_ctor_set(x_6, 0, x_178);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_6);
x_22 = x_184;
x_23 = x_15;
goto block_28;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_162);
lean_dec(x_155);
x_185 = lean_ctor_get(x_164, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_186 = x_164;
} else {
 lean_dec_ref(x_164);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Syntax_inhabited;
x_188 = lean_array_get(x_187, x_153, x_185);
x_189 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_188);
x_190 = l_Array_toList___rarg(x_189);
lean_dec(x_189);
x_191 = lean_array_push(x_32, x_190);
x_192 = lean_unsigned_to_nat(3u);
x_193 = l_Lean_Syntax_getArg(x_188, x_192);
x_194 = lean_array_push(x_154, x_193);
x_195 = l_Array_eraseIdx___rarg(x_153, x_185);
lean_dec(x_185);
if (lean_is_scalar(x_186)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_186;
}
lean_ctor_set(x_196, 0, x_188);
if (lean_is_scalar(x_156)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_156;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_6, 1, x_198);
lean_ctor_set(x_6, 0, x_191);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_6);
x_22 = x_199;
x_23 = x_15;
goto block_28;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_162);
x_200 = lean_ctor_get(x_163, 0);
lean_inc(x_200);
lean_dec(x_163);
x_201 = l_Lean_Syntax_inhabited;
x_202 = lean_array_get(x_201, x_153, x_200);
x_203 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_202);
x_204 = l_Array_toList___rarg(x_203);
lean_dec(x_203);
x_205 = lean_array_push(x_32, x_204);
x_206 = lean_unsigned_to_nat(3u);
x_207 = l_Lean_Syntax_getArg(x_202, x_206);
lean_dec(x_202);
x_208 = lean_array_push(x_154, x_207);
x_209 = l_Array_eraseIdx___rarg(x_153, x_200);
lean_dec(x_200);
if (lean_is_scalar(x_156)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_156;
}
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_155);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_6, 1, x_211);
lean_ctor_set(x_6, 0, x_205);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_6);
x_22 = x_212;
x_23 = x_15;
goto block_28;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_213 = lean_ctor_get(x_6, 0);
lean_inc(x_213);
lean_dec(x_6);
x_214 = lean_ctor_get(x_29, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_215 = x_29;
} else {
 lean_dec_ref(x_29);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_30, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_30, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_218 = x_30;
} else {
 lean_dec_ref(x_30);
 x_218 = lean_box(0);
}
x_219 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_5);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_217);
if (lean_is_scalar(x_215)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_215;
}
lean_ctor_set(x_221, 0, x_214);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_213);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_22 = x_223;
x_23 = x_15;
goto block_28;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = l_Lean_Name_inhabited;
x_225 = lean_array_get(x_224, x_2, x_5);
x_226 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(x_225, x_214, x_18);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__2(x_214, x_18);
if (lean_obj_tag(x_227) == 0)
{
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_218);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_21);
lean_dec(x_5);
x_228 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_228, 0, x_225);
x_229 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2;
x_230 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4;
x_232 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_232, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_225);
x_238 = lean_ctor_get(x_217, 0);
lean_inc(x_238);
x_239 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_238);
x_240 = l_Array_toList___rarg(x_239);
lean_dec(x_239);
x_241 = lean_array_push(x_213, x_240);
x_242 = lean_unsigned_to_nat(3u);
x_243 = l_Lean_Syntax_getArg(x_238, x_242);
lean_dec(x_238);
x_244 = lean_array_push(x_216, x_243);
if (lean_is_scalar(x_218)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_218;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_217);
if (lean_is_scalar(x_215)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_215;
}
lean_ctor_set(x_246, 0, x_214);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_22 = x_248;
x_23 = x_15;
goto block_28;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_225);
lean_dec(x_217);
x_249 = lean_ctor_get(x_227, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_250 = x_227;
} else {
 lean_dec_ref(x_227);
 x_250 = lean_box(0);
}
x_251 = l_Lean_Syntax_inhabited;
x_252 = lean_array_get(x_251, x_214, x_249);
x_253 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_252);
x_254 = l_Array_toList___rarg(x_253);
lean_dec(x_253);
x_255 = lean_array_push(x_213, x_254);
x_256 = lean_unsigned_to_nat(3u);
x_257 = l_Lean_Syntax_getArg(x_252, x_256);
x_258 = lean_array_push(x_216, x_257);
x_259 = l_Array_eraseIdx___rarg(x_214, x_249);
lean_dec(x_249);
if (lean_is_scalar(x_250)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_250;
}
lean_ctor_set(x_260, 0, x_252);
if (lean_is_scalar(x_218)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_218;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_260);
if (lean_is_scalar(x_215)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_215;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_255);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_22 = x_264;
x_23 = x_15;
goto block_28;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_225);
x_265 = lean_ctor_get(x_226, 0);
lean_inc(x_265);
lean_dec(x_226);
x_266 = l_Lean_Syntax_inhabited;
x_267 = lean_array_get(x_266, x_214, x_265);
x_268 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_267);
x_269 = l_Array_toList___rarg(x_268);
lean_dec(x_268);
x_270 = lean_array_push(x_213, x_269);
x_271 = lean_unsigned_to_nat(3u);
x_272 = l_Lean_Syntax_getArg(x_267, x_271);
lean_dec(x_267);
x_273 = lean_array_push(x_216, x_272);
x_274 = l_Array_eraseIdx___rarg(x_214, x_265);
lean_dec(x_265);
if (lean_is_scalar(x_218)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_218;
}
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_217);
if (lean_is_scalar(x_215)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_215;
}
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_270);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_22 = x_278;
x_23 = x_15;
goto block_28;
}
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_nat_add(x_5, x_25);
lean_dec(x_5);
x_4 = x_21;
x_5 = x_26;
x_6 = x_24;
x_15 = x_23;
goto _start;
}
}
else
{
lean_object* x_279; 
lean_dec(x_5);
lean_dec(x_4);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_6);
lean_ctor_set(x_279, 1, x_15);
return x_279;
}
}
else
{
lean_object* x_280; 
lean_dec(x_5);
lean_dec(x_4);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_6);
lean_ctor_set(x_280, 1, x_15);
return x_280;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = lean_erase_macro_scopes(x_23);
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
x_31 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(x_15);
lean_dec(x_15);
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
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__1), 6, 1);
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
x_40 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_36, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_get_size(x_41);
x_44 = lean_unsigned_to_nat(0u);
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_22);
x_46 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
lean_ctor_set(x_33, 1, x_46);
lean_ctor_set(x_33, 0, x_31);
x_47 = l_Array_empty___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_33);
x_49 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(x_27, x_41, x_45, x_43, x_44, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_27);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = l_Array_isEmpty___rarg(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_56);
lean_free_object(x_49);
lean_dec(x_29);
x_60 = l_Lean_Syntax_inhabited;
x_61 = lean_array_get(x_60, x_57, x_44);
lean_dec(x_57);
x_62 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_63 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_61, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_ctor_set(x_68, 1, x_56);
lean_ctor_set(x_68, 2, x_58);
lean_ctor_set(x_49, 0, x_68);
return x_49;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_dec(x_49);
x_70 = lean_ctor_get(x_50, 0);
lean_inc(x_70);
lean_dec(x_50);
x_71 = lean_ctor_get(x_51, 0);
lean_inc(x_71);
lean_dec(x_51);
x_72 = lean_ctor_get(x_52, 0);
lean_inc(x_72);
lean_dec(x_52);
x_73 = l_Array_isEmpty___rarg(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_29);
x_74 = l_Lean_Syntax_inhabited;
x_75 = lean_array_get(x_74, x_71, x_44);
lean_dec(x_71);
x_76 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_77 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_75, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_75);
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
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_71);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_29);
lean_ctor_set(x_82, 1, x_70);
lean_ctor_set(x_82, 2, x_72);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_69);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_49);
if (x_84 == 0)
{
return x_49;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_49, 0);
x_86 = lean_ctor_get(x_49, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_49);
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
x_88 = !lean_is_exclusive(x_40);
if (x_88 == 0)
{
return x_40;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_40, 0);
x_90 = lean_ctor_get(x_40, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_40);
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
x_92 = lean_ctor_get(x_33, 0);
lean_inc(x_92);
lean_dec(x_33);
lean_inc(x_29);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__1), 6, 1);
lean_closure_set(x_93, 0, x_29);
x_94 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_94, 0, x_93);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_95 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_92, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_array_get_size(x_96);
x_99 = lean_unsigned_to_nat(0u);
lean_inc(x_98);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_22);
x_101 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_31);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Array_empty___closed__1;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(x_27, x_96, x_100, x_98, x_99, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_97);
lean_dec(x_100);
lean_dec(x_96);
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
x_114 = l_Array_isEmpty___rarg(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_29);
x_115 = l_Lean_Syntax_inhabited;
x_116 = lean_array_get(x_115, x_112, x_99);
lean_dec(x_112);
x_117 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_118 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_116, x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_116);
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
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_112);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_29);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_123, 2, x_113);
if (lean_is_scalar(x_110)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_110;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_109);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_105, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_105, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_127 = x_105;
} else {
 lean_dec_ref(x_105);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
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
x_129 = lean_ctor_get(x_95, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_95, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_131 = x_95;
} else {
 lean_dec_ref(x_95);
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
}
else
{
uint8_t x_133; 
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
x_133 = !lean_is_exclusive(x_32);
if (x_133 == 0)
{
return x_32;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_32, 0);
x_135 = lean_ctor_get(x_32, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_32);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
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
x_137 = l_Array_empty___closed__1;
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_29);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_25, 0, x_138);
return x_25;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_25, 0);
x_140 = lean_ctor_get(x_25, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_25);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = l_Lean_Syntax_isNone(x_15);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(x_15);
lean_dec(x_15);
x_144 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
lean_inc(x_141);
x_149 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__1), 6, 1);
lean_closure_set(x_149, 0, x_141);
x_150 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_150, 0, x_149);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_151 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_147, x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_146);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_array_get_size(x_152);
x_155 = lean_unsigned_to_nat(0u);
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_22);
x_157 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
if (lean_is_scalar(x_148)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_148;
}
lean_ctor_set(x_158, 0, x_143);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Array_empty___closed__1;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(x_139, x_152, x_156, x_154, x_155, x_160, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_153);
lean_dec(x_156);
lean_dec(x_152);
lean_dec(x_139);
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
x_170 = l_Array_isEmpty___rarg(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_141);
x_171 = l_Lean_Syntax_inhabited;
x_172 = lean_array_get(x_171, x_168, x_155);
lean_dec(x_168);
x_173 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_174 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_172, x_173, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_165);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_172);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_168);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_141);
lean_ctor_set(x_179, 1, x_167);
lean_ctor_set(x_179, 2, x_169);
if (lean_is_scalar(x_166)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_166;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_165);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_141);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = lean_ctor_get(x_161, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_161, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_183 = x_161;
} else {
 lean_dec_ref(x_161);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_148);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = lean_ctor_get(x_151, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_151, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_187 = x_151;
} else {
 lean_dec_ref(x_151);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_189 = lean_ctor_get(x_144, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_144, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_191 = x_144;
} else {
 lean_dec_ref(x_144);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_139);
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = l_Array_empty___closed__1;
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_141);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set(x_194, 2, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_140);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = !lean_is_exclusive(x_25);
if (x_196 == 0)
{
return x_25;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_25, 0);
x_198 = lean_ctor_get(x_25, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_25);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; lean_object* x_201; 
lean_dec(x_13);
x_200 = 0;
x_201 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault(x_2, x_15, x_200, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
lean_ctor_set(x_201, 0, x_204);
return x_201;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_201, 0);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_201);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_201);
if (x_209 == 0)
{
return x_201;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_201, 0);
x_211 = lean_ctor_get(x_201, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_201);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = lean_ctor_get(x_9, 1);
x_215 = lean_ctor_get(x_9, 2);
x_216 = lean_ctor_get(x_9, 3);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_9);
x_217 = l_Lean_replaceRef(x_1, x_216);
x_218 = l_Lean_replaceRef(x_217, x_216);
lean_dec(x_217);
x_219 = l_Lean_replaceRef(x_218, x_216);
lean_dec(x_216);
lean_dec(x_218);
x_220 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_214);
lean_ctor_set(x_220, 2, x_215);
lean_ctor_set(x_220, 3, x_219);
if (x_16 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_unsigned_to_nat(1u);
x_222 = l_Lean_Syntax_getIdAt(x_13, x_221);
lean_dec(x_13);
x_223 = lean_erase_macro_scopes(x_222);
lean_inc(x_10);
lean_inc(x_220);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_224 = l_Lean_Elab_Tactic_getRecFromUsing(x_2, x_223, x_3, x_4, x_5, x_6, x_7, x_8, x_220, x_10, x_11);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_225, 0);
lean_inc(x_228);
x_229 = l_Lean_Syntax_isNone(x_15);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_227);
x_230 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAlts(x_15);
lean_dec(x_15);
x_231 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_220, x_10, x_226);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
lean_inc(x_228);
x_236 = lean_alloc_closure((void*)(l_Lean_Meta_getParamNames___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__1), 6, 1);
lean_closure_set(x_236, 0, x_228);
x_237 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_237, 0, x_236);
lean_inc(x_10);
lean_inc(x_220);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_238 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_234, x_237, x_3, x_4, x_5, x_6, x_7, x_8, x_220, x_10, x_233);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_array_get_size(x_239);
x_242 = lean_unsigned_to_nat(0u);
lean_inc(x_241);
x_243 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_221);
x_244 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1;
if (lean_is_scalar(x_235)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_235;
}
lean_ctor_set(x_245, 0, x_230);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Array_empty___closed__1;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(x_225, x_239, x_243, x_241, x_242, x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_220, x_10, x_240);
lean_dec(x_243);
lean_dec(x_239);
lean_dec(x_225);
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
x_257 = l_Array_isEmpty___rarg(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_228);
x_258 = l_Lean_Syntax_inhabited;
x_259 = lean_array_get(x_258, x_255, x_242);
lean_dec(x_255);
x_260 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4;
x_261 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___rarg(x_259, x_260, x_3, x_4, x_5, x_6, x_7, x_8, x_220, x_10, x_252);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_259);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_255);
lean_dec(x_220);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_266 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_266, 0, x_228);
lean_ctor_set(x_266, 1, x_254);
lean_ctor_set(x_266, 2, x_256);
if (lean_is_scalar(x_253)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_253;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_252);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_228);
lean_dec(x_220);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_268 = lean_ctor_get(x_248, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_248, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_270 = x_248;
} else {
 lean_dec_ref(x_248);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_235);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_272 = lean_ctor_get(x_238, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_238, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_274 = x_238;
} else {
 lean_dec_ref(x_238);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_276 = lean_ctor_get(x_231, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_231, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_278 = x_231;
} else {
 lean_dec_ref(x_231);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = l_Array_empty___closed__1;
x_281 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_281, 0, x_228);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_280);
if (lean_is_scalar(x_227)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_227;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_226);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_220);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_283 = lean_ctor_get(x_224, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_224, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_285 = x_224;
} else {
 lean_dec_ref(x_224);
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
uint8_t x_287; lean_object* x_288; 
lean_dec(x_13);
x_287 = 0;
x_288 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault(x_2, x_15, x_287, x_3, x_4, x_5, x_6, x_7, x_8, x_220, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_291 = x_288;
} else {
 lean_dec_ref(x_288);
 x_291 = lean_box(0);
}
x_292 = lean_ctor_get(x_289, 0);
lean_inc(x_292);
lean_dec(x_289);
if (lean_is_scalar(x_291)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_291;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_290);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_288, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_288, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_296 = x_288;
} else {
 lean_dec_ref(x_288);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
uint8_t l_Lean_Elab_Tactic_isHoleRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
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
lean_object* l_Lean_Elab_Tactic_isHoleRHS___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_isHoleRHS(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_replaceRef(x_1, x_3);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 3);
x_16 = l_Lean_replaceRef(x_13, x_15);
lean_dec(x_13);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
lean_ctor_set(x_10, 3, x_17);
lean_inc(x_2);
x_18 = l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_22, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Tactic_evalExact___spec__1(x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Meta_getMVarsNoDelayedImp(x_25, x_8, x_9, x_10, x_11, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec(x_19);
x_34 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_32);
x_35 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_33, x_34, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
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
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
x_50 = lean_ctor_get(x_10, 2);
x_51 = lean_ctor_get(x_10, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_52 = l_Lean_replaceRef(x_13, x_51);
lean_dec(x_13);
x_53 = l_Lean_replaceRef(x_52, x_51);
lean_dec(x_51);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_53);
lean_inc(x_2);
x_55 = l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_54, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 2);
lean_inc(x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = 0;
lean_inc(x_11);
lean_inc(x_54);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_61 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_59, x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_54, x_11, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
x_64 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Tactic_evalExact___spec__1(x_2, x_62, x_4, x_5, x_6, x_7, x_8, x_9, x_54, x_11, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_Meta_getMVarsNoDelayedImp(x_62, x_8, x_9, x_54, x_11, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Array_toList___rarg(x_67);
lean_dec(x_67);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
lean_dec(x_56);
x_71 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_69);
x_72 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_70, x_71, x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_54, x_11, x_68);
lean_dec(x_11);
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
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
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_55, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_55, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_82 = x_55;
} else {
 lean_dec_ref(x_55);
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
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_nat_dec_le(x_17, x_6);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_5, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_5, x_21);
lean_dec(x_5);
x_30 = l_Lean_Meta_InductionSubgoal_inhabited;
x_31 = lean_array_get(x_30, x_2, x_6);
x_32 = l_Lean_Syntax_inhabited;
x_33 = lean_array_get(x_32, x_1, x_6);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_33);
x_35 = l_Lean_Elab_Tactic_isHoleRHS(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_3);
x_37 = l_Lean_Elab_Tactic_setGoals(x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l_Lean_Elab_Tactic_evalTactic(x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_10);
x_41 = l_Lean_Elab_Tactic_done(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_7);
x_23 = x_43;
x_24 = x_42;
goto block_29;
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
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
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc(x_34);
x_52 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2___boxed), 12, 2);
lean_closure_set(x_52, 0, x_33);
lean_closure_set(x_52, 1, x_34);
x_53 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2;
x_54 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_52);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_55 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_34, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_List_append___rarg(x_7, x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_23 = x_59;
x_24 = x_57;
goto block_29;
}
else
{
uint8_t x_60; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_4, 2);
x_27 = lean_nat_add(x_6, x_26);
lean_dec(x_6);
x_5 = x_22;
x_6 = x_27;
x_7 = x_25;
x_16 = x_24;
goto _start;
}
}
else
{
lean_object* x_64; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_7);
lean_ctor_set(x_64, 1, x_16);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_7);
lean_ctor_set(x_65, 1, x_16);
return x_65;
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_nat_dec_le(x_17, x_6);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_5, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_5, x_21);
lean_dec(x_5);
x_30 = l_Lean_Meta_InductionSubgoal_inhabited;
x_31 = lean_array_get(x_30, x_2, x_6);
x_32 = l_Lean_Syntax_inhabited;
x_33 = lean_array_get(x_32, x_1, x_6);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_33);
x_35 = l_Lean_Elab_Tactic_isHoleRHS(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_3);
x_37 = l_Lean_Elab_Tactic_setGoals(x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l_Lean_Elab_Tactic_evalTactic(x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_10);
x_41 = l_Lean_Elab_Tactic_done(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_7);
x_23 = x_43;
x_24 = x_42;
goto block_29;
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
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
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc(x_34);
x_52 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2___boxed), 12, 2);
lean_closure_set(x_52, 0, x_33);
lean_closure_set(x_52, 1, x_34);
x_53 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2;
x_54 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_52);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_55 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_34, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_List_append___rarg(x_7, x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_23 = x_59;
x_24 = x_57;
goto block_29;
}
else
{
uint8_t x_60; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_4, 2);
x_27 = lean_nat_add(x_6, x_26);
lean_dec(x_6);
x_5 = x_22;
x_6 = x_27;
x_7 = x_25;
x_16 = x_24;
goto _start;
}
}
else
{
lean_object* x_64; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_7);
lean_ctor_set(x_64, 1, x_16);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_7);
lean_ctor_set(x_65, 1, x_16);
return x_65;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__3(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__3(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mistmatch on the number of subgoals produced (");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") and alternatives provided (");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ULift_HasRepr___rarg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Array_isEmpty___rarg(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_16 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_13);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__5;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
x_32 = lean_box(0);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_14);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__2(x_1, x_2, x_32, x_35, x_14, x_33, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Tactic_setGoals(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
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
x_44 = l_Array_toList___rarg(x_2);
x_45 = l_List_map___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__3(x_44);
x_46 = l_Lean_Elab_Tactic_setGoals(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction_match__1___rarg), 2, 0);
return x_2;
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
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_15 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
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
x_17 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
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
x_27 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_induction(x_23, x_24, x_25, x_26, x_27, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_18, 2);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult(x_31, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_29);
lean_dec(x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
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
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_12;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName(x_1);
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor), 11, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed), 11, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2() {
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
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alternative for '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been provided");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not needed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_24 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2___rarg(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
x_36 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__6;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
x_45 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___rarg(x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Array_isEmpty___rarg(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop(x_1, x_2, x_3, x_14, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalCases_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalCases_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalCases_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalCases_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases_match__2___rarg), 2, 0);
return x_2;
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
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeMajor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
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
x_22 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault(x_13, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
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
x_29 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = l_Lean_Meta_Cases_cases(x_18, x_27, x_28, x_29, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_25, 2);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult(x_31, x_26, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = x_31;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalCases___spec__1(x_37, x_36);
x_39 = x_38;
x_40 = l_Array_filterAux___main___at_Lean_Elab_Tactic_evalCases___spec__2(x_33, x_37, x_37);
x_41 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult(x_40, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_39);
lean_dec(x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
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
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
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
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
return x_22;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_22, 0);
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_22);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAuxHypothesisName(x_1);
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getMajor(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor), 11, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__1___boxed), 11, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2() {
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
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_CollectMVars(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Generalize(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectMVars(lean_io_mk_world());
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
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_elabMajor___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getGeneralizingFVarIds___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltCtorNames___spec__4___closed__6);
l_Lean_Elab_Tactic_RecInfo_altVars___default = _init_l_Lean_Elab_Tactic_RecInfo_altVars___default();
lean_mark_persistent(l_Lean_Elab_Tactic_RecInfo_altVars___default);
l_Lean_Elab_Tactic_RecInfo_altRHSs___default = _init_l_Lean_Elab_Tactic_RecInfo_altRHSs___default();
lean_mark_persistent(l_Lean_Elab_Tactic_RecInfo_altRHSs___default);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecFromUsingLoop___closed__1);
l_Lean_Elab_Tactic_getRecFromUsing___closed__1 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__1);
l_Lean_Elab_Tactic_getRecFromUsing___closed__2 = _init_l_Lean_Elab_Tactic_getRecFromUsing___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getRecFromUsing___closed__2);
l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__1 = _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__1();
lean_mark_persistent(l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__1);
l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2 = _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2();
lean_mark_persistent(l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__2);
l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__3 = _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__3();
lean_mark_persistent(l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__3);
l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4 = _init_l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4();
lean_mark_persistent(l_List_forInAux___main___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___spec__3___closed__4);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfoDefault___closed__4);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getRecInfo___spec__3___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___spec__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__4);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__5 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_processResult___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2);
res = l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__4);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__5 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__5);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__6 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkCasesResult_loop___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2);
res = l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
