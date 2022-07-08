// Lean compiler output
// Module: Lean.Elab.Tactic.Induction
// Imports: Init Lean.Util.CollectFVars Lean.Parser.Term Lean.Meta.RecursorInfo Lean.Meta.CollectMVars Lean.Meta.Tactic.ElimInfo Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Cases Lean.Meta.GeneralizeVars Lean.Elab.App Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Generalize
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__3;
static lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__4(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabCasesTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388_(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1;
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Tactic_elabCasesTargets___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction_checkTargets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTRAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabCasesTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__2;
lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__3;
lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__4;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_elabCasesTargets___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__3;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2;
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__2;
lean_object* l_Lean_assignExprMVar___at_Lean_Elab_Tactic_closeMainGoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___boxed__const__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__4;
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_State_argPos___default;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isHoleRHS(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addImplicitTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__3;
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltDArrow(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_Result_others___default;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__3;
extern lean_object* l_Lean_LocalContext_empty;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__7;
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandCases_x3f(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___closed__1;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__7;
static lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__4;
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__2___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1;
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__2(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___lambda__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2;
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltDArrow___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_State_targetPos___default;
static lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__3;
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isExprMVarAssigned___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object**);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__8;
lean_object* l_Std_RBNode_insert___at_Lean_Meta_ToHide_moveToHiddeProp___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___boxed(lean_object**);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_admitGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__1;
lean_object* l_Lean_Meta_generalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_State_alts___default;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_generalize___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType(lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7;
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388____closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabCasesTargets___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMVarId;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3;
lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars___boxed(lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__2;
lean_object* l_Lean_Meta_sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalCases___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__3;
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__3;
uint8_t l_Lean_LocalDecl_hasValue(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__4(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___boxed__const__1;
lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInduction_x3f(lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__9;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isHoleRHS___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier(lean_object*);
static lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_elabCasesTargets___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabCasesTargets___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Tactic_elabCasesTargets___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_Result_alts___default;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___boxed(lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isHoleRHS___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_State_insts___default;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__2;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__1;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction_checkTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__1;
extern lean_object* l_Lean_casesOnSuffix;
static lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__2;
static lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Syntax_hasArgs(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Syntax_getArg(x_4, x_3);
lean_dec(x_4);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = lean_erase_macro_scopes(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Syntax_hasArgs(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_4, x_7);
lean_dec(x_4);
x_9 = l_Lean_Syntax_isNone(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getFirstAltLhs(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars(x_1);
lean_dec(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___spec__1(x_4, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltRHS(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltDArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltDArrow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltDArrow(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_isHoleRHS___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_isHoleRHS___closed__2;
x_2 = l_Lean_Elab_Tactic_isHoleRHS___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_isHoleRHS___closed__4;
x_2 = l_Lean_Elab_Tactic_isHoleRHS___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("syntheticHole", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_isHoleRHS___closed__6;
x_2 = l_Lean_Elab_Tactic_isHoleRHS___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isHoleRHS___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_isHoleRHS___closed__6;
x_2 = l_Lean_Elab_Tactic_isHoleRHS___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isHoleRHS(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_isHoleRHS___closed__8;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Tactic_isHoleRHS___closed__10;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isHoleRHS___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_isHoleRHS(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__1;
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_2);
x_16 = lean_box(2);
x_17 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_15);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 5);
x_21 = l_Lean_replaceRef(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
lean_ctor_set(x_10, 5, x_21);
x_22 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
x_28 = lean_ctor_get(x_10, 5);
x_29 = lean_ctor_get(x_10, 6);
x_30 = lean_ctor_get(x_10, 7);
x_31 = lean_ctor_get(x_10, 8);
x_32 = lean_ctor_get(x_10, 9);
x_33 = lean_ctor_get(x_10, 10);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_34 = l_Lean_replaceRef(x_18, x_28);
lean_dec(x_28);
lean_dec(x_18);
x_35 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_30);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_35, 9, x_32);
lean_ctor_set(x_35, 10, x_33);
x_36 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35, x_11, x_12);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Elab_Tactic_setGoals(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_16, 0, x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_closeUsingOrAdmit(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("induction", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
lean_inc(x_2);
x_15 = l_Lean_Meta_getMVarDecl(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_assignExprMVar___at_Lean_Elab_Tactic_closeMainGoal___spec__1(x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_Lean_Meta_getMVarsNoDelayed(x_22, x_7, x_8, x_9, x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
lean_inc(x_27);
x_30 = lean_array_to_list(lean_box(0), x_27);
x_31 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_32 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_29, x_31, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_27);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
return x_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
x_47 = lean_ctor_get(x_9, 2);
x_48 = lean_ctor_get(x_9, 3);
x_49 = lean_ctor_get(x_9, 4);
x_50 = lean_ctor_get(x_9, 5);
x_51 = lean_ctor_get(x_9, 6);
x_52 = lean_ctor_get(x_9, 7);
x_53 = lean_ctor_get(x_9, 8);
x_54 = lean_ctor_get(x_9, 9);
x_55 = lean_ctor_get(x_9, 10);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_56 = l_Lean_replaceRef(x_1, x_50);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_47);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set(x_57, 4, x_49);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_57, 6, x_51);
lean_ctor_set(x_57, 7, x_52);
lean_ctor_set(x_57, 8, x_53);
lean_ctor_set(x_57, 9, x_54);
lean_ctor_set(x_57, 10, x_55);
lean_inc(x_2);
x_58 = l_Lean_Meta_getMVarDecl(x_2, x_7, x_8, x_57, x_10, x_11);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = 0;
lean_inc(x_10);
lean_inc(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_62, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_57, x_10, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_65);
x_67 = l_Lean_assignExprMVar___at_Lean_Elab_Tactic_closeMainGoal___spec__1(x_2, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_57, x_10, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_10);
lean_inc(x_57);
lean_inc(x_8);
lean_inc(x_7);
x_69 = l_Lean_Meta_getMVarsNoDelayed(x_65, x_7, x_8, x_57, x_10, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
lean_dec(x_59);
lean_inc(x_70);
x_73 = lean_array_to_list(lean_box(0), x_70);
x_74 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_75 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_72, x_74, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_57, x_10, x_71);
lean_dec(x_10);
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
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
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_58, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_58, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_85 = x_58;
} else {
 lean_dec_ref(x_58);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Array_append___rarg(x_3, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Array_append___rarg(x_3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
lean_inc(x_14);
x_17 = l_Lean_Elab_Tactic_isHoleRHS(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAlt___lambda__1), 13, 4);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
x_21 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1(x_16, x_14, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAlt___lambda__2___boxed), 11, 2);
lean_closure_set(x_22, 0, x_14);
lean_closure_set(x_22, 1, x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAlt___lambda__3), 12, 3);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_3);
x_24 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1(x_16, x_14, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalAlt___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalAlt___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_State_argPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_State_targetPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_State_alts___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_State_insts___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_17);
lean_inc(x_1);
x_22 = l_Lean_mkApp(x_18, x_1);
x_23 = l_Lean_Expr_bindingBody_x21(x_19);
lean_dec(x_19);
x_24 = lean_expr_instantiate1(x_23, x_1);
lean_dec(x_1);
lean_dec(x_23);
lean_ctor_set(x_14, 3, x_24);
lean_ctor_set(x_14, 2, x_22);
lean_ctor_set(x_14, 0, x_21);
x_25 = lean_st_ref_set(x_3, x_14, x_15);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
x_34 = lean_ctor_get(x_14, 2);
x_35 = lean_ctor_get(x_14, 3);
x_36 = lean_ctor_get(x_14, 4);
x_37 = lean_ctor_get(x_14, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_32, x_38);
lean_dec(x_32);
lean_inc(x_1);
x_40 = l_Lean_mkApp(x_34, x_1);
x_41 = l_Lean_Expr_bindingBody_x21(x_35);
lean_dec(x_35);
x_42 = lean_expr_instantiate1(x_41, x_1);
lean_dec(x_1);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_36);
lean_ctor_set(x_43, 5, x_37);
x_44 = lean_st_ref_set(x_3, x_43, x_15);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_bindingName_x21(x_14);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_bindingName_x21(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_bindingDomain_x21(x_14);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_bindingDomain_x21(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
x_15 = l_Lean_Meta_whnfForall(x_14, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 3);
lean_dec(x_24);
lean_inc(x_16);
lean_ctor_set(x_21, 3, x_16);
x_25 = lean_st_ref_set(x_1, x_21, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
x_32 = lean_ctor_get(x_21, 2);
x_33 = lean_ctor_get(x_21, 4);
x_34 = lean_ctor_get(x_21, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
lean_inc(x_16);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_16);
lean_ctor_set(x_35, 4, x_33);
lean_ctor_set(x_35, 5, x_34);
x_36 = lean_st_ref_set(x_1, x_35, x_22);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_Result_alts___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_Result_others___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_2, 1);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_14, x_15);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_box(0);
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_9, 5);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
lean_ctor_set_uint8(x_23, 10, x_30);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_32 = l_Lean_Elab_Term_ensureHasType(x_21, x_17, x_22, x_7, x_8, x_31, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_12, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_take(x_6, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_41);
lean_ctor_set(x_38, 1, x_43);
x_44 = lean_st_ref_set(x_6, x_38, x_39);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_apply_10(x_3, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
x_52 = lean_ctor_get(x_38, 2);
x_53 = lean_ctor_get(x_38, 3);
x_54 = lean_ctor_get(x_38, 4);
x_55 = lean_ctor_get(x_38, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_51, x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
x_59 = lean_st_ref_set(x_6, x_58, x_39);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_apply_10(x_3, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
return x_32;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_32, 0);
x_67 = lean_ctor_get(x_32, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_32);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get_uint8(x_23, 0);
x_70 = lean_ctor_get_uint8(x_23, 1);
x_71 = lean_ctor_get_uint8(x_23, 2);
x_72 = lean_ctor_get_uint8(x_23, 3);
x_73 = lean_ctor_get_uint8(x_23, 4);
x_74 = lean_ctor_get_uint8(x_23, 5);
x_75 = lean_ctor_get_uint8(x_23, 6);
x_76 = lean_ctor_get_uint8(x_23, 7);
x_77 = lean_ctor_get_uint8(x_23, 8);
x_78 = lean_ctor_get_uint8(x_23, 9);
x_79 = lean_ctor_get_uint8(x_23, 11);
x_80 = lean_ctor_get_uint8(x_23, 12);
x_81 = lean_ctor_get_uint8(x_23, 13);
lean_dec(x_23);
x_82 = 1;
x_83 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_83, 0, x_69);
lean_ctor_set_uint8(x_83, 1, x_70);
lean_ctor_set_uint8(x_83, 2, x_71);
lean_ctor_set_uint8(x_83, 3, x_72);
lean_ctor_set_uint8(x_83, 4, x_73);
lean_ctor_set_uint8(x_83, 5, x_74);
lean_ctor_set_uint8(x_83, 6, x_75);
lean_ctor_set_uint8(x_83, 7, x_76);
lean_ctor_set_uint8(x_83, 8, x_77);
lean_ctor_set_uint8(x_83, 9, x_78);
lean_ctor_set_uint8(x_83, 10, x_82);
lean_ctor_set_uint8(x_83, 11, x_79);
lean_ctor_set_uint8(x_83, 12, x_80);
lean_ctor_set_uint8(x_83, 13, x_81);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_24);
lean_ctor_set(x_84, 2, x_25);
lean_ctor_set(x_84, 3, x_26);
lean_ctor_set(x_84, 4, x_27);
lean_ctor_set(x_84, 5, x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_85 = l_Lean_Elab_Term_ensureHasType(x_21, x_17, x_22, x_7, x_8, x_84, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_get(x_12, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_st_ref_take(x_6, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 5);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_94, x_100);
lean_dec(x_94);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 6, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_95);
lean_ctor_set(x_102, 3, x_96);
lean_ctor_set(x_102, 4, x_97);
lean_ctor_set(x_102, 5, x_98);
x_103 = lean_st_ref_set(x_6, x_102, x_92);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_apply_10(x_3, x_106, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_109 = lean_ctor_get(x_85, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_85, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_111 = x_85;
} else {
 lean_dec_ref(x_85);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("insufficient number of targets for '", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getFType___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_17 = lean_st_ref_get(x_10, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__1), 12, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_25, x_22);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_27, x_22);
lean_dec(x_22);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_23);
x_29 = (uint8_t)((x_16 << 24) >> 61);
x_30 = lean_box(x_29);
switch (lean_obj_tag(x_30)) {
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
x_31 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = 0;
x_36 = lean_box(0);
lean_inc(x_7);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_34, x_35, x_36, x_7, x_8, x_9, x_10, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_11 = x_41;
goto _start;
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_15);
x_43 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_44);
x_47 = 0;
x_48 = lean_box(0);
lean_inc(x_7);
x_49 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_46, x_47, x_48, x_7, x_8, x_9, x_10, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_11 = x_53;
goto _start;
}
case 3:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_55 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
lean_inc(x_2);
x_59 = l_Lean_Meta_appendTag(x_2, x_15);
x_60 = 1;
lean_inc(x_7);
x_61 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_58, x_60, x_59, x_7, x_8, x_9, x_10, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_10, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_4, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_67, 5);
x_71 = l_Lean_Expr_mvarId_x21(x_62);
x_72 = lean_array_push(x_70, x_71);
lean_ctor_set(x_67, 5, x_72);
x_73 = lean_st_ref_set(x_4, x_67, x_68);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_11 = x_76;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
x_80 = lean_ctor_get(x_67, 2);
x_81 = lean_ctor_get(x_67, 3);
x_82 = lean_ctor_get(x_67, 4);
x_83 = lean_ctor_get(x_67, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_84 = l_Lean_Expr_mvarId_x21(x_62);
x_85 = lean_array_push(x_83, x_84);
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_80);
lean_ctor_set(x_86, 3, x_81);
lean_ctor_set(x_86, 4, x_82);
lean_ctor_set(x_86, 5, x_85);
x_87 = lean_st_ref_set(x_4, x_86, x_68);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_11 = x_90;
goto _start;
}
}
default: 
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_30);
x_92 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_2);
x_95 = l_Lean_Meta_appendTag(x_2, x_15);
lean_inc(x_7);
x_96 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_93, x_95, x_7, x_8, x_9, x_10, x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getBindingName___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_ref_get(x_10, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_st_ref_take(x_4, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_105, 4);
x_109 = l_Lean_Expr_mvarId_x21(x_97);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_push(x_108, x_110);
lean_ctor_set(x_105, 4, x_111);
x_112 = lean_st_ref_set(x_4, x_105, x_106);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_113);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_11 = x_115;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_117 = lean_ctor_get(x_105, 0);
x_118 = lean_ctor_get(x_105, 1);
x_119 = lean_ctor_get(x_105, 2);
x_120 = lean_ctor_get(x_105, 3);
x_121 = lean_ctor_get(x_105, 4);
x_122 = lean_ctor_get(x_105, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_105);
x_123 = l_Lean_Expr_mvarId_x21(x_97);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_100);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_121, x_124);
x_126 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_126, 0, x_117);
lean_ctor_set(x_126, 1, x_118);
lean_ctor_set(x_126, 2, x_119);
lean_ctor_set(x_126, 3, x_120);
lean_ctor_set(x_126, 4, x_125);
lean_ctor_set(x_126, 5, x_122);
x_127 = lean_st_ref_set(x_4, x_126, x_106);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_11 = x_130;
goto _start;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_15);
lean_dec(x_2);
x_132 = lean_st_ref_get(x_10, x_21);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_get(x_4, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 1);
lean_inc(x_138);
x_139 = lean_array_get_size(x_138);
lean_dec(x_138);
x_140 = lean_nat_dec_lt(x_137, x_139);
lean_dec(x_139);
lean_dec(x_137);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_135);
lean_dec(x_23);
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
lean_dec(x_1);
x_142 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__2;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___spec__1(x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_136);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
return x_147;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_147);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_1);
x_152 = lean_box(0);
lean_inc(x_3);
x_153 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__2(x_3, x_135, x_23, x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_136);
lean_dec(x_135);
lean_dec(x_3);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_15);
x_154 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getArgExpectedType___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_155);
x_158 = 2;
x_159 = lean_box(0);
lean_inc(x_7);
x_160 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_157, x_158, x_159, x_7, x_8, x_9, x_10, x_156);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_addNewArg(x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_11 = x_164;
goto _start;
}
}
else
{
uint8_t x_166; 
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
x_166 = !lean_is_exclusive(x_12);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_12, 0);
lean_dec(x_167);
x_168 = lean_box(0);
lean_ctor_set(x_12, 0, x_168);
return x_12;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_12, 1);
lean_inc(x_169);
lean_dec(x_12);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
uint8_t x_172; 
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
x_172 = !lean_is_exclusive(x_12);
if (x_172 == 0)
{
return x_12;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_12, 0);
x_174 = lean_ctor_get(x_12, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_12);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; 
x_14 = lean_array_uget(x_1, x_3);
x_22 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_23 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_14, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = 2;
lean_inc(x_14);
x_28 = l_Lean_Meta_setMVarKind(x_14, x_27, x_7, x_8, x_9, x_10, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_array_push(x_4, x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_15 = x_31;
x_16 = x_29;
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_4);
x_15 = x_33;
x_16 = x_32;
goto block_21;
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = 2;
lean_inc(x_14);
x_36 = l_Lean_Meta_setMVarKind(x_14, x_35, x_7, x_8, x_9, x_10, x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_array_push(x_4, x_14);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_15 = x_39;
x_16 = x_37;
goto block_21;
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = l_Lean_isExprMVarAssigned___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_push(x_4, x_13);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_19;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_13);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_11 = x_23;
goto _start;
}
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_mkConst(x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_16 = lean_infer_type(x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_st_ref_get(x_9, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_mk_ref(x_22, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_26);
x_28 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop(x_1, x_3, x_19, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_9, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_26, x_31);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 5);
lean_inc(x_35);
x_36 = lean_array_get_size(x_35);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__1(x_35, x_37, x_38, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_33, 4);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_20, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_43);
lean_dec(x_42);
x_45 = lean_ctor_get(x_33, 2);
lean_inc(x_45);
lean_dec(x_33);
x_46 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_21);
lean_ctor_set(x_49, 2, x_40);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_21);
lean_ctor_set(x_52, 2, x_40);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_43, x_43);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_43);
lean_dec(x_42);
x_55 = lean_ctor_get(x_33, 2);
lean_inc(x_55);
lean_dec(x_33);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_21);
lean_ctor_set(x_59, 2, x_40);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_21);
lean_ctor_set(x_62, 2, x_40);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__2(x_42, x_38, x_64, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_42);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_33, 2);
lean_inc(x_68);
lean_dec(x_33);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_40);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_40);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_28);
if (x_77 == 0)
{
return x_28;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_28, 0);
x_79 = lean_ctor_get(x_28, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_28);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_16);
if (x_81 == 0)
{
return x_16;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_16, 0);
x_83 = lean_ctor_get(x_16, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_16);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_13);
if (x_85 == 0)
{
return x_13;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_13, 0);
x_87 = lean_ctor_get(x_13, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_13);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_mkElimApp___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__1(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type mismatch when assigning motive", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkMVar(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_3);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_14, x_15, x_3);
x_17 = 0;
x_18 = 1;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_16, x_11, x_17, x_18, x_19, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_21);
x_23 = lean_infer_type(x_21, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_2);
x_26 = l_Lean_mkMVar(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = lean_infer_type(x_26, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_28);
lean_inc(x_24);
x_30 = l_Lean_Meta_isExprDefEqGuarded(x_24, x_28, x_4, x_5, x_6, x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_24, x_28, x_4, x_5, x_6, x_7, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_indentExpr(x_21);
x_38 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_44, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_50; lean_object* x_51; 
lean_dec(x_28);
lean_dec(x_24);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__1(x_2, x_21, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
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
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_name_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
size_t x_19; size_t x_20; 
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
lean_inc(x_2);
{
size_t _tmp_4 = x_20;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown alternative name '", 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__2(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___closed__1;
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__1(x_2, x_14, x_10, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1(x_2, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_27 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 4, x_20);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_22);
lean_ctor_set(x_28, 7, x_23);
lean_ctor_set(x_28, 8, x_24);
lean_ctor_set(x_28, 9, x_25);
lean_ctor_set(x_28, 10, x_26);
x_29 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28, x_10, x_11);
lean_dec(x_28);
return x_29;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid alternative name '", 26);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_26; uint8_t x_27; 
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_1);
x_26 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
x_27 = lean_name_eq(x_13, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_array_get_size(x_2);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_box(0);
x_14 = x_31;
goto block_25;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
x_33 = lean_box(0);
x_14 = x_33;
goto block_25;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_36 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__2(x_13, x_2, x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_14 = x_37;
goto block_25;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_10);
x_38 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_10);
x_40 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
block_25:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1(x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid occurrence of wildcard alternative, it must be the last alternative", 75);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_4, x_21);
lean_dec(x_4);
x_23 = l_Lean_instInhabitedSyntax;
x_24 = lean_array_get(x_23, x_2, x_5);
x_25 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_24);
x_26 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
x_27 = lean_name_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
lean_inc(x_15);
x_29 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1(x_24, x_1, x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_33;
x_8 = x_32;
x_17 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_nat_sub(x_3, x_21);
x_40 = lean_nat_dec_eq(x_5, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_22);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_15, 5);
x_43 = l_Lean_replaceRef(x_24, x_42);
lean_dec(x_42);
lean_dec(x_24);
lean_ctor_set(x_15, 5, x_43);
x_44 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2;
x_45 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_44, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_15);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_50 = lean_ctor_get(x_15, 0);
x_51 = lean_ctor_get(x_15, 1);
x_52 = lean_ctor_get(x_15, 2);
x_53 = lean_ctor_get(x_15, 3);
x_54 = lean_ctor_get(x_15, 4);
x_55 = lean_ctor_get(x_15, 5);
x_56 = lean_ctor_get(x_15, 6);
x_57 = lean_ctor_get(x_15, 7);
x_58 = lean_ctor_get(x_15, 8);
x_59 = lean_ctor_get(x_15, 9);
x_60 = lean_ctor_get(x_15, 10);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_15);
x_61 = l_Lean_replaceRef(x_24, x_55);
lean_dec(x_55);
lean_dec(x_24);
x_62 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_53);
lean_ctor_set(x_62, 4, x_54);
lean_ctor_set(x_62, 5, x_61);
lean_ctor_set(x_62, 6, x_56);
lean_ctor_set(x_62, 7, x_57);
lean_ctor_set(x_62, 8, x_58);
lean_ctor_set(x_62, 9, x_59);
lean_ctor_set(x_62, 10, x_60);
x_63 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2;
x_64 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_63, x_9, x_10, x_11, x_12, x_13, x_14, x_62, x_16, x_17);
lean_dec(x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
lean_inc(x_15);
x_70 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1(x_24, x_1, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_24);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_74;
x_8 = x_73;
x_17 = x_72;
goto _start;
}
else
{
uint8_t x_76; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 0);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_8);
lean_ctor_set(x_80, 1, x_17);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_8);
lean_ctor_set(x_81, 1, x_17);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3(x_1, x_2, x_12, x_12, x_13, x_12, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_BinderInfo_isExplicit(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (x_8 == 0)
{
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_2 = x_10;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__2___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_forallMetaBoundedTelescope(x_2, x_1, x_11, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_17, x_17);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_16);
x_26 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_18);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_33 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__1(x_16, x_31, x_32, x_18);
lean_dec(x_16);
x_34 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_dec(x_12);
x_41 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getMVarType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_withoutModifyingState___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__2___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__3(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; 
x_18 = lean_array_uget(x_3, x_5);
lean_inc(x_11);
lean_inc(x_18);
x_26 = l_Lean_Meta_getLocalDecl(x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
if (x_2 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_1);
x_29 = lean_nat_dec_lt(x_6, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_6);
x_19 = x_30;
x_20 = x_27;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_instInhabitedSyntax;
x_32 = lean_array_get(x_31, x_1, x_6);
x_33 = l_Lean_mkFVar(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_34 = l_Lean_Elab_Term_addLocalVarInfo(x_32, x_33, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_19 = x_38;
x_20 = x_35;
goto block_25;
}
else
{
uint8_t x_39; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_dec(x_26);
x_45 = l_Lean_LocalDecl_binderInfo(x_43);
lean_dec(x_43);
x_46 = l_Lean_BinderInfo_isExplicit(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_6);
x_19 = x_47;
x_20 = x_44;
goto block_25;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_array_get_size(x_1);
x_49 = lean_nat_dec_lt(x_6, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_18);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_6);
x_19 = x_50;
x_20 = x_44;
goto block_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lean_instInhabitedSyntax;
x_52 = lean_array_get(x_51, x_1, x_6);
x_53 = l_Lean_mkFVar(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_54 = l_Lean_Elab_Term_addLocalVarInfo(x_52, x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_44);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_6, x_56);
lean_dec(x_6);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_19 = x_58;
x_20 = x_55;
goto block_25;
}
else
{
uint8_t x_59; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
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
}
}
else
{
uint8_t x_63; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_63 = !lean_is_exclusive(x_26);
if (x_63 == 0)
{
return x_26;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
block_25:
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
x_15 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5;
x_2 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_3, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get(x_2, 7);
x_18 = lean_st_ref_get(x_3, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_28 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_14);
lean_ctor_set(x_28, 3, x_15);
lean_ctor_set(x_28, 4, x_16);
lean_ctor_set(x_28, 5, x_17);
lean_ctor_set(x_28, 6, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___boxed), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg(x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_inc(x_14);
lean_ctor_set(x_12, 1, x_14);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 2);
x_19 = lean_ctor_get(x_12, 3);
x_20 = lean_ctor_get(x_12, 4);
x_21 = lean_ctor_get(x_12, 5);
x_22 = lean_ctor_get(x_12, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
lean_inc(x_16);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set(x_23, 6, x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_24, 6);
lean_inc(x_32);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 x_33 = x_24;
} else {
 lean_dec_ref(x_24);
 x_33 = lean_box(0);
}
lean_inc(x_26);
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 7, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set(x_34, 6, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_1);
x_19 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6(x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_18, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_13 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_InfoTree_substitute(x_16, x_19);
x_21 = l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_18, x_3, x_24);
x_3 = x_26;
x_4 = x_27;
x_13 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7(x_1, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_2, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7(x_1, x_25, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8(x_1, x_36, x_37, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_2, 0, x_40);
lean_ctor_set(x_38, 0, x_2);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_2, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8(x_1, x_46, x_47, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_InfoTree_substitute(x_16, x_19);
x_21 = l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_18, x_3, x_24);
x_3 = x_26;
x_4 = x_27;
x_13 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_15 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_14);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9(x_1, x_19, x_20, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_16);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get_usize(x_2, 4);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_1);
x_32 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_28);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9(x_1, x_36, x_37, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
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
x_42 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set_usize(x_42, 4, x_30);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_1);
x_19 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11(x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_18, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_13 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_InfoTree_substitute(x_16, x_19);
x_21 = l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_18, x_3, x_24);
x_3 = x_26;
x_4 = x_27;
x_13 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12(x_1, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_2, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12(x_1, x_25, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13(x_1, x_36, x_37, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_2, 0, x_40);
lean_ctor_set(x_38, 0, x_2);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_2, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13(x_1, x_46, x_47, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_InfoTree_substitute(x_16, x_19);
x_21 = l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_18, x_3, x_24);
x_3 = x_26;
x_4 = x_27;
x_13 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_15 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_14);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14(x_1, x_19, x_20, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_16);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get_usize(x_2, 4);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_1);
x_32 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_28);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14(x_1, x_36, x_37, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
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
x_42 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set_usize(x_42, 4, x_30);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(x_5, x_6, x_7, x_8, x_9, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_9, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 4);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__5(x_31, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_9, x_35);
lean_dec(x_9);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_take(x_5, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 4);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_40, 1);
lean_dec(x_45);
x_46 = l_Std_PersistentArray_append___rarg(x_21, x_34);
lean_ctor_set(x_40, 1, x_46);
x_47 = lean_st_ref_set(x_5, x_39, x_41);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_24);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_24);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get_uint8(x_40, sizeof(void*)*2);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
x_54 = l_Std_PersistentArray_append___rarg(x_21, x_34);
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_52);
lean_ctor_set(x_39, 4, x_55);
x_56 = lean_st_ref_set(x_5, x_39, x_41);
lean_dec(x_5);
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
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
x_62 = lean_ctor_get(x_39, 2);
x_63 = lean_ctor_get(x_39, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
x_64 = lean_ctor_get_uint8(x_40, sizeof(void*)*2);
x_65 = lean_ctor_get(x_40, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_66 = x_40;
} else {
 lean_dec_ref(x_40);
 x_66 = lean_box(0);
}
x_67 = l_Std_PersistentArray_append___rarg(x_21, x_34);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 1);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_64);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_68);
x_70 = lean_st_ref_set(x_5, x_69, x_41);
lean_dec(x_5);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_24);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_74 = lean_ctor_get(x_23, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_23, 1);
lean_inc(x_75);
lean_dec(x_23);
x_76 = lean_st_ref_get(x_9, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_5, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 4);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__10(x_81, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_9, x_85);
lean_dec(x_9);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_take(x_5, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 4);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_89, 4);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_90, 1);
lean_dec(x_95);
x_96 = l_Std_PersistentArray_append___rarg(x_21, x_84);
lean_ctor_set(x_90, 1, x_96);
x_97 = lean_st_ref_set(x_5, x_89, x_91);
lean_dec(x_5);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
lean_ctor_set_tag(x_97, 1);
lean_ctor_set(x_97, 0, x_74);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_74);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get_uint8(x_90, sizeof(void*)*2);
x_103 = lean_ctor_get(x_90, 0);
lean_inc(x_103);
lean_dec(x_90);
x_104 = l_Std_PersistentArray_append___rarg(x_21, x_84);
x_105 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_102);
lean_ctor_set(x_89, 4, x_105);
x_106 = lean_st_ref_set(x_5, x_89, x_91);
lean_dec(x_5);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
 lean_ctor_set_tag(x_109, 1);
}
lean_ctor_set(x_109, 0, x_74);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_110 = lean_ctor_get(x_89, 0);
x_111 = lean_ctor_get(x_89, 1);
x_112 = lean_ctor_get(x_89, 2);
x_113 = lean_ctor_get(x_89, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_89);
x_114 = lean_ctor_get_uint8(x_90, sizeof(void*)*2);
x_115 = lean_ctor_get(x_90, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_116 = x_90;
} else {
 lean_dec_ref(x_90);
 x_116 = lean_box(0);
}
x_117 = l_Std_PersistentArray_append___rarg(x_21, x_84);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 1);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_114);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_110);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_119, 2, x_112);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set(x_119, 4, x_118);
x_120 = lean_st_ref_set(x_5, x_119, x_91);
lean_dec(x_5);
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
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_74);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__1(x_1, x_2, x_3, x_4, x_5, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; uint8_t x_17; 
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier(x_2);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVars(x_2);
lean_dec(x_2);
x_15 = lean_array_get_size(x_3);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
if (x_13 == 0)
{
uint8_t x_25; 
x_25 = 1;
x_17 = x_25;
goto block_24;
}
else
{
uint8_t x_26; 
x_26 = 0;
x_17 = x_26;
goto block_24;
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_box(x_17);
x_19 = lean_box_usize(x_16);
x_20 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___boxed__const__1;
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___lambda__1___boxed), 14, 5);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg), 11, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__2(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__1(x_1, x_16, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_ContextInfo_save___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__7(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__8(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__9(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__12(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__13(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PersistentArray_mapMAux___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__14(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PersistentArray_mapM___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___lambda__1(x_1, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_Lean_instInhabitedMVarId;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_7);
lean_dec(x_7);
x_13 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_array_get_size(x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_findIdx_x3f_loop___rarg(x_10, x_13, x_14, x_15, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_11);
x_17 = l_Array_append___rarg(x_11, x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1;
x_22 = lean_array_get(x_21, x_10, x_20);
x_23 = lean_array_push(x_11, x_22);
x_24 = l_Array_eraseIdx___rarg(x_10, x_20);
lean_dec(x_20);
lean_ctor_set(x_8, 1, x_23);
lean_ctor_set(x_8, 0, x_24);
lean_inc(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_8);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_31 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_7);
lean_dec(x_7);
x_32 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_array_get_size(x_29);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_findIdx_x3f_loop___rarg(x_29, x_32, x_33, x_34, lean_box(0));
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
lean_inc(x_29);
lean_inc(x_30);
x_36 = l_Array_append___rarg(x_30, x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1;
x_42 = lean_array_get(x_41, x_29, x_40);
x_43 = lean_array_push(x_30, x_42);
x_44 = l_Array_eraseIdx___rarg(x_29, x_40);
lean_dec(x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_inc(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_4, x_47);
x_4 = x_48;
x_5 = x_46;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_append___rarg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1(x_4, x_2, x_9, x_10, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Array_append___rarg(x_15, x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
return x_17;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_ElimApp_reorderAlts___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_reorderAlts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_ElimApp_reorderAlts(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Syntax_isNone(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Elab_Tactic_evalTacticAt(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_tryClear(x_4, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_4 = x_18;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_admitGoal(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_14;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Elab_Tactic_evalAlt(x_14, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_2 = x_15;
x_3 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("alternative '", 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not needed", 15);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_to_list(lean_box(0), x_1);
if (x_15 == 0)
{
uint8_t x_286; 
x_286 = 1;
x_27 = x_286;
goto block_285;
}
else
{
uint8_t x_287; 
x_287 = 0;
x_27 = x_287;
goto block_285;
}
block_285:
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_29 = l_Lean_Meta_introNCore(x_2, x_3, x_26, x_27, x_28, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_34);
x_35 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo(x_34, x_4, x_33, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_box(0);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_39 = l_Lean_Meta_Cases_unifyEqs_x3f(x_5, x_34, x_37, x_38, x_21, x_22, x_23, x_24, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_30);
lean_dec(x_8);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_42, 0, x_7);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_46, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_41);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_dec(x_49);
x_50 = lean_box(x_9);
lean_ctor_set(x_30, 1, x_50);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_39, 0, x_30);
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_box(x_9);
lean_ctor_set(x_30, 1, x_52);
lean_ctor_set(x_30, 0, x_8);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_30);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
lean_free_object(x_30);
x_54 = lean_ctor_get(x_40, 0);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_dec(x_39);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = 1;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_59 = l_Lean_Meta_introNCore(x_56, x_10, x_57, x_28, x_58, x_21, x_22, x_23, x_24, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_ctor_get(x_60, 0);
lean_dec(x_64);
x_65 = lean_array_get_size(x_11);
x_66 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_67 = 0;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(x_11, x_66, x_67, x_63, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_61);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_71 = l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(x_12, x_69, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_70);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = l_List_isEmpty___rarg(x_73);
if (x_75 == 0)
{
lean_object* x_76; 
lean_free_object(x_71);
lean_dec(x_8);
lean_dec(x_7);
x_76 = l_List_forIn_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__4(x_4, x_73, x_13, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_74);
if (lean_obj_tag(x_76) == 0)
{
if (x_9 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_box(x_14);
lean_ctor_set(x_60, 1, x_79);
lean_ctor_set(x_60, 0, x_78);
lean_ctor_set(x_76, 0, x_60);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
x_82 = lean_box(x_14);
lean_ctor_set(x_60, 1, x_82);
lean_ctor_set(x_60, 0, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_60);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_box(x_58);
lean_ctor_set(x_60, 1, x_86);
lean_ctor_set(x_60, 0, x_85);
lean_ctor_set(x_76, 0, x_60);
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_box(x_58);
lean_ctor_set(x_60, 1, x_89);
lean_ctor_set(x_60, 0, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_60);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_free_object(x_60);
x_91 = !lean_is_exclusive(x_76);
if (x_91 == 0)
{
return x_76;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_76, 0);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_76);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_73);
lean_dec(x_13);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_71);
lean_free_object(x_60);
lean_dec(x_8);
x_95 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_95, 0, x_7);
x_96 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_99, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_74);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_101 = lean_box(x_9);
lean_ctor_set(x_60, 1, x_101);
lean_ctor_set(x_60, 0, x_8);
lean_ctor_set(x_71, 0, x_60);
return x_71;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_71, 0);
x_103 = lean_ctor_get(x_71, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_71);
x_104 = l_List_isEmpty___rarg(x_102);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_8);
lean_dec(x_7);
x_105 = l_List_forIn_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__4(x_4, x_102, x_13, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_103);
if (lean_obj_tag(x_105) == 0)
{
if (x_9 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_box(x_14);
lean_ctor_set(x_60, 1, x_109);
lean_ctor_set(x_60, 0, x_106);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_60);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_105, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_113 = x_105;
} else {
 lean_dec_ref(x_105);
 x_113 = lean_box(0);
}
x_114 = lean_box(x_58);
lean_ctor_set(x_60, 1, x_114);
lean_ctor_set(x_60, 0, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_60);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_60);
x_116 = lean_ctor_get(x_105, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_118 = x_105;
} else {
 lean_dec_ref(x_105);
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
lean_dec(x_102);
lean_dec(x_13);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_60);
lean_dec(x_8);
x_120 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_120, 0, x_7);
x_121 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_124, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_103);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_126 = lean_box(x_9);
lean_ctor_set(x_60, 1, x_126);
lean_ctor_set(x_60, 0, x_8);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_60);
lean_ctor_set(x_127, 1, x_103);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_60);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_71);
if (x_128 == 0)
{
return x_71;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_71, 0);
x_130 = lean_ctor_get(x_71, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_71);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_free_object(x_60);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_132 = !lean_is_exclusive(x_68);
if (x_132 == 0)
{
return x_68;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_68, 0);
x_134 = lean_ctor_get(x_68, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_68);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_60, 1);
lean_inc(x_136);
lean_dec(x_60);
x_137 = lean_array_get_size(x_11);
x_138 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_139 = 0;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_140 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(x_11, x_138, x_139, x_136, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_61);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_143 = l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(x_12, x_141, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = l_List_isEmpty___rarg(x_144);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_7);
x_148 = l_List_forIn_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__4(x_4, x_144, x_13, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_145);
if (lean_obj_tag(x_148) == 0)
{
if (x_9 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_box(x_14);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_157 = x_148;
} else {
 lean_dec_ref(x_148);
 x_157 = lean_box(0);
}
x_158 = lean_box(x_58);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_148, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_148, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_163 = x_148;
} else {
 lean_dec_ref(x_148);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_dec(x_144);
lean_dec(x_13);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_146);
lean_dec(x_8);
x_165 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_165, 0, x_7);
x_166 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_167 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
x_169 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_169, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_145);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_171 = lean_box(x_9);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_8);
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
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_174 = lean_ctor_get(x_143, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_143, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_176 = x_143;
} else {
 lean_dec_ref(x_143);
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
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_178 = lean_ctor_get(x_140, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_140, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_180 = x_140;
} else {
 lean_dec_ref(x_140);
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
}
else
{
uint8_t x_182; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_182 = !lean_is_exclusive(x_59);
if (x_182 == 0)
{
return x_59;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_59, 0);
x_184 = lean_ctor_get(x_59, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_59);
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
uint8_t x_186; 
lean_free_object(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_186 = !lean_is_exclusive(x_39);
if (x_186 == 0)
{
return x_39;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_39, 0);
x_188 = lean_ctor_get(x_39, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_39);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_free_object(x_30);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_35);
if (x_190 == 0)
{
return x_35;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_35, 0);
x_192 = lean_ctor_get(x_35, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_35);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_30, 0);
x_195 = lean_ctor_get(x_30, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_30);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_195);
x_196 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo(x_195, x_4, x_194, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_31);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_box(0);
x_199 = lean_box(0);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_200 = l_Lean_Meta_Cases_unifyEqs_x3f(x_5, x_195, x_198, x_199, x_21, x_22, x_23, x_24, x_197);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_8);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_203, 0, x_7);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_207, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_202);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_210 = x_200;
} else {
 lean_dec_ref(x_200);
 x_210 = lean_box(0);
}
x_211 = lean_box(x_9);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_8);
lean_ctor_set(x_212, 1, x_211);
if (lean_is_scalar(x_210)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_210;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_209);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_201, 0);
lean_inc(x_214);
lean_dec(x_201);
x_215 = lean_ctor_get(x_200, 1);
lean_inc(x_215);
lean_dec(x_200);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_box(0);
x_218 = 1;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_219 = l_Lean_Meta_introNCore(x_216, x_10, x_217, x_28, x_218, x_21, x_22, x_23, x_24, x_215);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_array_get_size(x_11);
x_225 = lean_usize_of_nat(x_224);
lean_dec(x_224);
x_226 = 0;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_227 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(x_11, x_225, x_226, x_222, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_221);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_230 = l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(x_12, x_228, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = l_List_isEmpty___rarg(x_231);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_233);
lean_dec(x_8);
lean_dec(x_7);
x_235 = l_List_forIn_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__4(x_4, x_231, x_13, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_232);
if (lean_obj_tag(x_235) == 0)
{
if (x_9 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_box(x_14);
if (lean_is_scalar(x_223)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_223;
}
lean_ctor_set(x_240, 0, x_236);
lean_ctor_set(x_240, 1, x_239);
if (lean_is_scalar(x_238)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_238;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_237);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_235, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_235, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_244 = x_235;
} else {
 lean_dec_ref(x_235);
 x_244 = lean_box(0);
}
x_245 = lean_box(x_218);
if (lean_is_scalar(x_223)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_223;
}
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_245);
if (lean_is_scalar(x_244)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_244;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_243);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_223);
x_248 = lean_ctor_get(x_235, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_235, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_250 = x_235;
} else {
 lean_dec_ref(x_235);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_dec(x_231);
lean_dec(x_13);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_233);
lean_dec(x_223);
lean_dec(x_8);
x_252 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_252, 0, x_7);
x_253 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_254 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4;
x_256 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_256, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_232);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_258 = lean_box(x_9);
if (lean_is_scalar(x_223)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_223;
}
lean_ctor_set(x_259, 0, x_8);
lean_ctor_set(x_259, 1, x_258);
if (lean_is_scalar(x_233)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_233;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_232);
return x_260;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_223);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_261 = lean_ctor_get(x_230, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_230, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_263 = x_230;
} else {
 lean_dec_ref(x_230);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_223);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_265 = lean_ctor_get(x_227, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_227, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_267 = x_227;
} else {
 lean_dec_ref(x_227);
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
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_269 = lean_ctor_get(x_219, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_219, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_271 = x_219;
} else {
 lean_dec_ref(x_219);
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
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_273 = lean_ctor_get(x_200, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_200, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_275 = x_200;
} else {
 lean_dec_ref(x_200);
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
lean_dec(x_195);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_277 = lean_ctor_get(x_196, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_196, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_279 = x_196;
} else {
 lean_dec_ref(x_196);
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
}
else
{
uint8_t x_281; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_281 = !lean_is_exclusive(x_29);
if (x_281 == 0)
{
return x_29;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_29, 0);
x_283 = lean_ctor_get(x_29, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_29);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("too many variable names provided at alternative '", 49);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', #", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" provided, but #", 16);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" expected", 9);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_get_size(x_1);
x_27 = lean_nat_dec_lt(x_16, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_16);
x_28 = lean_box(0);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_28, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_7);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_7);
x_31 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Nat_repr(x_26);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__6;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Nat_repr(x_16);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__8;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = 2;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_48 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_46, x_47, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_49, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_50);
lean_dec(x_49);
return x_51;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has not been provided", 23);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_9);
x_24 = lean_box(0);
x_25 = 0;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_26 = l_Lean_Meta_introNCore(x_1, x_2, x_24, x_25, x_25, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_box(0);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_32 = l_Lean_Meta_Cases_unifyEqs_x3f(x_3, x_29, x_30, x_31, x_19, x_20, x_21, x_22, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(x_13);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_32, 0, x_39);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_box(x_13);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_50 = l_Lean_Meta_introNCore(x_48, x_4, x_24, x_25, x_49, x_19, x_20, x_21, x_22, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_array_get_size(x_5);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = 0;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(x_5, x_55, x_56, x_53, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_60 = l_Lean_Elab_Tactic_ElimApp_evalAlts_applyPreTac(x_6, x_58, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_array_get_size(x_7);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_lt(x_65, x_64);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
x_67 = l_List_redLength___rarg(x_62);
x_68 = lean_mk_empty_array_with_capacity(x_67);
lean_dec(x_67);
x_69 = l_List_toArrayAux___rarg(x_62, x_68);
x_70 = l_Array_append___rarg(x_12, x_69);
x_71 = lean_box(x_13);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_10);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_60, 0, x_74);
return x_60;
}
else
{
uint8_t x_75; 
x_75 = l_List_isEmpty___rarg(x_62);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_60);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_8);
x_77 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = 2;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_82 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_80, x_81, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_63);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2(x_62, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_83);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = lean_box(x_13);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_84, 0, x_90);
return x_84;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_box(x_13);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_10);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_10);
x_97 = !lean_is_exclusive(x_84);
if (x_97 == 0)
{
return x_84;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_84, 0);
x_99 = lean_ctor_get(x_84, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_84);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_62);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
x_101 = lean_box(x_13);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_12);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_10);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_60, 0, x_104);
return x_60;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_60, 0);
x_106 = lean_ctor_get(x_60, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_60);
x_107 = lean_array_get_size(x_7);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_lt(x_108, x_107);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
x_110 = l_List_redLength___rarg(x_105);
x_111 = lean_mk_empty_array_with_capacity(x_110);
lean_dec(x_110);
x_112 = l_List_toArrayAux___rarg(x_105, x_111);
x_113 = l_Array_append___rarg(x_12, x_112);
x_114 = lean_box(x_13);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_10);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_106);
return x_118;
}
else
{
uint8_t x_119; 
x_119 = l_List_isEmpty___rarg(x_105);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_120, 0, x_8);
x_121 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = 2;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_126 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_124, x_125, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_106);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2(x_105, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_127);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(x_13);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_12);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_10);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_129);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_12);
lean_dec(x_10);
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_138 = x_128;
} else {
 lean_dec_ref(x_128);
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
lean_dec(x_105);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
x_140 = lean_box(x_13);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_12);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_10);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_106);
return x_144;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_145 = !lean_is_exclusive(x_60);
if (x_145 == 0)
{
return x_60;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_60, 0);
x_147 = lean_ctor_get(x_60, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_60);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_149 = !lean_is_exclusive(x_57);
if (x_149 == 0)
{
return x_57;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_57, 0);
x_151 = lean_ctor_get(x_57, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_57);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_153 = !lean_is_exclusive(x_50);
if (x_153 == 0)
{
return x_50;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_50, 0);
x_155 = lean_ctor_get(x_50, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_50);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
x_157 = !lean_is_exclusive(x_32);
if (x_157 == 0)
{
return x_32;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_32, 0);
x_159 = lean_ctor_get(x_32, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_32);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_26);
if (x_161 == 0)
{
return x_26;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_26, 0);
x_163 = lean_ctor_get(x_26, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_26);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_14, 0);
lean_inc(x_165);
lean_dec(x_14);
lean_inc(x_165);
x_166 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_165);
x_167 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_altHasExplicitModifier(x_165);
if (x_11 == 0)
{
uint8_t x_272; 
x_272 = 0;
x_168 = x_272;
goto block_271;
}
else
{
uint8_t x_273; 
x_273 = 1;
x_168 = x_273;
goto block_271;
}
block_271:
{
uint8_t x_169; 
if (x_167 == 0)
{
uint8_t x_269; 
x_269 = 0;
x_169 = x_269;
goto block_268;
}
else
{
uint8_t x_270; 
x_270 = 1;
x_169 = x_270;
goto block_268;
}
block_268:
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_21);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_21, 5);
x_172 = l_Lean_replaceRef(x_165, x_171);
lean_dec(x_171);
lean_ctor_set(x_21, 5, x_172);
if (x_169 == 0)
{
lean_object* x_173; 
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_2);
lean_inc(x_1);
x_173 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields(x_1, x_2, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(x_166, x_1, x_2, x_165, x_3, x_168, x_8, x_9, x_13, x_4, x_5, x_6, x_12, x_11, x_167, x_174, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_175);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_10);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_176, 0, x_183);
return x_176;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_176, 0);
x_185 = lean_ctor_get(x_176, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_10);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_185);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_10);
x_192 = !lean_is_exclusive(x_176);
if (x_192 == 0)
{
return x_176;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_176, 0);
x_194 = lean_ctor_get(x_176, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_176);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_21);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_173);
if (x_196 == 0)
{
return x_173;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_173, 0);
x_198 = lean_ctor_get(x_173, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_173);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; 
lean_inc(x_2);
x_200 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(x_166, x_1, x_2, x_165, x_3, x_168, x_8, x_9, x_13, x_4, x_5, x_6, x_12, x_11, x_167, x_2, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_10);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_200, 0, x_207);
return x_200;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_200, 0);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_200);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_10);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_209);
return x_215;
}
}
else
{
uint8_t x_216; 
lean_dec(x_10);
x_216 = !lean_is_exclusive(x_200);
if (x_216 == 0)
{
return x_200;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_200, 0);
x_218 = lean_ctor_get(x_200, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_200);
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
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_220 = lean_ctor_get(x_21, 0);
x_221 = lean_ctor_get(x_21, 1);
x_222 = lean_ctor_get(x_21, 2);
x_223 = lean_ctor_get(x_21, 3);
x_224 = lean_ctor_get(x_21, 4);
x_225 = lean_ctor_get(x_21, 5);
x_226 = lean_ctor_get(x_21, 6);
x_227 = lean_ctor_get(x_21, 7);
x_228 = lean_ctor_get(x_21, 8);
x_229 = lean_ctor_get(x_21, 9);
x_230 = lean_ctor_get(x_21, 10);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_21);
x_231 = l_Lean_replaceRef(x_165, x_225);
lean_dec(x_225);
x_232 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_232, 0, x_220);
lean_ctor_set(x_232, 1, x_221);
lean_ctor_set(x_232, 2, x_222);
lean_ctor_set(x_232, 3, x_223);
lean_ctor_set(x_232, 4, x_224);
lean_ctor_set(x_232, 5, x_231);
lean_ctor_set(x_232, 6, x_226);
lean_ctor_set(x_232, 7, x_227);
lean_ctor_set(x_232, 8, x_228);
lean_ctor_set(x_232, 9, x_229);
lean_ctor_set(x_232, 10, x_230);
if (x_169 == 0)
{
lean_object* x_233; 
lean_inc(x_22);
lean_inc(x_232);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_2);
lean_inc(x_1);
x_233 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getNumExplicitFields(x_1, x_2, x_19, x_20, x_232, x_22, x_23);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(x_166, x_1, x_2, x_165, x_3, x_168, x_8, x_9, x_13, x_4, x_5, x_6, x_12, x_11, x_167, x_234, x_15, x_16, x_17, x_18, x_19, x_20, x_232, x_22, x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
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
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_10);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
if (lean_is_scalar(x_239)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_239;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_238);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_10);
x_246 = lean_ctor_get(x_236, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_236, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_248 = x_236;
} else {
 lean_dec_ref(x_236);
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
lean_dec(x_232);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_233, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_233, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_252 = x_233;
} else {
 lean_dec_ref(x_233);
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
else
{
lean_object* x_254; 
lean_inc(x_2);
x_254 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(x_166, x_1, x_2, x_165, x_3, x_168, x_8, x_9, x_13, x_4, x_5, x_6, x_12, x_11, x_167, x_2, x_15, x_16, x_17, x_18, x_19, x_20, x_232, x_22, x_23);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_10);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_261);
if (lean_is_scalar(x_257)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_257;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_256);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_10);
x_264 = lean_ctor_get(x_254, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_254, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_266 = x_254;
} else {
 lean_dec_ref(x_254);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_2);
x_4 = lean_name_eq(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_1);
x_3 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__5___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_10, x_9);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_array_uget(x_8, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_24);
lean_inc(x_1);
x_30 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields(x_1, x_24, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_24);
x_33 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__4___boxed), 2, 1);
lean_closure_set(x_33, 0, x_24);
x_34 = lean_array_get_size(x_26);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_34);
x_36 = l_Array_findIdx_x3f_loop___rarg(x_26, x_33, x_34, x_35, lean_box(0));
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___closed__1;
x_38 = l_Array_findIdx_x3f_loop___rarg(x_26, x_37, x_34, x_35, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = 0;
x_41 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(x_25, x_31, x_4, x_5, x_6, x_2, x_3, x_24, x_7, x_26, x_40, x_28, x_41, x_39, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = 1;
x_53 = lean_usize_add(x_10, x_52);
x_10 = x_53;
x_11 = x_51;
x_20 = x_50;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = l_Lean_instInhabitedSyntax;
x_62 = lean_array_get(x_61, x_26, x_60);
lean_dec(x_60);
lean_ctor_set(x_38, 0, x_62);
x_63 = 1;
x_64 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(x_25, x_31, x_4, x_5, x_6, x_2, x_3, x_24, x_7, x_26, x_63, x_28, x_64, x_38, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; 
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = 1;
x_76 = lean_usize_add(x_10, x_75);
x_10 = x_76;
x_11 = x_74;
x_20 = x_73;
goto _start;
}
}
else
{
uint8_t x_78; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
return x_65;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_38, 0);
lean_inc(x_82);
lean_dec(x_38);
x_83 = l_Lean_instInhabitedSyntax;
x_84 = lean_array_get(x_83, x_26, x_82);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = 1;
x_87 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(x_25, x_31, x_4, x_5, x_6, x_2, x_3, x_24, x_7, x_26, x_86, x_28, x_87, x_85, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
lean_dec(x_89);
x_96 = 1;
x_97 = lean_usize_add(x_10, x_96);
x_10 = x_97;
x_11 = x_95;
x_20 = x_94;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_99 = lean_ctor_get(x_88, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_101 = x_88;
} else {
 lean_dec_ref(x_88);
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
}
}
else
{
uint8_t x_103; 
lean_dec(x_34);
x_103 = !lean_is_exclusive(x_36);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_36, 0);
x_105 = l_Lean_instInhabitedSyntax;
x_106 = lean_array_get(x_105, x_26, x_104);
x_107 = l_Array_eraseIdx___rarg(x_26, x_104);
lean_dec(x_104);
lean_ctor_set(x_36, 0, x_106);
x_108 = 0;
x_109 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_110 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(x_25, x_31, x_4, x_5, x_6, x_2, x_3, x_24, x_7, x_107, x_108, x_28, x_109, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
lean_ctor_set(x_110, 0, x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; size_t x_120; size_t x_121; 
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
lean_dec(x_110);
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
lean_dec(x_111);
x_120 = 1;
x_121 = lean_usize_add(x_10, x_120);
x_10 = x_121;
x_11 = x_119;
x_20 = x_118;
goto _start;
}
}
else
{
uint8_t x_123; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
return x_110;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_110, 0);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_110);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_36, 0);
lean_inc(x_127);
lean_dec(x_36);
x_128 = l_Lean_instInhabitedSyntax;
x_129 = lean_array_get(x_128, x_26, x_127);
x_130 = l_Array_eraseIdx___rarg(x_26, x_127);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_129);
x_132 = 0;
x_133 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(x_25, x_31, x_4, x_5, x_6, x_2, x_3, x_24, x_7, x_130, x_132, x_28, x_133, x_131, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; 
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
lean_dec(x_135);
x_142 = 1;
x_143 = lean_usize_add(x_10, x_142);
x_10 = x_143;
x_11 = x_141;
x_20 = x_140;
goto _start;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_145 = lean_ctor_get(x_134, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_147 = x_134;
} else {
 lean_dec_ref(x_134);
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
}
}
else
{
uint8_t x_149; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_30);
if (x_149 == 0)
{
return x_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_30, 0);
x_151 = lean_ctor_get(x_30, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_30);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_6);
x_8 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
if (x_9 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_4, x_6);
x_2 = x_11;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_to_list(lean_box(0), x_1);
x_13 = l_Lean_Elab_Tactic_setGoals(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unused alternative", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = l_Array_isEmpty___rarg(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = l_Lean_instInhabitedSyntax;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__3;
x_18 = 2;
x_19 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1(x_1, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1(x_1, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = l_Lean_Elab_Tactic_ElimApp_reorderAlts(x_2, x_4);
x_18 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___closed__1;
lean_inc(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_get_size(x_17);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5(x_1, x_3, x_4, x_5, x_6, x_7, x_23, x_17, x_21, x_22, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2(x_31, x_30, x_32, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_array_get_size(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2(x_36, x_23, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_37, x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_37);
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2(x_36, x_23, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
return x_44;
}
else
{
size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__6(x_35, x_22, x_45, x_23);
lean_dec(x_35);
x_47 = lean_box(0);
x_48 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2(x_36, x_46, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_unbox(x_6);
lean_dec(x_6);
x_27 = lean_unbox(x_9);
lean_dec(x_9);
x_28 = lean_unbox(x_14);
lean_dec(x_14);
x_29 = lean_unbox(x_15);
lean_dec(x_15);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_26, x_7, x_8, x_27, x_10, x_11, x_12, x_13, x_28, x_29, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_unbox(x_6);
lean_dec(x_6);
x_27 = lean_unbox(x_9);
lean_dec(x_9);
x_28 = lean_unbox(x_14);
lean_dec(x_14);
x_29 = lean_unbox(x_15);
lean_dec(x_15);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_26, x_7, x_8, x_27, x_10, x_11, x_12, x_13, x_28, x_29, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_12);
lean_dec(x_11);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_unbox(x_11);
lean_dec(x_11);
x_25 = lean_unbox(x_13);
lean_dec(x_13);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24, x_12, x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__5___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__5(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_22 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_15);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames(x_2, x_4, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_5);
x_23 = l_Lean_Elab_Tactic_ElimApp_evalAlts_go(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_ElimApp_evalAlts_go), 16, 7);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_6);
lean_closure_set(x_24, 5, x_7);
lean_closure_set(x_24, 6, x_8);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_ElimApp_evalAlts___lambda__1___boxed), 11, 1);
lean_closure_set(x_25, 0, x_5);
x_26 = l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__3(x_24, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_19);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_ElimApp_evalAlts___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ElimApp_evalAlts___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Tactic_ElimApp_evalAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2;
x_2 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_15 = lean_ctor_get(x_8, 5);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_16);
x_17 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3;
x_31 = lean_st_ref_get(x_9, x_10);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_18 = x_36;
x_19 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_18 = x_41;
x_19 = x_40;
goto block_30;
}
block_30:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(x_12, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_12);
x_23 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_17, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(x_12, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_27);
lean_dec(x_12);
return x_29;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
x_44 = lean_ctor_get(x_8, 2);
x_45 = lean_ctor_get(x_8, 3);
x_46 = lean_ctor_get(x_8, 4);
x_47 = lean_ctor_get(x_8, 5);
x_48 = lean_ctor_get(x_8, 6);
x_49 = lean_ctor_get(x_8, 7);
x_50 = lean_ctor_get(x_8, 8);
x_51 = lean_ctor_get(x_8, 9);
x_52 = lean_ctor_get(x_8, 10);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_53 = l_Lean_replaceRef(x_1, x_47);
lean_dec(x_47);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set(x_54, 4, x_46);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_48);
lean_ctor_set(x_54, 7, x_49);
lean_ctor_set(x_54, 8, x_50);
lean_ctor_set(x_54, 9, x_51);
lean_ctor_set(x_54, 10, x_52);
x_55 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3;
x_69 = lean_st_ref_get(x_9, x_10);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = 0;
x_56 = x_74;
x_57 = x_73;
goto block_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_54, x_9, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_56 = x_79;
x_57 = x_78;
goto block_68;
}
block_68:
{
if (x_56 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(x_12, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_54, x_9, x_57);
lean_dec(x_12);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_inc(x_12);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_12);
x_61 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_55, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_54, x_9, x_57);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(x_12, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_54, x_9, x_66);
lean_dec(x_65);
lean_dec(x_12);
return x_67;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = l_Std_RBNode_insert___at_Lean_Meta_ToHide_moveToHiddeProp___spec__1(x_2, x_1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unnecessary 'generalizing' argument, variable '", 47);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is generalized automatically", 30);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_2, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_2);
x_16 = l_Lean_mkFVar(x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("variable cannot be generalized because target depends on it", 59);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_3, x_5);
x_19 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2(x_18, x_6, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
x_6 = x_24;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_6);
x_32 = l_Lean_mkFVar(x_18);
x_33 = l_Lean_indentExpr(x_32);
x_34 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_2, x_4);
x_18 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2(x_17, x_5, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_5 = x_23;
x_14 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_5);
x_31 = l_Lean_mkFVar(x_17);
x_32 = l_Lean_indentExpr(x_31);
x_33 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_2, x_16, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
lean_inc(x_8);
lean_inc(x_18);
x_21 = l_Lean_Meta_getFVarSetToGeneralize(x_2, x_18, x_20, x_8, x_9, x_10, x_11, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_14);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__2(x_18, x_14, x_25, x_26, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Std_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(x_28);
lean_inc(x_8);
x_31 = l_Lean_Meta_sortFVarIds(x_30, x_8, x_9, x_10, x_11, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_revert(x_3, x_32, x_20, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_array_get_size(x_38);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_array_get_size(x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = lean_array_get_size(x_46);
lean_dec(x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
return x_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_27, 0);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_27);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
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
x_60 = !lean_is_exclusive(x_17);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___boxed), 12, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_1);
x_14 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__2(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_3 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___closed__1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getNumArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_box(2);
x_12 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
lean_inc(x_1);
x_14 = l_Lean_Syntax_setArg(x_1, x_7, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_8, x_3, x_14);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1(x_1, x_8, x_9, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_isMultiAlt(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_array_push(x_4, x_6);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Array_append___rarg(x_4, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__1(x_2, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__2(x_2, x_10, x_9, x_13);
lean_dec(x_2);
x_15 = lean_box(2);
x_16 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_setArg(x_1, x_18, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInduction_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_3, x_5);
lean_dec(x_3);
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1;
x_12 = lean_array_push(x_11, x_10);
x_13 = lean_box(2);
x_14 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_12);
x_16 = l_Lean_Syntax_setArg(x_1, x_2, x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1;
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_box(2);
x_21 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
x_23 = l_Lean_Syntax_setArg(x_1, x_2, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandCases_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_3, x_5);
lean_dec(x_3);
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInductionAlts_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1;
x_12 = lean_array_push(x_11, x_10);
x_13 = lean_box(2);
x_14 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_12);
x_16 = l_Lean_Syntax_setArg(x_1, x_2, x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1;
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_box(2);
x_21 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3;
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
x_23 = l_Lean_Syntax_setArg(x_1, x_2, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("more than one wildcard alternative '| _ => ...' used", 52);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__1;
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_box(x_2);
x_16 = lean_apply_11(x_13, x_15, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__3;
x_18 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wildcard alternative must not specify variable names", 52);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_box(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_uget(x_1, x_3);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName(x_17);
x_19 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
size_t x_21; size_t x_22; 
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_17);
x_24 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltVarNames(x_17);
x_25 = l_Array_isEmpty___rarg(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__2;
x_27 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__1(x_17, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_17);
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
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2(x_17, x_4, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_45 = lean_unbox(x_42);
lean_dec(x_42);
x_3 = x_44;
x_4 = x_45;
x_13 = x_41;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Syntax_isNone(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfInductionAlts(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = 0;
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1(x_1, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("major premise type is not an inductive type ", 44);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = lean_whnf(x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_18);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_9, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_environment_find(x_26, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_22);
x_28 = l_Lean_indentExpr(x_18);
x_29 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_33, x_12, x_32, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_7);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
if (lean_obj_tag(x_35) == 5)
{
lean_object* x_36; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_22, 0, x_36);
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_35);
lean_free_object(x_22);
x_37 = l_Lean_indentExpr(x_18);
x_38 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_42, x_12, x_41, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_7);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_environment_find(x_46, x_21);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = l_Lean_indentExpr(x_18);
x_49 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_54 = l_Lean_Meta_throwTacticEx___rarg(x_53, x_12, x_52, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_7);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
if (lean_obj_tag(x_55) == 5)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_45);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_55);
x_58 = l_Lean_indentExpr(x_18);
x_59 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_64 = l_Lean_Meta_throwTacticEx___rarg(x_63, x_12, x_62, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_7);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_20);
x_65 = l_Lean_indentExpr(x_18);
x_66 = l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2;
x_71 = l_Lean_Meta_throwTacticEx___rarg(x_70, x_12, x_69, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_7);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_17);
if (x_72 == 0)
{
return x_17;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_17, 0);
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_17);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_14);
if (x_76 == 0)
{
return x_14;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_14, 0);
x_78 = lean_ctor_get(x_14, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_14);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_11);
if (x_80 == 0)
{
return x_11;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_11, 0);
x_82 = lean_ctor_get(x_11, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_11);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getInductiveValFromMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_27 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 4, x_20);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_22);
lean_ctor_set(x_28, 7, x_23);
lean_ctor_set(x_28, 8, x_24);
lean_ctor_set(x_28, 9, x_25);
lean_ctor_set(x_28, 10, x_26);
x_29 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28, x_10, x_11);
lean_dec(x_10);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = lean_ctor_get(x_8, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 7);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_14, x_15, x_16, x_1);
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
x_21 = lean_ctor_get(x_8, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_ResolveName_resolveGlobalName(x_20, x_21, x_22, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_8);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_List_filterTRAux___at_Lean_resolveGlobalConstCore___spec__1(x_12, x_14);
x_16 = l_List_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6___lambda__1(x_15, x_14, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_15);
x_19 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_12);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 5);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_18);
x_19 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get(x_8, 6);
x_27 = lean_ctor_get(x_8, 7);
x_28 = lean_ctor_get(x_8, 8);
x_29 = lean_ctor_get(x_8, 9);
x_30 = lean_ctor_get(x_8, 10);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_31 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set(x_32, 7, x_27);
lean_ctor_set(x_32, 8, x_28);
lean_ctor_set(x_32, 9, x_29);
lean_ctor_set(x_32, 10, x_30);
x_33 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_32, x_9, x_10);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__3;
x_35 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__4(x_1, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_27 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 4, x_20);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_22);
lean_ctor_set(x_28, 7, x_23);
lean_ctor_set(x_28, 8, x_24);
lean_ctor_set(x_28, 9, x_25);
lean_ctor_set(x_28, 10, x_26);
x_29 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28, x_10, x_11);
lean_dec(x_10);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous identifier '", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: ", 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = 0;
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_17 = l_Lean_Syntax_formatStxAux(x_14, x_15, x_16, x_1);
x_18 = l_Std_Format_defWidth;
x_19 = lean_format_pretty(x_17, x_18);
x_20 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_box(0);
x_25 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_12, x_24);
x_26 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_25);
x_27 = lean_string_append(x_23, x_26);
lean_dec(x_26);
x_28 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__9(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_11, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_36);
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_33);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_box(0);
x_42 = 0;
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_44 = l_Lean_Syntax_formatStxAux(x_41, x_42, x_43, x_1);
x_45 = l_Std_Format_defWidth;
x_46 = lean_format_pretty(x_44, x_45);
x_47 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_box(0);
x_52 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_12, x_51);
x_53 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_52);
x_54 = lean_string_append(x_50, x_53);
lean_dec(x_53);
x_55 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__9(x_1, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = lean_environment_find(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_11);
x_17 = lean_box(0);
x_18 = l_Lean_mkConst(x_1, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = lean_environment_find(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_box(0);
x_31 = l_Lean_mkConst(x_1, x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_ConstantInfo_levelParams(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_14, x_15);
x_17 = l_Lean_mkConst(x_1, x_16);
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
x_20 = l_Lean_ConstantInfo_levelParams(x_18);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_20, x_21);
x_23 = l_Lean_mkConst(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_st_ref_get(x_9, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 4);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_28, 1);
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_1);
lean_ctor_set(x_28, 1, x_34);
x_35 = lean_st_ref_set(x_5, x_27, x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = l_Std_PersistentArray_push___rarg(x_44, x_1);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_42);
lean_ctor_set(x_27, 4, x_46);
x_47 = lean_st_ref_set(x_5, x_27, x_29);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
x_54 = lean_ctor_get(x_27, 2);
x_55 = lean_ctor_get(x_27, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_56 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_57 = lean_ctor_get(x_28, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_59 = x_28;
} else {
 lean_dec_ref(x_28);
 x_59 = lean_box(0);
}
x_60 = l_Std_PersistentArray_push___rarg(x_58, x_1);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 1);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_56);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_54);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_61);
x_63 = lean_st_ref_set(x_5, x_62, x_29);
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
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__3;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__15(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_1);
x_12 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
if (x_20 == 0)
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
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_13);
x_26 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__11(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
x_31 = l_Lean_LocalContext_empty;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_2);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_13);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
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
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
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
uint8_t x_44; 
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
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_casesOnSuffix;
x_16 = lean_name_mk_string(x_14, x_15);
x_17 = l_Lean_Meta_getElimInfo(x_16, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1;
x_21 = lean_name_mk_string(x_19, x_20);
x_22 = l_Lean_Meta_getElimInfo(x_21, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'induction' tactic does not support nested inductive types, the eliminator '", 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has multiple motives", 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1;
x_21 = lean_name_mk_string(x_19, x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'induction' tactic does not support mutually inductive types, the eliminator '", 78);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_1, x_14);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_getInductiveValFromMajor(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2(x_2, x_17, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
x_24 = l_List_lengthTRAux___rarg(x_23, x_14);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1;
x_30 = lean_name_mk_string(x_28, x_29);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2(x_2, x_21, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eliminator must be provided when multiple targets are used (use 'using <eliminator-name>'), and no default eliminator has been registered using attribute `[eliminator]`", 168);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_16 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__2;
x_17 = l_Lean_throwError___at_Lean_Elab_Tactic_refineCore___spec__1(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Syntax_isNone(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 5);
x_19 = l_Lean_replaceRef(x_15, x_18);
lean_dec(x_18);
lean_ctor_set(x_10, 5, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1(x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_getElimInfo(x_21, x_8, x_9, x_10, x_11, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
x_30 = lean_ctor_get(x_10, 2);
x_31 = lean_ctor_get(x_10, 3);
x_32 = lean_ctor_get(x_10, 4);
x_33 = lean_ctor_get(x_10, 5);
x_34 = lean_ctor_get(x_10, 6);
x_35 = lean_ctor_get(x_10, 7);
x_36 = lean_ctor_get(x_10, 8);
x_37 = lean_ctor_get(x_10, 9);
x_38 = lean_ctor_get(x_10, 10);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_39 = l_Lean_replaceRef(x_15, x_33);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 4, x_32);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_34);
lean_ctor_set(x_40, 7, x_35);
lean_ctor_set(x_40, 8, x_36);
lean_ctor_set(x_40, 9, x_37);
lean_ctor_set(x_40, 10, x_38);
lean_inc(x_11);
lean_inc(x_40);
lean_inc(x_9);
lean_inc(x_8);
x_41 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1(x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_40, x_11, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_getElimInfo(x_42, x_8, x_9, x_40, x_11, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_49 = l_Lean_Meta_getCustomEliminator_x3f(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4(x_2, x_3, x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
lean_ctor_set(x_49, 0, x_56);
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_dec(x_49);
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_getLocalDecl(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_LocalDecl_hasValue(x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lean_LocalDecl_hasValue(x_13);
lean_dec(x_13);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
x_15 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_8);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__1(x_15, x_16, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_generalize(x_12, x_17, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_24, x_16, x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_replaceMainGoal(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_25);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__2___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
x_30 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1;
x_11 = x_30;
goto block_26;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
x_32 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1;
x_11 = x_32;
goto block_26;
}
else
{
size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_34 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___boxed__const__1;
x_35 = lean_box_usize(x_33);
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__2___boxed), 12, 3);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_34);
lean_closure_set(x_36, 2, x_35);
x_11 = x_36;
goto block_26;
}
}
block_26:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__1), 10, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = l_Lean_Elab_Tactic_withMainContext___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_21;
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___spec__2(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("target (or one of its indices) occurs more than once", 52);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_Expr_fvarId_x21(x_1);
x_10 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_2, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_10);
x_13 = l_Lean_indentExpr(x_1);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_17, x_4, x_5, x_6, x_7, x_8);
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
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index in target's type is not a variable (consider using the `cases` tactic instead)", 84);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = l_Lean_Expr_isFVar(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = l_Lean_indentExpr(x_13);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_19, x_6, x_7, x_8, x_9, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1(x_13, x_1, x_25, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_5 = x_29;
x_10 = x_28;
goto _start;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction_checkTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(0);
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1(x_7, x_1, x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction_checkTargets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalInduction_checkTargets(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_2, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = lean_box(0);
x_19 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Elab_Tactic_elabTerm(x_15, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_17, x_2, x_21);
x_2 = x_24;
x_3 = x_25;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvarId_x21(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux(x_19, x_20);
x_22 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
lean_inc(x_19);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_19, x_23, x_25);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = l_Lean_instInhabitedExpr;
x_29 = lean_array_get(x_28, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_30 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(x_3, x_30, x_4, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts(x_5);
x_34 = l_Lean_assignExprMVar___at_Lean_Elab_Tactic_closeMainGoal___spec__1(x_3, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_37 = l_Lean_Elab_Tactic_ElimApp_evalAlts(x_2, x_36, x_33, x_6, x_7, x_20, x_8, x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_array_to_list(lean_box(0), x_39);
x_41 = l_Lean_Elab_Tactic_appendGoals(x_40, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
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
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elimApp: ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 7);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 8);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 9);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 10);
lean_inc(x_30);
x_31 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set(x_32, 7, x_27);
lean_ctor_set(x_32, 8, x_28);
lean_ctor_set(x_32, 9, x_29);
lean_ctor_set(x_32, 10, x_30);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_33 = l_Lean_Elab_Tactic_ElimApp_mkElimApp(x_2, x_3, x_4, x_13, x_14, x_15, x_16, x_32, x_18, x_19);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3;
x_52 = lean_st_ref_get(x_18, x_35);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 3);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = 0;
x_37 = x_57;
x_38 = x_56;
goto block_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_36, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_37 = x_62;
x_38 = x_61;
goto block_51;
}
block_51:
{
if (x_37 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Tactic_evalInduction___lambda__1(x_34, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_39, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_38);
lean_dec(x_7);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__2;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_36, x_46, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_38);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Tactic_evalInduction___lambda__1(x_34, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_48, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_49);
lean_dec(x_48);
lean_dec(x_7);
return x_50;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_33);
if (x_63 == 0)
{
return x_33;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_33, 0);
x_65 = lean_ctor_get(x_33, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_33);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_1);
x_20 = l_Lean_Meta_addImplicitTargets(x_1, x_2, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_evalInduction_checkTargets(x_21, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_21);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
lean_inc(x_21);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(x_26, x_3, x_21);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_21);
x_28 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars(x_4, x_5, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__2___boxed), 19, 10);
lean_closure_set(x_33, 0, x_6);
lean_closure_set(x_33, 1, x_1);
lean_closure_set(x_33, 2, x_21);
lean_closure_set(x_33, 3, x_7);
lean_closure_set(x_33, 4, x_32);
lean_closure_set(x_33, 5, x_27);
lean_closure_set(x_33, 6, x_8);
lean_closure_set(x_33, 7, x_9);
lean_closure_set(x_33, 8, x_10);
lean_closure_set(x_33, 9, x_31);
x_34 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_32, x_33, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Elab_Tactic_withMainContext___rarg(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_Syntax_getArg(x_2, x_22);
x_24 = 1;
x_25 = lean_box(x_24);
lean_inc(x_20);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___boxed), 12, 3);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_20);
lean_closure_set(x_26, 2, x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Elab_Tactic_withMainContext___rarg(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = l_Lean_Elab_Tactic_getMainGoal(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_14, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_12, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_13, 5);
lean_inc(x_42);
x_43 = l_Lean_Elab_Tactic_mkTacticInfo(x_38, x_40, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_31);
x_46 = l_Lean_Meta_getMVarTag(x_31, x_11, x_12, x_13, x_14, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box_usize(x_3);
lean_inc(x_31);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__3___boxed), 19, 10);
lean_closure_set(x_50, 0, x_28);
lean_closure_set(x_50, 1, x_20);
lean_closure_set(x_50, 2, x_49);
lean_closure_set(x_50, 3, x_31);
lean_closure_set(x_50, 4, x_2);
lean_closure_set(x_50, 5, x_4);
lean_closure_set(x_50, 6, x_47);
lean_closure_set(x_50, 7, x_5);
lean_closure_set(x_50, 8, x_6);
lean_closure_set(x_50, 9, x_44);
x_51 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_31, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_48);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_44);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
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
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
return x_30;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_30, 0);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_30);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_19);
if (x_64 == 0)
{
return x_19;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_19, 0);
x_66 = lean_ctor_get(x_19, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_19);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_16);
if (x_68 == 0)
{
return x_16;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_16, 0);
x_70 = lean_ctor_get(x_16, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_16);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_5, 2, x_15);
x_16 = l_Lean_Elab_Tactic_evalTacticAux(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 4);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 5);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 6);
x_31 = lean_ctor_get(x_5, 7);
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 7);
lean_inc(x_31);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_19);
x_35 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_18);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_23);
lean_ctor_set(x_35, 4, x_24);
lean_ctor_set(x_35, 5, x_25);
lean_ctor_set(x_35, 6, x_26);
lean_ctor_set(x_35, 7, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*8, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 1, x_21);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 2, x_22);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 3, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 4, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 5, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 6, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*8 + 7, x_32);
x_36 = l_Lean_Elab_Tactic_evalTacticAux(x_2, x_3, x_4, x_35, x_6, x_7, x_8, x_9, x_10, x_11);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalInduction___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandInduction_x3f(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getSepArgs(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_box_usize(x_19);
x_21 = l_Lean_Elab_Tactic_evalInduction___boxed__const__1;
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__1___boxed), 12, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_17);
x_23 = l_Lean_Elab_Tactic_evalInduction___boxed__const__1;
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__4___boxed), 15, 6);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_16);
lean_closure_set(x_24, 4, x_13);
lean_closure_set(x_24, 5, x_14);
x_25 = l_Lean_Elab_Tactic_focus___rarg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
lean_inc(x_26);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__5), 11, 2);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_1, x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Tactic_evalInduction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_9);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Elab_Tactic_evalInduction___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
size_t x_20; lean_object* x_21; 
x_20 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_21 = l_Lean_Elab_Tactic_evalInduction___lambda__3(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalInduction___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; lean_object* x_17; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Lean_Elab_Tactic_evalInduction___lambda__4(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_isHoleRHS___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2;
x_2 = l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_isHoleRHS___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalInduction", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__9;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(500u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(535u);
x_2 = lean_unsigned_to_nat(92u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__1;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__2;
x_4 = lean_unsigned_to_nat(92u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(500u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(500u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__4;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__5;
x_4 = lean_unsigned_to_nat(63u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabCasesTargets___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_2, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = l_Lean_Syntax_getArg(x_15, x_16);
x_19 = l_Lean_Syntax_isNone(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_15, x_20);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Elab_Tactic_elabTerm(x_21, x_22, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (x_19 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Syntax_getArg(x_18, x_16);
lean_dec(x_18);
x_28 = l_Lean_Syntax_getId(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_29);
x_31 = 1;
x_32 = lean_usize_add(x_2, x_31);
x_33 = lean_array_uset(x_17, x_2, x_30);
x_2 = x_32;
x_3 = x_33;
x_12 = x_26;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_22);
x_42 = 1;
x_43 = lean_usize_add(x_2, x_42);
x_44 = lean_array_uset(x_17, x_2, x_41);
x_2 = x_43;
x_3 = x_44;
x_12 = x_40;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabCasesTargets___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_inc(x_6);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
lean_dec(x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_array_push(x_16, x_17);
lean_ctor_set(x_5, 1, x_23);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_10 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_21);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_instInhabitedFVarId;
x_29 = lean_array_get(x_28, x_1, x_15);
x_30 = l_Lean_mkFVar(x_29);
x_31 = lean_array_push(x_16, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_15, x_32);
lean_dec(x_15);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_33);
x_34 = 1;
x_35 = lean_usize_add(x_4, x_34);
x_4 = x_35;
x_10 = x_27;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_17);
lean_dec(x_13);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = l_Lean_instInhabitedFVarId;
x_39 = lean_array_get(x_38, x_1, x_15);
x_40 = l_Lean_mkFVar(x_39);
x_41 = lean_array_push(x_16, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_15, x_42);
lean_dec(x_15);
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_43);
x_44 = 1;
x_45 = lean_usize_add(x_4, x_44);
x_4 = x_45;
x_10 = x_37;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_5, 0);
x_52 = lean_ctor_get(x_5, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_5);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_inc(x_6);
lean_inc(x_53);
x_54 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(x_53, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_13, 2);
lean_inc(x_57);
lean_dec(x_13);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_array_push(x_52, x_53);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_59);
x_61 = 1;
x_62 = lean_usize_add(x_4, x_61);
x_4 = x_62;
x_5 = x_60;
x_10 = x_58;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
lean_dec(x_57);
lean_dec(x_53);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_dec(x_54);
x_65 = l_Lean_instInhabitedFVarId;
x_66 = lean_array_get(x_65, x_1, x_51);
x_67 = l_Lean_mkFVar(x_66);
x_68 = lean_array_push(x_52, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_51, x_69);
lean_dec(x_51);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_72 = 1;
x_73 = lean_usize_add(x_4, x_72);
x_4 = x_73;
x_5 = x_71;
x_10 = x_64;
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; 
lean_dec(x_53);
lean_dec(x_13);
x_75 = lean_ctor_get(x_54, 1);
lean_inc(x_75);
lean_dec(x_54);
x_76 = l_Lean_instInhabitedFVarId;
x_77 = lean_array_get(x_76, x_1, x_51);
x_78 = l_Lean_mkFVar(x_77);
x_79 = lean_array_push(x_52, x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_51, x_80);
lean_dec(x_51);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
x_83 = 1;
x_84 = lean_usize_add(x_4, x_83);
x_4 = x_84;
x_5 = x_82;
x_10 = x_75;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_13);
lean_dec(x_6);
x_86 = lean_ctor_get(x_54, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_54, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_88 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_elabCasesTargets___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_5);
x_13 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_9 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_16);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_array_push(x_4, x_11);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_22;
x_9 = x_21;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_array_push(x_4, x_11);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_2 = x_29;
x_4 = x_27;
x_9 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Tactic_elabCasesTargets___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_inc(x_8);
x_16 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_shouldGeneralizeTarget(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_19);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_16, 0, x_35);
return x_16;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_8);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
return x_46;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_49; uint8_t x_50; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_16 = x_51;
x_17 = x_15;
goto block_48;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_1, x_1);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
x_16 = x_53;
x_17 = x_15;
goto block_48;
}
else
{
size_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_usize_of_nat(x_1);
x_55 = l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1;
lean_inc(x_8);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_elabCasesTargets___spec__3(x_2, x_3, x_54, x_55, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_16 = x_57;
x_17 = x_58;
goto block_48;
}
else
{
uint8_t x_59; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_48:
{
lean_object* x_18; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_generalize(x_14, x_16, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_usize_of_nat(x_1);
x_24 = l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___closed__1;
lean_inc(x_8);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabCasesTargets___spec__2(x_21, x_2, x_23, x_3, x_24, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Tactic_replaceMainGoal(x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
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
uint8_t x_40; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
else
{
uint8_t x_63; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_13);
if (x_63 == 0)
{
return x_13;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_13, 0);
x_65 = lean_ctor_get(x_13, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_13);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabCasesTargets___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_38; uint8_t x_39; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_16);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1;
x_17 = x_40;
goto block_37;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_16, x_16);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1;
x_17 = x_42;
goto block_37;
}
else
{
size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_usize_of_nat(x_16);
x_44 = lean_box_usize(x_2);
x_45 = lean_box_usize(x_43);
lean_inc(x_14);
x_46 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_Elab_Tactic_elabCasesTargets___spec__4___boxed), 12, 3);
lean_closure_set(x_46, 0, x_14);
lean_closure_set(x_46, 1, x_44);
lean_closure_set(x_46, 2, x_45);
x_17 = x_46;
goto block_37;
}
}
block_37:
{
lean_object* x_18; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Meta_generalize___spec__1(x_23, x_2, x_14);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Meta_generalize___spec__1(x_26, x_2, x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_box_usize(x_2);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___boxed), 12, 3);
lean_closure_set(x_31, 0, x_16);
lean_closure_set(x_31, 1, x_14);
lean_closure_set(x_31, 2, x_30);
x_32 = l_Lean_Elab_Tactic_withMainContext___rarg(x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_13, 0);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabCasesTargets___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = lean_box_usize(x_12);
x_14 = l_Lean_Elab_Tactic_elabCasesTargets___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabCasesTargets___lambda__2___boxed), 12, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_1);
x_16 = l_Lean_Elab_Tactic_withMainContext___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabCasesTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabCasesTargets___spec__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabCasesTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabCasesTargets___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_elabCasesTargets___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_elabCasesTargets___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Tactic_elabCasesTargets___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Elab_Tactic_elabCasesTargets___spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_elabCasesTargets___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabCasesTargets___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_elabCasesTargets___lambda__2(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalCases___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_1, x_16);
lean_dec(x_16);
x_21 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_26 = lean_array_uset(x_18, x_3, x_22);
x_3 = x_25;
x_4 = x_26;
x_13 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(x_1, x_2, x_3, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_assignExprMVar___at_Lean_Elab_Tactic_closeMainGoal___spec__1(x_1, x_4, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Elab_Tactic_ElimApp_evalAlts(x_6, x_24, x_7, x_8, x_9, x_10, x_25, x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_18 = l_Lean_Meta_addImplicitTargets(x_1, x_2, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_15, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_15, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 10);
lean_inc(x_31);
x_32 = l_Lean_replaceRef(x_3, x_26);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_24);
lean_ctor_set(x_33, 4, x_25);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_27);
lean_ctor_set(x_33, 7, x_28);
lean_ctor_set(x_33, 8, x_29);
lean_ctor_set(x_33, 9, x_30);
lean_ctor_set(x_33, 10, x_31);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_34 = l_Lean_Elab_Tactic_ElimApp_mkElimApp(x_1, x_19, x_4, x_11, x_12, x_13, x_14, x_33, x_16, x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Expr_getAppNumArgsAux(x_37, x_38);
x_40 = l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1;
lean_inc(x_39);
x_41 = lean_mk_array(x_39, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
lean_inc(x_37);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_37, x_41, x_43);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = 0;
x_49 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalCases___spec__1(x_44, x_47, x_48, x_45, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_36);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = l_Lean_instInhabitedExpr;
x_54 = lean_array_get(x_53, x_44, x_52);
lean_dec(x_52);
lean_dec(x_44);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_54);
x_55 = lean_infer_type(x_54, x_13, x_14, x_15, x_16, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_50);
x_58 = l_Lean_Meta_generalizeTargetsEq(x_5, x_56, x_50, x_13, x_14, x_15, x_16, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_array_get_size(x_50);
lean_dec(x_50);
x_62 = lean_box(0);
x_63 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_61);
x_64 = l_Lean_Meta_introNCore(x_59, x_61, x_62, x_63, x_63, x_13, x_14, x_15, x_16, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Lean_Expr_mvarId_x21(x_54);
lean_dec(x_54);
lean_inc(x_68);
x_70 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__1___boxed), 19, 10);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_69);
lean_closure_set(x_70, 2, x_67);
lean_closure_set(x_70, 3, x_37);
lean_closure_set(x_70, 4, x_35);
lean_closure_set(x_70, 5, x_1);
lean_closure_set(x_70, 6, x_6);
lean_closure_set(x_70, 7, x_7);
lean_closure_set(x_70, 8, x_8);
lean_closure_set(x_70, 9, x_61);
x_71 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_68, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_66);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_61);
lean_dec(x_54);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_16);
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
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
return x_64;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_64, 0);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_64);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_16);
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
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_58);
if (x_76 == 0)
{
return x_58;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_58, 0);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_58);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_55);
if (x_80 == 0)
{
return x_55;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_55, 0);
x_82 = lean_ctor_get(x_55, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_55);
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
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_34);
if (x_84 == 0)
{
return x_34;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_34, 0);
x_86 = lean_ctor_get(x_34, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_34);
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
lean_dec(x_16);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_18);
if (x_88 == 0)
{
return x_18;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_18, 0);
x_90 = lean_ctor_get(x_18, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_18);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_13 = l_Lean_Elab_Tactic_elabCasesTargets(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts(x_17);
x_19 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltsOfOptInductionAlts(x_17);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_2, x_20);
x_22 = 0;
x_23 = lean_box(x_22);
lean_inc(x_14);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___boxed), 12, 3);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Elab_Tactic_withMainContext___rarg(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_11, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_9, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_10, 5);
lean_inc(x_40);
x_41 = l_Lean_Elab_Tactic_mkTacticInfo(x_36, x_38, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_29);
x_44 = l_Lean_Meta_getMVarTag(x_29, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_29);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__2___boxed), 17, 8);
lean_closure_set(x_47, 0, x_26);
lean_closure_set(x_47, 1, x_14);
lean_closure_set(x_47, 2, x_3);
lean_closure_set(x_47, 3, x_45);
lean_closure_set(x_47, 4, x_29);
lean_closure_set(x_47, 5, x_18);
lean_closure_set(x_47, 6, x_19);
lean_closure_set(x_47, 7, x_42);
x_48 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_29, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_42);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_18);
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
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
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
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_18);
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
x_53 = !lean_is_exclusive(x_28);
if (x_53 == 0)
{
return x_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_28, 0);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_28);
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
lean_dec(x_19);
lean_dec(x_18);
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
x_57 = !lean_is_exclusive(x_25);
if (x_57 == 0)
{
return x_25;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandCases_x3f(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getSepArgs(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases___lambda__3___boxed), 12, 3);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_13);
x_16 = l_Lean_Elab_Tactic_focus___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInduction___lambda__5), 11, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_1, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalCases___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Elab_Tactic_evalCases___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Tactic_evalCases___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCases___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalCases___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cases", 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalCases", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCases), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(559u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(585u);
x_2 = lean_unsigned_to_nat(118u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__1;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__2;
x_4 = lean_unsigned_to_nat(118u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(559u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(559u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__4;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__5;
x_4 = lean_unsigned_to_nat(55u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Induction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ElimInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_GeneralizeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getAltName___closed__2);
l_Lean_Elab_Tactic_isHoleRHS___closed__1 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__1);
l_Lean_Elab_Tactic_isHoleRHS___closed__2 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__2);
l_Lean_Elab_Tactic_isHoleRHS___closed__3 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__3);
l_Lean_Elab_Tactic_isHoleRHS___closed__4 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__4);
l_Lean_Elab_Tactic_isHoleRHS___closed__5 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__5);
l_Lean_Elab_Tactic_isHoleRHS___closed__6 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__6);
l_Lean_Elab_Tactic_isHoleRHS___closed__7 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__7);
l_Lean_Elab_Tactic_isHoleRHS___closed__8 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__8);
l_Lean_Elab_Tactic_isHoleRHS___closed__9 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__9);
l_Lean_Elab_Tactic_isHoleRHS___closed__10 = _init_l_Lean_Elab_Tactic_isHoleRHS___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_isHoleRHS___closed__10);
l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__1 = _init_l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__1);
l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__2 = _init_l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__2);
l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3 = _init_l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalAlt___spec__1___closed__3);
l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAlt___lambda__2___closed__2);
l_Lean_Elab_Tactic_ElimApp_State_argPos___default = _init_l_Lean_Elab_Tactic_ElimApp_State_argPos___default();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_State_argPos___default);
l_Lean_Elab_Tactic_ElimApp_State_targetPos___default = _init_l_Lean_Elab_Tactic_ElimApp_State_targetPos___default();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_State_targetPos___default);
l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1 = _init_l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_State_alts___default___closed__1);
l_Lean_Elab_Tactic_ElimApp_State_alts___default = _init_l_Lean_Elab_Tactic_ElimApp_State_alts___default();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_State_alts___default);
l_Lean_Elab_Tactic_ElimApp_State_insts___default = _init_l_Lean_Elab_Tactic_ElimApp_State_insts___default();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_State_insts___default);
l_Lean_Elab_Tactic_ElimApp_Result_alts___default = _init_l_Lean_Elab_Tactic_ElimApp_Result_alts___default();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_Result_alts___default);
l_Lean_Elab_Tactic_ElimApp_Result_others___default = _init_l_Lean_Elab_Tactic_ElimApp_Result_others___default();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_Result_others___default);
l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__1 = _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__1);
l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__2 = _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__2);
l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__3 = _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__3);
l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4 = _init_l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_mkElimApp_loop___closed__4);
l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__1 = _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__1);
l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__2 = _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__2);
l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__3 = _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__3);
l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__4 = _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__4);
l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5 = _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__5);
l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6 = _init_l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_setMotiveArg___closed__6);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___lambda__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_checkAltNames___spec__3___closed__2);
l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1 = _init_l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_ContextInfo_saveNoFileMap___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___spec__4___rarg___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_saveAltVarsInfo___boxed__const__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_reorderAlts___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___lambda__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_ElimApp_evalAlts_go___spec__5___closed__1);
l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__1);
l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__2);
l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_evalAlts_go___lambda__2___closed__3);
l_Lean_Elab_Tactic_ElimApp_evalAlts_go___closed__1 = _init_l_Lean_Elab_Tactic_ElimApp_evalAlts_go___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ElimApp_evalAlts_go___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getUserGeneralizingFVarIds___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeVars___spec__1___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getOptPreTacOfOptInductionAlts___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_expandMultiAlt_x3f___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_checkAltsOfOptInductionAlts___spec__1___closed__2);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__1);
l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getInductiveValFromMajor___lambda__1___closed__2);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__1 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__1);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__8___closed__2);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__1 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__1);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__2 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__2);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__3 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__3___closed__3);
l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1 = _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__1);
l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2 = _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__2___closed__2);
l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__1);
l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__2);
l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___spec__14___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__3 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__3);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__2___closed__4);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__3___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__2 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_getElimNameInfo___lambda__4___closed__2);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___closed__1);
l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_generalizeTargets___boxed__const__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalInduction_checkTargets___spec__1___closed__2);
l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalInduction___boxed__const__1 = _init_l_Lean_Elab_Tactic_evalInduction___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalInduction___boxed__const__1);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__7);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__8);
l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__9 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction___closed__9);
res = l___regBuiltin_Lean_Elab_Tactic_evalInduction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Tactic_evalInduction_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabCasesTargets___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabCasesTargets___boxed__const__1 = _init_l_Lean_Elab_Tactic_elabCasesTargets___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabCasesTargets___boxed__const__1);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalCases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Tactic_evalCases_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388____closed__1 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388____closed__1);
res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Induction___hyg_7388_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
