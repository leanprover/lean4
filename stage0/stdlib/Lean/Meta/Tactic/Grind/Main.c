// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Main
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Util Lean.Meta.Tactic.ExposeNames Lean.Meta.Tactic.Simp.Diagnostics Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Proj Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.Solve Lean.Meta.Tactic.Grind.SimpUtil Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.LawfulEqCmp Lean.Meta.Tactic.Grind.ReflCmp
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
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__0;
lean_object* l_Lean_Meta_Grind_getNatZeroExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__5;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__2;
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__29;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__11;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__27;
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__9;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__6;
static lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__33;
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27;
lean_object* l_Lean_Meta_Grind_getBoolFalseExpr___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__6;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__21;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5;
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17;
lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__3;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkENodeCore___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__22;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__4;
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__2;
lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__30;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_debug_terminalTacticsAsSorry;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__13;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__13;
lean_object* l_Lean_Meta_Grind_getTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__1;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__0;
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__17;
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__12;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__4;
lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_PersistentHashMap_toList_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__23;
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__18;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__22;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__14;
lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__5;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__8;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
lean_object* l_Lean_profileitM___at___Lean_Meta_letToHave_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailed___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommonAlpha_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkDiagMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__47;
lean_object* l_Lean_Meta_Grind_getBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__37;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__44;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__43;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__41;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__7;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__42;
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5;
lean_object* l_Lean_MVarId_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38;
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_192__spec__0(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__25;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Result_hasFailed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4;
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1;
extern lean_object* l_Lean_Meta_Grind_builtinPropagatorsRef;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__7;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_shareCommon_spec__0(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__0;
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_6081__spec__0(lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__0;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__2;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__28;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__23;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__34;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__32;
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__14;
lean_object* l_Lean_Meta_Grind_SplitSource_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__26;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__45;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__24;
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__20;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__0;
lean_object* l_Lean_MVarId_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__4;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12;
lean_object* l_Lean_Meta_Grind_getOrderingEqExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__31;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_propagateReflCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__15;
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__15;
lean_object* l_Lean_Meta_Simp_mkMethods(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__13;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2;
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__5;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_mkMethods___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_dischargeRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2;
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__3;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__40;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__21;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__3;
lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__36;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4;
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__10;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32;
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__2;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__10;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__48;
lean_object* l_Lean_MVarId_exposeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4___boxed(lean_object**);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8;
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__8;
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__4;
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__6;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__38;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34;
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_6081__spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__4;
x_2 = l_Lean_Meta_Grind_mkParams___closed__3;
x_3 = l_Lean_Meta_Grind_mkParams___closed__2;
x_4 = l_Lean_Meta_Grind_mkParams___closed__1;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__9() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_mkParams___closed__7;
x_4 = l_Lean_Meta_Grind_mkParams___closed__8;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_7 = l_Lean_Meta_Grind_getSimpContext(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_Meta_Grind_getSimprocs___redArg(x_4, x_5, x_9);
lean_dec_ref(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(x_5, x_12);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Meta_Grind_mkParams___closed__5;
x_17 = l_Lean_Meta_Grind_mkParams___closed__6;
x_18 = l_Lean_Meta_Grind_mkParams___closed__9;
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_8);
lean_ctor_set(x_19, 6, x_11);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lean_Meta_Grind_mkParams___closed__5;
x_23 = l_Lean_Meta_Grind_mkParams___closed__6;
x_24 = l_Lean_Meta_Grind_mkParams___closed__9;
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_8);
lean_ctor_set(x_25, 6, x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l_Lean_Meta_Grind_propagateForallPropUp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Meta_Grind_propagateReflCmp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_array_get_size(x_25);
x_27 = l_Lean_Name_hash___override(x_19);
x_28 = 32;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = 16;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = 1;
x_37 = lean_usize_sub(x_35, x_36);
x_38 = lean_usize_land(x_34, x_37);
x_39 = lean_array_uget(x_25, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_19, x_39);
lean_dec(x_39);
lean_dec(x_19);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_20, 0, x_41);
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_20);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_apply_10(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_array_get_size(x_46);
x_48 = l_Lean_Name_hash___override(x_19);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_46, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_19, x_60);
lean_dec(x_60);
lean_dec(x_19);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_45);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_apply_10(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
return x_65;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_66; 
lean_dec_ref(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = lean_box(0);
lean_ctor_set(x_14, 0, x_66);
return x_14;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
lean_dec(x_14);
x_68 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_68) == 4)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_70 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_71 = lean_ctor_get(x_1, 0);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_array_get_size(x_74);
x_76 = l_Lean_Name_hash___override(x_69);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_74, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_69, x_88);
lean_dec(x_88);
lean_dec(x_69);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_90 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_73;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_72);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_73);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_apply_10(x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
return x_93;
}
}
else
{
lean_dec(x_69);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_70;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_68);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_67);
return x_95;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l_Lean_Meta_Grind_propagateForallPropDown(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Meta_Grind_propagateLawfulEqCmp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash___override(x_20);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_21, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_20, x_35);
lean_dec(x_35);
lean_dec(x_20);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = lean_box(0);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_14);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_10(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec_ref(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = lean_box(0);
lean_ctor_set(x_14, 0, x_40);
return x_14;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_dec(x_14);
x_42 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_42) == 4)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lean_Name_hash___override(x_44);
x_48 = 32;
x_49 = lean_uint64_shift_right(x_47, x_48);
x_50 = lean_uint64_xor(x_47, x_49);
x_51 = 16;
x_52 = lean_uint64_shift_right(x_50, x_51);
x_53 = lean_uint64_xor(x_50, x_52);
x_54 = lean_uint64_to_usize(x_53);
x_55 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_56 = 1;
x_57 = lean_usize_sub(x_55, x_56);
x_58 = lean_usize_land(x_54, x_57);
x_59 = lean_array_uget(x_45, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_44, x_59);
lean_dec(x_59);
lean_dec(x_44);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_41);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_apply_10(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_42);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_41);
return x_66;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkMethods___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_builtinPropagatorsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_mkMethods___redArg___closed__0;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed), 11, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed), 11, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_mkMethods___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkMethods___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkMethods___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_mkMethods(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_cleanupAnnotations(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = lean_simp(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_14);
x_15 = l_Lean_Meta_Simp_dischargeRfl(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec_ref(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_isTrue(x_14);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_19 = l_Lean_Meta_Simp_Result_getProof(x_12, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Meta_mkOfEqTrue(x_20, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_dec_ref(x_15);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = l_Lean_Meta_Simp_Result_getProof(x_12, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4;
x_45 = l_Lean_mkApp4(x_44, x_10, x_14, x_43, x_40);
lean_ctor_set(x_16, 0, x_45);
lean_ctor_set(x_41, 0, x_16);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4;
x_49 = l_Lean_mkApp4(x_48, x_10, x_14, x_46, x_40);
lean_ctor_set(x_16, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_16);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_16);
lean_dec(x_40);
lean_dec_ref(x_14);
lean_dec_ref(x_10);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_16, 0);
lean_inc(x_55);
lean_dec(x_16);
x_56 = l_Lean_Meta_Simp_Result_getProof(x_12, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4;
x_61 = l_Lean_mkApp4(x_60, x_10, x_14, x_57, x_55);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_55);
lean_dec_ref(x_14);
lean_dec_ref(x_10);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_66 = x_56;
} else {
 lean_dec_ref(x_56);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
else
{
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
else
{
uint8_t x_68; 
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
return x_11;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_11, 0);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_11);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_shareCommon_spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__5;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__6;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__2;
x_3 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__12;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__15;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ordering", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__20;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__21;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__24;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__25;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__26;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__27;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__29;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__28;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__31;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__34;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__36() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__34;
x_4 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__36;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__33;
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__31;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__32;
x_4 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__28;
x_5 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__30;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_192__spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__33;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__40;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__34;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__43() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__34;
x_4 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__42;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_9 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__7;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__10;
x_13 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__14;
x_17 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__17;
x_21 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__18;
x_25 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_24, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__22;
x_29 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Lean_Int_mkType;
x_33 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_32, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lean_Meta_Grind_mkMethods___redArg(x_3, x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = 1;
x_40 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__23;
x_41 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__38;
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_45 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_45);
x_47 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__41;
x_48 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__43;
x_49 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__44;
x_50 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_42);
lean_ctor_set(x_50, 4, x_43);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set(x_50, 7, x_48);
lean_ctor_set(x_50, 8, x_49);
lean_ctor_set(x_50, 9, x_49);
x_51 = lean_st_mk_ref(x_50, x_38);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_57);
lean_dec_ref(x_2);
x_58 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__45;
x_59 = l_Lean_Meta_Simp_mkMethods(x_57, x_58, x_39);
x_60 = 0;
x_61 = lean_box(6);
x_62 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_54);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_55);
lean_ctor_set(x_62, 5, x_14);
lean_ctor_set(x_62, 6, x_10);
lean_ctor_set(x_62, 7, x_26);
lean_ctor_set(x_62, 8, x_22);
lean_ctor_set(x_62, 9, x_18);
lean_ctor_set(x_62, 10, x_30);
lean_ctor_set(x_62, 11, x_34);
lean_ctor_set_uint8(x_62, sizeof(void*)*12, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*12 + 1, x_39);
lean_inc(x_52);
x_63 = lean_apply_8(x_1, x_37, x_62, x_52, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_st_ref_get(x_52, x_65);
lean_dec(x_52);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_dec(x_52);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_GrindM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_array_uget(x_5, x_7);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_17);
x_20 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_3, x_19, x_17, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_17);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec_ref(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_4);
x_30 = 1;
x_31 = lean_usize_add(x_7, x_30);
x_7 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
x_38 = lean_array_uget(x_5, x_7);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_37);
x_39 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_3, x_38, x_37, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
lean_dec(x_37);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec_ref(x_39);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_inc(x_4);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_47);
x_49 = 1;
x_50 = lean_usize_add(x_7, x_49);
x_7 = x_50;
x_8 = x_48;
x_13 = x_46;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_35);
x_37 = lean_apply_7(x_1, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_35);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
x_11 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_8 = x_17;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_2, x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_13, x_12, x_15, x_16, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_free_object(x_4);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_4);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_37, x_36, x_39, x_40, x_38, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_55 = x_41;
} else {
 lean_dec_ref(x_41);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_4);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0___boxed), 7, 0);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_5);
x_62 = lean_array_size(x_58);
x_63 = 0;
x_64 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(x_59, x_60, x_58, x_62, x_63, x_61, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
lean_ctor_set(x_4, 0, x_69);
lean_ctor_set(x_64, 0, x_4);
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
lean_ctor_set(x_4, 0, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_65);
lean_free_object(x_4);
x_73 = !lean_is_exclusive(x_64);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_64, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_75);
return x_64;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_dec(x_64);
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
lean_dec(x_66);
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
lean_free_object(x_4);
x_79 = !lean_is_exclusive(x_64);
if (x_79 == 0)
{
return x_64;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_64, 0);
x_81 = lean_ctor_get(x_64, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_64);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_4, 0);
lean_inc(x_83);
lean_dec(x_4);
x_84 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0___boxed), 7, 0);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_5);
x_87 = lean_array_size(x_83);
x_88 = 0;
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(x_84, x_85, x_83, x_87, x_88, x_86, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_93 = x_89;
} else {
 lean_dec_ref(x_89);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
lean_dec(x_91);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_89, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_89, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_103 = x_89;
} else {
 lean_dec_ref(x_89);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_27 = x_19;
} else {
 lean_dec_ref(x_19);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec_ref(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_11 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_39);
x_41 = lean_apply_7(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_5, x_53);
x_5 = x_54;
x_6 = x_52;
x_11 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_8 = x_17;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_2, x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0___boxed), 7, 0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_array_size(x_11);
x_26 = 0;
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__3(x_22, x_23, x_11, x_25, x_26, x_24, x_5, x_6, x_7, x_8, x_20);
lean_dec_ref(x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_14 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(x_2, x_3, x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*6 + 12);
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__0;
x_11 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__1;
x_12 = lean_box(x_9);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___boxed), 8, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_5, x_7);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
lean_inc(x_1);
x_24 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_3, x_23, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_8, 0, x_28);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_8, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec_ref(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_4);
x_34 = 1;
x_35 = lean_usize_add(x_7, x_34);
x_7 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_8);
lean_dec(x_21);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_array_uget(x_5, x_7);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
lean_inc(x_1);
x_43 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_3, x_42, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_41);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec_ref(x_43);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_inc(x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_7, x_53);
x_7 = x_54;
x_8 = x_52;
x_17 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_58 = x_43;
} else {
 lean_dec_ref(x_43);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_22 = lean_apply_11(x_1, x_21, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_19);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec_ref(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_39);
x_41 = lean_apply_11(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_39);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec_ref(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_5, x_51);
x_5 = x_52;
x_6 = x_50;
x_15 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_activateTheorem(x_3, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_17, x_16, x_19, x_20, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_22);
lean_free_object(x_4);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_4);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
x_43 = lean_array_size(x_40);
x_44 = 0;
x_45 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_41, x_40, x_43, x_44, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_4);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_4, 0);
x_63 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0___boxed), 13, 2);
lean_closure_set(x_63, 0, x_1);
lean_closure_set(x_63, 1, x_2);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_5);
x_66 = lean_array_size(x_62);
x_67 = 0;
x_68 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(x_63, x_64, x_62, x_66, x_67, x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
lean_ctor_set(x_4, 0, x_73);
lean_ctor_set(x_68, 0, x_4);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
lean_ctor_set(x_4, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_69);
lean_free_object(x_4);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_68, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_79);
return x_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_dec(x_68);
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
lean_dec(x_70);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_4);
x_83 = !lean_is_exclusive(x_68);
if (x_83 == 0)
{
return x_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_68, 0);
x_85 = lean_ctor_get(x_68, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_68);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
lean_dec(x_4);
x_88 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0___boxed), 13, 2);
lean_closure_set(x_88, 0, x_1);
lean_closure_set(x_88, 1, x_2);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
x_91 = lean_array_size(x_87);
x_92 = 0;
x_93 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(x_88, x_89, x_87, x_91, x_92, x_90, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_94);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_95, 0);
lean_inc(x_103);
lean_dec(x_95);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_107 = x_93;
} else {
 lean_dec_ref(x_93);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_22 = lean_apply_11(x_1, x_21, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_6, 0, x_23);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_6, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_19);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec_ref(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_2);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
x_15 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_43);
x_45 = lean_apply_11(x_1, x_44, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
lean_dec(x_43);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec_ref(x_45);
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
lean_inc(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_5, x_57);
x_5 = x_58;
x_6 = x_56;
x_15 = x_54;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_43);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_activateTheorem(x_3, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_3);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_4, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec_ref(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0___boxed), 13, 2);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = lean_array_size(x_15);
x_30 = 0;
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__7(x_26, x_27, x_15, x_29, x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec_ref(x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_32);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
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
else
{
uint8_t x_50; 
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_20 = lean_st_mk_ref(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_5);
x_33 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_2, x_3, x_4, x_5, x_21, x_22);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_5);
x_35 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_6, x_3, x_4, x_5, x_21, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_5);
x_37 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_7, x_4, x_3, x_5, x_21, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_5);
x_39 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_8, x_4, x_3, x_5, x_21, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_5);
x_41 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_9, x_3, x_4, x_5, x_21, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_5);
x_43 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_10, x_4, x_3, x_5, x_21, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
lean_inc(x_21);
x_46 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(x_5, x_45, x_11, x_45, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_23 = x_47;
goto block_32;
}
else
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_23 = x_48;
goto block_32;
}
else
{
uint8_t x_49; 
lean_dec(x_21);
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
block_32:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_st_ref_get(x_21, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_st_ref_get(x_21, x_26);
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__6;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__13;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__26;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__26;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__23;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__26() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__26;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__22;
x_5 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__21;
x_6 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_7 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7;
x_8 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_3);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_2);
lean_ctor_set(x_8, 7, x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_98; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_14);
x_98 = lean_ctor_get_uint8(x_11, sizeof(void*)*6 + 12);
lean_dec_ref(x_11);
if (x_98 == 0)
{
x_15 = x_1;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
goto block_97;
}
else
{
lean_object* x_99; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_99 = l_Lean_MVarId_exposeNames(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_15 = x_100;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_101;
goto block_97;
}
else
{
uint8_t x_102; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_97:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_17, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_17, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Meta_Grind_getBoolTrueExpr___redArg(x_17, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_Grind_getBoolFalseExpr___redArg(x_17, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Lean_Meta_Grind_getNatZeroExpr___redArg(x_17, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Meta_Grind_getOrderingEqExpr___redArg(x_17, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_15);
x_42 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_15, x_2, x_19, x_20, x_21, x_22, x_41);
lean_dec_ref(x_2);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
x_46 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4;
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7;
x_49 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8;
x_50 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_box(0));
x_51 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9;
x_52 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10;
x_53 = 0;
x_54 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11;
x_55 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12;
x_56 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14;
x_57 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_box(0));
x_58 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_59 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_47);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_47);
lean_ctor_set(x_59, 5, x_47);
lean_ctor_set(x_59, 6, x_57);
lean_ctor_set(x_59, 7, x_47);
lean_ctor_set(x_59, 8, x_58);
x_60 = lean_box(0);
x_61 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16;
x_62 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_box(0));
x_63 = lean_box(0);
x_64 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18;
x_65 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19;
x_66 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_66, 0, x_47);
lean_ctor_set(x_66, 1, x_13);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set(x_66, 3, x_61);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_63);
lean_ctor_set(x_66, 6, x_60);
lean_ctor_set(x_66, 7, x_64);
lean_ctor_set(x_66, 8, x_65);
x_67 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_68 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27;
x_69 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28;
x_70 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30;
x_71 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32;
x_72 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34;
x_73 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36;
x_74 = lean_box(0);
x_75 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38;
x_76 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40;
x_77 = lean_box(0);
x_78 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41;
x_79 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_box(0));
x_80 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42;
x_81 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44;
x_82 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45;
x_83 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_83, 0, x_48);
lean_ctor_set(x_83, 1, x_67);
lean_ctor_set(x_83, 2, x_48);
lean_ctor_set(x_83, 3, x_67);
lean_ctor_set(x_83, 4, x_69);
lean_ctor_set(x_83, 5, x_67);
lean_ctor_set(x_83, 6, x_70);
lean_ctor_set(x_83, 7, x_71);
lean_ctor_set(x_83, 8, x_71);
lean_ctor_set(x_83, 9, x_72);
lean_ctor_set(x_83, 10, x_73);
lean_ctor_set(x_83, 11, x_74);
lean_ctor_set(x_83, 12, x_75);
lean_ctor_set(x_83, 13, x_76);
lean_ctor_set(x_83, 14, x_47);
lean_ctor_set(x_83, 15, x_77);
lean_ctor_set(x_83, 16, x_78);
lean_ctor_set(x_83, 17, x_79);
lean_ctor_set(x_83, 18, x_80);
lean_ctor_set(x_83, 19, x_81);
lean_ctor_set(x_83, 20, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*21, x_53);
lean_ctor_set_uint8(x_83, sizeof(void*)*21 + 1, x_53);
x_84 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__47;
x_85 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__48;
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_68);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set(x_86, 3, x_85);
lean_inc(x_15);
x_87 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_87, 0, x_15);
lean_ctor_set(x_87, 1, x_45);
lean_ctor_set(x_87, 2, x_46);
lean_ctor_set(x_87, 3, x_48);
lean_ctor_set(x_87, 4, x_49);
lean_ctor_set(x_87, 5, x_50);
lean_ctor_set(x_87, 6, x_51);
lean_ctor_set(x_87, 7, x_52);
lean_ctor_set(x_87, 8, x_47);
lean_ctor_set(x_87, 9, x_54);
lean_ctor_set(x_87, 10, x_48);
lean_ctor_set(x_87, 11, x_55);
lean_ctor_set(x_87, 12, x_59);
lean_ctor_set(x_87, 13, x_66);
lean_ctor_set(x_87, 14, x_86);
lean_ctor_set(x_87, 15, x_43);
lean_ctor_set_uint8(x_87, sizeof(void*)*16, x_53);
x_88 = 1;
x_89 = lean_box(x_88);
x_90 = lean_box(x_53);
x_91 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed), 19, 11);
lean_closure_set(x_91, 0, x_87);
lean_closure_set(x_91, 1, x_28);
lean_closure_set(x_91, 2, x_89);
lean_closure_set(x_91, 3, x_90);
lean_closure_set(x_91, 4, x_47);
lean_closure_set(x_91, 5, x_25);
lean_closure_set(x_91, 6, x_31);
lean_closure_set(x_91, 7, x_34);
lean_closure_set(x_91, 8, x_37);
lean_closure_set(x_91, 9, x_40);
lean_closure_set(x_91, 10, x_14);
x_92 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(x_15, x_91, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_44);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_93 = !lean_is_exclusive(x_42);
if (x_93 == 0)
{
return x_42;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_42, 0);
x_95 = lean_ctor_get(x_42, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_42);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__7(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed(lean_object** _args) {
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
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_3);
x_21 = lean_unbox(x_4);
x_22 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(x_1, x_2, x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ↦ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uset(x_5, x_4, x_20);
lean_inc(x_1);
x_22 = lean_float_of_nat(x_1);
x_23 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_11);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1;
x_26 = l_Lean_MessageData_ofConst(x_18);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_25);
x_27 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Nat_reprFast(x_16);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
x_34 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4;
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_38 = lean_array_uset(x_21, x_4, x_35);
x_4 = x_37;
x_5 = x_38;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_40; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_44, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; double x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_uset(x_5, x_4, x_49);
lean_inc(x_1);
x_51 = lean_float_of_nat(x_1);
x_52 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
lean_inc(x_2);
x_53 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_float(x_53, sizeof(void*)*2, x_51);
lean_ctor_set_float(x_53, sizeof(void*)*2 + 8, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 16, x_11);
x_54 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1;
x_55 = l_Lean_MessageData_ofConst(x_47);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Nat_reprFast(x_45);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_MessageData_ofFormat(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_64 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4;
x_65 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
x_66 = 1;
x_67 = lean_usize_add(x_4, x_66);
x_68 = lean_array_uset(x_50, x_4, x_65);
x_4 = x_67;
x_5 = x_68;
x_10 = x_48;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_45);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_72 = x_46;
} else {
 lean_dec_ref(x_46);
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
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_6, x_4);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Name_lt(x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
static double _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_38; lean_object* x_39; lean_object* x_42; uint8_t x_43; 
x_9 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_3);
x_43 = lean_nat_dec_eq(x_42, x_9);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_49; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_42, x_44);
lean_dec(x_42);
x_49 = lean_nat_dec_le(x_9, x_45);
if (x_49 == 0)
{
lean_inc(x_45);
x_46 = x_45;
goto block_48;
}
else
{
x_46 = x_9;
goto block_48;
}
block_48:
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_46, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_inc(x_46);
x_38 = x_46;
x_39 = x_46;
goto block_41;
}
else
{
x_38 = x_46;
x_39 = x_45;
goto block_41;
}
}
}
else
{
lean_dec(x_42);
x_10 = x_3;
goto block_37;
}
block_37:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc(x_2);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(x_9, x_2, x_11, x_12, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; double x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_17 = 1;
x_18 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_17);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; double x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_26 = 1;
x_27 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_28 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_float(x_28, sizeof(void*)*2, x_25);
lean_ctor_set_float(x_28, sizeof(void*)*2 + 8, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 16, x_26);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_41:
{
lean_object* x_40; 
x_40 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_3, x_38, x_39);
lean_dec(x_39);
x_10 = x_40;
goto block_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("source: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generation: ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# cases: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 4);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_7, x_6, x_21);
x_30 = l_Lean_Meta_Grind_SplitSource_toMessageData(x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_34 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1;
x_35 = l_Lean_MessageData_ofExpr(x_17);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_3);
x_39 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
lean_inc(x_4);
x_40 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set_float(x_40, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_40, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 16, x_13);
x_41 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__1;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_31);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
x_44 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4;
lean_inc_ref(x_40);
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__3;
x_47 = l_Nat_reprFast(x_18);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_MessageData_ofFormat(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_34);
lean_inc_ref(x_40);
x_52 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_44);
x_53 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__5;
x_54 = l_Nat_reprFast(x_19);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_34);
lean_inc_ref(x_40);
x_59 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_59, 0, x_40);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_44);
x_60 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6;
x_61 = lean_array_push(x_60, x_45);
x_62 = lean_array_push(x_61, x_52);
x_63 = lean_array_push(x_62, x_59);
x_64 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_37);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_65, 0, x_38);
lean_ctor_set(x_65, 1, x_64);
x_23 = x_65;
x_24 = x_32;
goto block_29;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_30, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
lean_dec_ref(x_30);
x_23 = x_66;
x_24 = x_67;
goto block_29;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_22);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_30);
if (x_68 == 0)
{
return x_30;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_30, 0);
x_70 = lean_ctor_get(x_30, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_30);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
block_29:
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_27 = lean_array_uset(x_22, x_6, x_23);
x_6 = x_26;
x_7 = x_27;
x_12 = x_24;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_2 = 1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Case splits", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1;
x_17 = lean_array_size(x_1);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0(x_13, x_14, x_15, x_16, x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_12);
lean_dec_ref(x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2;
x_23 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5;
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2;
x_28 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5;
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___lam__0), 3, 0);
x_3 = lean_box(0);
x_4 = l_Lean_PersistentHashMap_foldl___at___Lean_PersistentHashMap_toList_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_array_push(x_4, x_11);
x_5 = x_16;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_push(x_4, x_19);
x_5 = x_20;
goto block_9;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
static lean_object* _init_l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0;
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_of_nat(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_lt(x_13, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
else
{
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_2 = 1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Diagnostics", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simplifier", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Applications", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cases instances", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("E-Matching instances", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("thm", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_12 = x_1;
} else {
 lean_dec_ref(x_1);
 x_12 = lean_box(0);
}
x_13 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(x_9);
lean_dec_ref(x_9);
x_14 = lean_array_mk(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_120 = lean_array_get_size(x_14);
x_121 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(x_14, x_15, x_120);
lean_dec(x_120);
lean_dec_ref(x_14);
x_136 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__20___redArg(x_10);
lean_dec_ref(x_10);
x_137 = lean_array_mk(x_136);
x_138 = lean_array_get_size(x_137);
x_139 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0;
x_140 = lean_nat_dec_lt(x_15, x_138);
if (x_140 == 0)
{
lean_dec(x_138);
lean_dec_ref(x_137);
x_122 = x_139;
goto block_135;
}
else
{
uint8_t x_141; 
x_141 = lean_nat_dec_le(x_138, x_138);
if (x_141 == 0)
{
lean_dec(x_138);
lean_dec_ref(x_137);
x_122 = x_139;
goto block_135;
}
else
{
size_t x_142; size_t x_143; lean_object* x_144; 
x_142 = 0;
x_143 = lean_usize_of_nat(x_138);
lean_dec(x_138);
x_144 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__4(x_137, x_142, x_143, x_139);
lean_dec_ref(x_137);
x_122 = x_144;
goto block_135;
}
}
block_26:
{
uint8_t x_18; 
x_18 = l_Array_isEmpty___redArg(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2;
x_20 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5;
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(9, 3, 0);
} else {
 x_21 = x_12;
 lean_ctor_set_tag(x_21, 9);
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_16);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
block_46:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_2);
x_34 = l_Lean_Meta_Simp_mkDiagMessages(x_33, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = l_Array_isEmpty___redArg(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2;
x_39 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__8;
x_40 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_35);
x_41 = lean_array_push(x_27, x_40);
x_16 = x_41;
x_17 = x_36;
goto block_26;
}
else
{
lean_dec(x_35);
x_16 = x_27;
x_17 = x_36;
goto block_26;
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_27);
lean_dec(x_12);
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
block_66:
{
uint8_t x_53; 
x_53 = l_Lean_PersistentHashMap_Node_isEmpty___redArg(x_11);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__9;
x_55 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__11;
x_56 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__20___redArg(x_11);
lean_dec_ref(x_11);
x_57 = lean_array_mk(x_56);
x_58 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_54, x_55, x_57, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_array_push(x_47, x_59);
x_27 = x_61;
x_28 = x_48;
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_60;
goto block_46;
}
else
{
uint8_t x_62; 
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_12);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_dec_ref(x_11);
x_27 = x_47;
x_28 = x_48;
x_29 = x_49;
x_30 = x_50;
x_31 = x_51;
x_32 = x_52;
goto block_46;
}
}
block_85:
{
uint8_t x_74; 
x_74 = l_Array_isEmpty___redArg(x_67);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__12;
x_76 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__14;
x_77 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_75, x_76, x_67, x_69, x_70, x_71, x_72, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_array_push(x_68, x_78);
x_47 = x_80;
x_48 = x_69;
x_49 = x_70;
x_50 = x_71;
x_51 = x_72;
x_52 = x_79;
goto block_66;
}
else
{
uint8_t x_81; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_dec_ref(x_67);
x_47 = x_68;
x_48 = x_69;
x_49 = x_70;
x_50 = x_71;
x_51 = x_72;
x_52 = x_73;
goto block_66;
}
}
block_103:
{
uint8_t x_94; 
x_94 = l_Array_isEmpty___redArg(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_inc_ref(x_92);
x_95 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData(x_93, x_89, x_87, x_92, x_86, x_91);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_array_push(x_88, x_96);
x_67 = x_90;
x_68 = x_98;
x_69 = x_89;
x_70 = x_87;
x_71 = x_92;
x_72 = x_86;
x_73 = x_97;
goto block_85;
}
else
{
uint8_t x_99; 
lean_dec_ref(x_92);
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_dec_ref(x_93);
x_67 = x_90;
x_68 = x_88;
x_69 = x_89;
x_70 = x_87;
x_71 = x_92;
x_72 = x_86;
x_73 = x_91;
goto block_85;
}
}
block_119:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = l_Lean_PersistentArray_toArray___redArg(x_3);
x_112 = lean_array_get_size(x_111);
x_113 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__15;
x_114 = lean_nat_dec_lt(x_15, x_112);
if (x_114 == 0)
{
lean_dec(x_112);
lean_dec_ref(x_111);
x_86 = x_109;
x_87 = x_107;
x_88 = x_105;
x_89 = x_106;
x_90 = x_104;
x_91 = x_110;
x_92 = x_108;
x_93 = x_113;
goto block_103;
}
else
{
uint8_t x_115; 
x_115 = lean_nat_dec_le(x_112, x_112);
if (x_115 == 0)
{
lean_dec(x_112);
lean_dec_ref(x_111);
x_86 = x_109;
x_87 = x_107;
x_88 = x_105;
x_89 = x_106;
x_90 = x_104;
x_91 = x_110;
x_92 = x_108;
x_93 = x_113;
goto block_103;
}
else
{
size_t x_116; size_t x_117; lean_object* x_118; 
x_116 = 0;
x_117 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_118 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(x_111, x_116, x_117, x_113);
lean_dec_ref(x_111);
x_86 = x_109;
x_87 = x_107;
x_88 = x_105;
x_89 = x_106;
x_90 = x_104;
x_91 = x_110;
x_92 = x_108;
x_93 = x_118;
goto block_103;
}
}
}
block_135:
{
lean_object* x_123; uint8_t x_124; 
x_123 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4;
x_124 = l_Array_isEmpty___redArg(x_121);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16;
x_126 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__18;
x_127 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_125, x_126, x_121, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = lean_array_push(x_123, x_128);
x_104 = x_122;
x_105 = x_130;
x_106 = x_4;
x_107 = x_5;
x_108 = x_6;
x_109 = x_7;
x_110 = x_129;
goto block_119;
}
else
{
uint8_t x_131; 
lean_dec_ref(x_122);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_131 = !lean_is_exclusive(x_127);
if (x_131 == 0)
{
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_127, 0);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_127);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_dec_ref(x_121);
x_104 = x_122;
x_105 = x_123;
x_106 = x_4;
x_107 = x_5;
x_108 = x_6;
x_109 = x_7;
x_110 = x_8;
goto block_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__4(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Result_hasFailed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailed___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Result_hasFailed(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_9 = l_List_reverse___redArg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = l_Lean_Meta_Grind_goalToMessageData(x_12, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_16);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_17;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_25);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_26 = l_Lean_Meta_Grind_goalToMessageData(x_23, x_25, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_24;
x_3 = x_29;
x_8 = x_28;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1;
x_9 = l_Lean_MessageData_joinSep(x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_36; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_12);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_36 = x_62;
goto block_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_7, 0);
lean_inc(x_63);
lean_dec(x_7);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_36 = x_65;
goto block_61;
}
block_35:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_19 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_10, x_11, x_12, x_14, x_15, x_16, x_17, x_18);
lean_dec_ref(x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_13, x_22, x_14, x_15, x_16, x_17, x_21);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec_ref(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_appendTR___redArg(x_13, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_28, x_29, x_14, x_15, x_16, x_17, x_24);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
block_61:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_38 = l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_9, sizeof(void*)*6 + 11);
lean_dec_ref(x_9);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec_ref(x_38);
x_42 = lean_box(0);
x_43 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_40, x_42, x_2, x_3, x_4, x_5, x_41);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec_ref(x_38);
x_46 = l_List_isEmpty___redArg(x_8);
if (x_46 == 0)
{
lean_object* x_47; double x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1;
x_48 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_49 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_50 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_float(x_50, sizeof(void*)*2, x_48);
lean_ctor_set_float(x_50, sizeof(void*)*2 + 8, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2 + 16, x_39);
x_51 = l_Lean_Meta_Grind_Result_toMessageData___closed__2;
x_52 = l_List_reverse___redArg(x_8);
x_53 = lean_array_mk(x_52);
x_54 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_37);
x_56 = l_List_appendTR___redArg(x_44, x_55);
x_13 = x_56;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_45;
goto block_35;
}
else
{
lean_dec(x_8);
x_13 = x_44;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_45;
goto block_35;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_MVarId_abstractMVars(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = l_Lean_MVarId_clearAuxDecls(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_17 = l_Lean_MVarId_revertAll(x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_20 = l_Lean_MVarId_unfoldReducible(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_23 = l_Lean_MVarId_betaReduce(x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1;
lean_inc(x_24);
x_27 = l_Lean_Meta_appendTagSuffix(x_24, x_26, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__0;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__2;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__3;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__4;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_110; uint8_t x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; uint8_t x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; uint8_t x_142; uint8_t x_158; 
x_133 = 2;
x_158 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_133);
if (x_158 == 0)
{
x_142 = x_158;
goto block_157;
}
else
{
uint8_t x_159; 
lean_inc_ref(x_2);
x_159 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_142 = x_159;
goto block_157;
}
block_80:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_take(x_18, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_17, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 7);
lean_inc(x_25);
lean_dec_ref(x_17);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_22, 6);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_16);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_14);
lean_ctor_set(x_29, 3, x_13);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_4);
x_30 = l_Lean_MessageLog_add(x_29, x_27);
lean_ctor_set(x_22, 6, x_30);
x_31 = lean_st_ref_set(x_18, x_22, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
x_41 = lean_ctor_get(x_22, 3);
x_42 = lean_ctor_get(x_22, 4);
x_43 = lean_ctor_get(x_22, 5);
x_44 = lean_ctor_get(x_22, 6);
x_45 = lean_ctor_get(x_22, 7);
x_46 = lean_ctor_get(x_22, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_16);
x_48 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set(x_48, 2, x_14);
lean_ctor_set(x_48, 3, x_13);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 2, x_4);
x_49 = l_Lean_MessageLog_add(x_48, x_44);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_40);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
lean_ctor_set(x_50, 6, x_49);
lean_ctor_set(x_50, 7, x_45);
lean_ctor_set(x_50, 8, x_46);
x_51 = lean_st_ref_set(x_18, x_50, x_23);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
x_58 = lean_ctor_get(x_17, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_17, 7);
lean_inc(x_59);
lean_dec_ref(x_17);
x_60 = lean_ctor_get(x_56, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_56, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_56, 4);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_56, 5);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_56, 6);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_56, 7);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_56, 8);
lean_inc_ref(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 lean_ctor_release(x_56, 7);
 lean_ctor_release(x_56, 8);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_16);
x_72 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_72, 0, x_12);
lean_ctor_set(x_72, 1, x_11);
lean_ctor_set(x_72, 2, x_14);
lean_ctor_set(x_72, 3, x_13);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 2, x_4);
x_73 = l_Lean_MessageLog_add(x_72, x_66);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 9, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_61);
lean_ctor_set(x_74, 2, x_62);
lean_ctor_set(x_74, 3, x_63);
lean_ctor_set(x_74, 4, x_64);
lean_ctor_set(x_74, 5, x_65);
lean_ctor_set(x_74, 6, x_73);
lean_ctor_set(x_74, 7, x_67);
lean_ctor_set(x_74, 8, x_68);
x_75 = lean_st_ref_set(x_18, x_74, x_57);
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
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
block_109:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_90 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_89, x_5, x_6, x_7, x_8, x_9);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc_ref(x_85);
x_94 = l_Lean_FileMap_toPosition(x_85, x_87);
lean_dec(x_87);
x_95 = l_Lean_FileMap_toPosition(x_85, x_88);
lean_dec(x_88);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
if (x_83 == 0)
{
lean_free_object(x_90);
lean_dec(x_81);
x_10 = x_82;
x_11 = x_94;
x_12 = x_84;
x_13 = x_97;
x_14 = x_96;
x_15 = x_86;
x_16 = x_92;
x_17 = x_7;
x_18 = x_8;
x_19 = x_93;
goto block_80;
}
else
{
uint8_t x_98; 
lean_inc(x_92);
x_98 = l_Lean_MessageData_hasTag(x_81, x_92);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec_ref(x_84);
lean_dec_ref(x_7);
x_99 = lean_box(0);
lean_ctor_set(x_90, 0, x_99);
return x_90;
}
else
{
lean_free_object(x_90);
x_10 = x_82;
x_11 = x_94;
x_12 = x_84;
x_13 = x_97;
x_14 = x_96;
x_15 = x_86;
x_16 = x_92;
x_17 = x_7;
x_18 = x_8;
x_19 = x_93;
goto block_80;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_90, 0);
x_101 = lean_ctor_get(x_90, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_90);
lean_inc_ref(x_85);
x_102 = l_Lean_FileMap_toPosition(x_85, x_87);
lean_dec(x_87);
x_103 = l_Lean_FileMap_toPosition(x_85, x_88);
lean_dec(x_88);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
if (x_83 == 0)
{
lean_dec(x_81);
x_10 = x_82;
x_11 = x_102;
x_12 = x_84;
x_13 = x_105;
x_14 = x_104;
x_15 = x_86;
x_16 = x_100;
x_17 = x_7;
x_18 = x_8;
x_19 = x_101;
goto block_80;
}
else
{
uint8_t x_106; 
lean_inc(x_100);
x_106 = l_Lean_MessageData_hasTag(x_81, x_100);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec(x_100);
lean_dec_ref(x_84);
lean_dec_ref(x_7);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_101);
return x_108;
}
else
{
x_10 = x_82;
x_11 = x_102;
x_12 = x_84;
x_13 = x_105;
x_14 = x_104;
x_15 = x_86;
x_16 = x_100;
x_17 = x_7;
x_18 = x_8;
x_19 = x_101;
goto block_80;
}
}
}
}
block_120:
{
lean_object* x_118; 
x_118 = l_Lean_Syntax_getTailPos_x3f(x_112, x_116);
lean_dec(x_112);
if (lean_obj_tag(x_118) == 0)
{
lean_inc(x_117);
x_81 = x_110;
x_82 = x_111;
x_83 = x_113;
x_84 = x_114;
x_85 = x_115;
x_86 = x_116;
x_87 = x_117;
x_88 = x_117;
goto block_109;
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_81 = x_110;
x_82 = x_111;
x_83 = x_113;
x_84 = x_114;
x_85 = x_115;
x_86 = x_116;
x_87 = x_117;
x_88 = x_119;
goto block_109;
}
}
block_132:
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_replaceRef(x_1, x_122);
lean_dec(x_122);
x_129 = l_Lean_Syntax_getPos_x3f(x_128, x_126);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_unsigned_to_nat(0u);
x_110 = x_121;
x_111 = x_127;
x_112 = x_128;
x_113 = x_123;
x_114 = x_124;
x_115 = x_125;
x_116 = x_126;
x_117 = x_130;
goto block_120;
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_110 = x_121;
x_111 = x_127;
x_112 = x_128;
x_113 = x_123;
x_114 = x_124;
x_115 = x_125;
x_116 = x_126;
x_117 = x_131;
goto block_120;
}
}
block_141:
{
if (x_140 == 0)
{
x_121 = x_137;
x_122 = x_134;
x_123 = x_135;
x_124 = x_136;
x_125 = x_138;
x_126 = x_139;
x_127 = x_3;
goto block_132;
}
else
{
x_121 = x_137;
x_122 = x_134;
x_123 = x_135;
x_124 = x_136;
x_125 = x_138;
x_126 = x_139;
x_127 = x_133;
goto block_132;
}
}
block_157:
{
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_143 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_7, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_7, 5);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_148 = lean_box(x_142);
x_149 = lean_box(x_147);
x_150 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_150, 0, x_148);
lean_closure_set(x_150, 1, x_149);
x_151 = 1;
x_152 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_151);
if (x_152 == 0)
{
lean_dec(x_145);
x_134 = x_146;
x_135 = x_147;
x_136 = x_143;
x_137 = x_150;
x_138 = x_144;
x_139 = x_142;
x_140 = x_152;
goto block_141;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0;
x_154 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_145, x_153);
lean_dec(x_145);
x_134 = x_146;
x_135 = x_147;
x_136 = x_143;
x_137 = x_150;
x_138 = x_144;
x_139 = x_142;
x_140 = x_154;
goto block_141;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_9);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 5);
lean_inc(x_12);
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_12, x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = 0;
x_12 = l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
lean_ctor_set_uint8(x_14, 9, x_1);
x_17 = 2;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_shift_left(x_18, x_17);
x_20 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_21 = lean_uint64_lor(x_19, x_20);
lean_ctor_set_uint64(x_8, sizeof(void*)*7, x_21);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_22 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_Grind_solve(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_st_ref_get(x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_st_ref_get(x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_st_ref_get(x_7, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_st_ref_get(x_7, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_st_ref_get(x_7, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 2);
lean_inc_ref(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_29, 4);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_ctor_get(x_32, 5);
lean_inc_ref(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_35, 6);
lean_inc_ref(x_48);
lean_dec(x_35);
x_49 = lean_ctor_get(x_39, 7);
lean_inc_ref(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_43, 5);
lean_inc_ref(x_51);
lean_dec_ref(x_43);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_50);
if (lean_obj_tag(x_26) == 0)
{
goto block_82;
}
else
{
if (x_4 == 0)
{
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_52 = x_44;
goto block_65;
}
else
{
goto block_82;
}
}
block_65:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_3);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_3, 0);
x_55 = lean_ctor_get(x_3, 6);
lean_dec(x_55);
x_56 = lean_ctor_get(x_3, 5);
lean_dec(x_56);
x_57 = lean_ctor_get(x_3, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_3, 1);
lean_dec(x_60);
lean_ctor_set(x_3, 6, x_49);
lean_ctor_set(x_3, 5, x_37);
lean_ctor_set(x_3, 4, x_48);
lean_ctor_set(x_3, 3, x_47);
lean_ctor_set(x_3, 2, x_54);
lean_ctor_set(x_3, 1, x_46);
lean_ctor_set(x_3, 0, x_26);
if (lean_is_scalar(x_45)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_45;
}
lean_ctor_set(x_61, 0, x_3);
lean_ctor_set(x_61, 1, x_52);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec(x_3);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_46);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_47);
lean_ctor_set(x_63, 4, x_48);
lean_ctor_set(x_63, 5, x_37);
lean_ctor_set(x_63, 6, x_49);
if (lean_is_scalar(x_45)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_45;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
return x_64;
}
}
block_82:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_44);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_52 = x_69;
goto block_65;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec_ref(x_66);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_37);
lean_inc_ref(x_48);
x_71 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_48, x_37, x_49, x_8, x_9, x_10, x_11, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_52 = x_73;
goto block_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec_ref(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_75, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_52 = x_77;
goto block_65;
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_37);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_26);
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_71, 0);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_71);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_83 = lean_ctor_get(x_37, 0);
x_84 = lean_ctor_get(x_37, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_37);
x_85 = lean_st_ref_get(x_7, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc_ref(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_29, 4);
lean_inc(x_90);
lean_dec(x_29);
x_91 = lean_ctor_get(x_32, 5);
lean_inc_ref(x_91);
lean_dec(x_32);
x_92 = lean_ctor_get(x_35, 6);
lean_inc_ref(x_92);
lean_dec(x_35);
x_93 = lean_ctor_get(x_83, 7);
lean_inc_ref(x_93);
lean_dec(x_83);
x_94 = lean_ctor_get(x_87, 3);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_87, 5);
lean_inc_ref(x_95);
lean_dec_ref(x_87);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
if (lean_obj_tag(x_26) == 0)
{
goto block_119;
}
else
{
if (x_4 == 0)
{
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_97 = x_88;
goto block_102;
}
else
{
goto block_119;
}
}
block_102:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_98);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_99 = x_3;
} else {
 lean_dec_ref(x_3);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 7, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_26);
lean_ctor_set(x_100, 1, x_90);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_91);
lean_ctor_set(x_100, 4, x_92);
lean_ctor_set(x_100, 5, x_96);
lean_ctor_set(x_100, 6, x_93);
if (lean_is_scalar(x_89)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_89;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
block_119:
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_88);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec_ref(x_103);
x_97 = x_106;
goto block_102;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec_ref(x_103);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_96);
lean_inc_ref(x_92);
x_108 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_92, x_96, x_93, x_8, x_9, x_10, x_11, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_97 = x_110;
goto block_102;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec_ref(x_108);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_112, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec_ref(x_113);
x_97 = x_114;
goto block_102;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_96);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_26);
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
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
}
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_120 = !lean_is_exclusive(x_25);
if (x_120 == 0)
{
return x_25;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_25, 0);
x_122 = lean_ctor_get(x_25, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_25);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_124 = !lean_is_exclusive(x_22);
if (x_124 == 0)
{
return x_22;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_22, 0);
x_126 = lean_ctor_get(x_22, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_22);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint64_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; lean_object* x_153; 
x_128 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_129 = lean_ctor_get_uint8(x_14, 0);
x_130 = lean_ctor_get_uint8(x_14, 1);
x_131 = lean_ctor_get_uint8(x_14, 2);
x_132 = lean_ctor_get_uint8(x_14, 3);
x_133 = lean_ctor_get_uint8(x_14, 4);
x_134 = lean_ctor_get_uint8(x_14, 5);
x_135 = lean_ctor_get_uint8(x_14, 6);
x_136 = lean_ctor_get_uint8(x_14, 7);
x_137 = lean_ctor_get_uint8(x_14, 8);
x_138 = lean_ctor_get_uint8(x_14, 10);
x_139 = lean_ctor_get_uint8(x_14, 11);
x_140 = lean_ctor_get_uint8(x_14, 12);
x_141 = lean_ctor_get_uint8(x_14, 13);
x_142 = lean_ctor_get_uint8(x_14, 14);
x_143 = lean_ctor_get_uint8(x_14, 15);
x_144 = lean_ctor_get_uint8(x_14, 16);
x_145 = lean_ctor_get_uint8(x_14, 17);
x_146 = lean_ctor_get_uint8(x_14, 18);
lean_dec(x_14);
x_147 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_147, 0, x_129);
lean_ctor_set_uint8(x_147, 1, x_130);
lean_ctor_set_uint8(x_147, 2, x_131);
lean_ctor_set_uint8(x_147, 3, x_132);
lean_ctor_set_uint8(x_147, 4, x_133);
lean_ctor_set_uint8(x_147, 5, x_134);
lean_ctor_set_uint8(x_147, 6, x_135);
lean_ctor_set_uint8(x_147, 7, x_136);
lean_ctor_set_uint8(x_147, 8, x_137);
lean_ctor_set_uint8(x_147, 9, x_1);
lean_ctor_set_uint8(x_147, 10, x_138);
lean_ctor_set_uint8(x_147, 11, x_139);
lean_ctor_set_uint8(x_147, 12, x_140);
lean_ctor_set_uint8(x_147, 13, x_141);
lean_ctor_set_uint8(x_147, 14, x_142);
lean_ctor_set_uint8(x_147, 15, x_143);
lean_ctor_set_uint8(x_147, 16, x_144);
lean_ctor_set_uint8(x_147, 17, x_145);
lean_ctor_set_uint8(x_147, 18, x_146);
x_148 = 2;
x_149 = lean_uint64_shift_right(x_128, x_148);
x_150 = lean_uint64_shift_left(x_149, x_148);
x_151 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_152 = lean_uint64_lor(x_150, x_151);
lean_ctor_set(x_8, 0, x_147);
lean_ctor_set_uint64(x_8, sizeof(void*)*7, x_152);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_153 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_156 = l_Lean_Meta_Grind_solve(x_154, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = lean_st_ref_get(x_7, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_st_ref_get(x_7, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
x_165 = lean_st_ref_get(x_7, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_st_ref_get(x_7, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_st_ref_get(x_7, x_170);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 2);
lean_inc_ref(x_174);
lean_dec(x_173);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_176 = x_172;
} else {
 lean_dec_ref(x_172);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_160, 4);
lean_inc(x_177);
lean_dec(x_160);
x_178 = lean_ctor_get(x_163, 5);
lean_inc_ref(x_178);
lean_dec(x_163);
x_179 = lean_ctor_get(x_166, 6);
lean_inc_ref(x_179);
lean_dec(x_166);
x_180 = lean_ctor_get(x_169, 7);
lean_inc_ref(x_180);
lean_dec(x_169);
x_181 = lean_ctor_get(x_174, 3);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_174, 5);
lean_inc_ref(x_182);
lean_dec_ref(x_174);
if (lean_is_scalar(x_171)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_171;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
if (lean_obj_tag(x_157) == 0)
{
goto block_206;
}
else
{
if (x_4 == 0)
{
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_184 = x_175;
goto block_189;
}
else
{
goto block_206;
}
}
block_189:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_185);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_186 = x_3;
} else {
 lean_dec_ref(x_3);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 7, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_157);
lean_ctor_set(x_187, 1, x_177);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set(x_187, 4, x_179);
lean_ctor_set(x_187, 5, x_183);
lean_ctor_set(x_187, 6, x_180);
if (lean_is_scalar(x_176)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_176;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
return x_188;
}
block_206:
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_175);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec_ref(x_190);
x_184 = x_193;
goto block_189;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec_ref(x_190);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_183);
lean_inc_ref(x_179);
x_195 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_179, x_183, x_180, x_8, x_9, x_10, x_11, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_184 = x_197;
goto block_189;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec_ref(x_195);
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
lean_dec(x_196);
x_200 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_199, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_198);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
x_184 = x_201;
goto block_189;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec_ref(x_183);
lean_dec_ref(x_180);
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_157);
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_202 = lean_ctor_get(x_195, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_195, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_204 = x_195;
} else {
 lean_dec_ref(x_195);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_207 = lean_ctor_get(x_156, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_156, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_209 = x_156;
} else {
 lean_dec_ref(x_156);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_8);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_211 = lean_ctor_get(x_153, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_153, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_213 = x_153;
} else {
 lean_dec_ref(x_153);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
}
else
{
lean_object* x_215; uint64_t x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; uint64_t x_246; uint64_t x_247; uint64_t x_248; uint64_t x_249; uint64_t x_250; lean_object* x_251; lean_object* x_252; 
x_215 = lean_ctor_get(x_8, 0);
x_216 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_217 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_218 = lean_ctor_get(x_8, 1);
x_219 = lean_ctor_get(x_8, 2);
x_220 = lean_ctor_get(x_8, 3);
x_221 = lean_ctor_get(x_8, 4);
x_222 = lean_ctor_get(x_8, 5);
x_223 = lean_ctor_get(x_8, 6);
x_224 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_225 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_215);
lean_dec(x_8);
x_226 = lean_ctor_get_uint8(x_215, 0);
x_227 = lean_ctor_get_uint8(x_215, 1);
x_228 = lean_ctor_get_uint8(x_215, 2);
x_229 = lean_ctor_get_uint8(x_215, 3);
x_230 = lean_ctor_get_uint8(x_215, 4);
x_231 = lean_ctor_get_uint8(x_215, 5);
x_232 = lean_ctor_get_uint8(x_215, 6);
x_233 = lean_ctor_get_uint8(x_215, 7);
x_234 = lean_ctor_get_uint8(x_215, 8);
x_235 = lean_ctor_get_uint8(x_215, 10);
x_236 = lean_ctor_get_uint8(x_215, 11);
x_237 = lean_ctor_get_uint8(x_215, 12);
x_238 = lean_ctor_get_uint8(x_215, 13);
x_239 = lean_ctor_get_uint8(x_215, 14);
x_240 = lean_ctor_get_uint8(x_215, 15);
x_241 = lean_ctor_get_uint8(x_215, 16);
x_242 = lean_ctor_get_uint8(x_215, 17);
x_243 = lean_ctor_get_uint8(x_215, 18);
if (lean_is_exclusive(x_215)) {
 x_244 = x_215;
} else {
 lean_dec_ref(x_215);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 0, 19);
} else {
 x_245 = x_244;
}
lean_ctor_set_uint8(x_245, 0, x_226);
lean_ctor_set_uint8(x_245, 1, x_227);
lean_ctor_set_uint8(x_245, 2, x_228);
lean_ctor_set_uint8(x_245, 3, x_229);
lean_ctor_set_uint8(x_245, 4, x_230);
lean_ctor_set_uint8(x_245, 5, x_231);
lean_ctor_set_uint8(x_245, 6, x_232);
lean_ctor_set_uint8(x_245, 7, x_233);
lean_ctor_set_uint8(x_245, 8, x_234);
lean_ctor_set_uint8(x_245, 9, x_1);
lean_ctor_set_uint8(x_245, 10, x_235);
lean_ctor_set_uint8(x_245, 11, x_236);
lean_ctor_set_uint8(x_245, 12, x_237);
lean_ctor_set_uint8(x_245, 13, x_238);
lean_ctor_set_uint8(x_245, 14, x_239);
lean_ctor_set_uint8(x_245, 15, x_240);
lean_ctor_set_uint8(x_245, 16, x_241);
lean_ctor_set_uint8(x_245, 17, x_242);
lean_ctor_set_uint8(x_245, 18, x_243);
x_246 = 2;
x_247 = lean_uint64_shift_right(x_216, x_246);
x_248 = lean_uint64_shift_left(x_247, x_246);
x_249 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_250 = lean_uint64_lor(x_248, x_249);
x_251 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_251, 0, x_245);
lean_ctor_set(x_251, 1, x_218);
lean_ctor_set(x_251, 2, x_219);
lean_ctor_set(x_251, 3, x_220);
lean_ctor_set(x_251, 4, x_221);
lean_ctor_set(x_251, 5, x_222);
lean_ctor_set(x_251, 6, x_223);
lean_ctor_set_uint64(x_251, sizeof(void*)*7, x_250);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 8, x_217);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 9, x_224);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 10, x_225);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_251);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_252 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_5, x_6, x_7, x_251, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec_ref(x_252);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_251);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_255 = l_Lean_Meta_Grind_solve(x_253, x_5, x_6, x_7, x_251, x_9, x_10, x_11, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec_ref(x_255);
x_258 = lean_st_ref_get(x_7, x_257);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec_ref(x_258);
x_261 = lean_st_ref_get(x_7, x_260);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec_ref(x_261);
x_264 = lean_st_ref_get(x_7, x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = lean_st_ref_get(x_7, x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = lean_st_ref_get(x_7, x_269);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 2);
lean_inc_ref(x_273);
lean_dec(x_272);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_275 = x_271;
} else {
 lean_dec_ref(x_271);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_259, 4);
lean_inc(x_276);
lean_dec(x_259);
x_277 = lean_ctor_get(x_262, 5);
lean_inc_ref(x_277);
lean_dec(x_262);
x_278 = lean_ctor_get(x_265, 6);
lean_inc_ref(x_278);
lean_dec(x_265);
x_279 = lean_ctor_get(x_268, 7);
lean_inc_ref(x_279);
lean_dec(x_268);
x_280 = lean_ctor_get(x_273, 3);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_273, 5);
lean_inc_ref(x_281);
lean_dec_ref(x_273);
if (lean_is_scalar(x_270)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_270;
}
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
if (lean_obj_tag(x_256) == 0)
{
goto block_305;
}
else
{
if (x_4 == 0)
{
lean_dec_ref(x_251);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_283 = x_274;
goto block_288;
}
else
{
goto block_305;
}
}
block_288:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_284);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_285 = x_3;
} else {
 lean_dec_ref(x_3);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 7, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_256);
lean_ctor_set(x_286, 1, x_276);
lean_ctor_set(x_286, 2, x_284);
lean_ctor_set(x_286, 3, x_277);
lean_ctor_set(x_286, 4, x_278);
lean_ctor_set(x_286, 5, x_282);
lean_ctor_set(x_286, 6, x_279);
if (lean_is_scalar(x_275)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_275;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_283);
return x_287;
}
block_305:
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_289 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_274);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_unbox(x_290);
lean_dec(x_290);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec_ref(x_251);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec_ref(x_289);
x_283 = x_292;
goto block_288;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_289, 1);
lean_inc(x_293);
lean_dec_ref(x_289);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_251);
lean_inc_ref(x_282);
lean_inc_ref(x_278);
x_294 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_278, x_282, x_279, x_251, x_9, x_10, x_11, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
lean_dec_ref(x_251);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec_ref(x_294);
x_283 = x_296;
goto block_288;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec_ref(x_294);
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
lean_dec(x_295);
x_299 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_298, x_5, x_6, x_7, x_251, x_9, x_10, x_11, x_297);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_251);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec_ref(x_299);
x_283 = x_300;
goto block_288;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec_ref(x_282);
lean_dec_ref(x_279);
lean_dec_ref(x_278);
lean_dec_ref(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_256);
lean_dec_ref(x_251);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_301 = lean_ctor_get(x_294, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_294, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_303 = x_294;
} else {
 lean_dec_ref(x_294);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_251);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_306 = lean_ctor_get(x_255, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_255, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_308 = x_255;
} else {
 lean_dec_ref(x_255);
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
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec_ref(x_251);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_310 = lean_ctor_get(x_252, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_252, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_312 = x_252;
} else {
 lean_dec_ref(x_252);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_debug_terminalTacticsAsSorry;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_2 = l_Lean_Meta_Grind_main___lam__1___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_main___lam__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_main___lam__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_main___lam__1___closed__5;
x_2 = l_Lean_Meta_Grind_main___lam__1___closed__4;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_main___lam__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_main___lam__1___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__36;
x_2 = l_Lean_Meta_Grind_main___lam__1___closed__5;
x_3 = l_Lean_Meta_Grind_main___lam__1___closed__7;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_main___lam__1___closed__9;
x_2 = l_Lean_Meta_Grind_main___lam__1___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = l_Lean_Meta_Grind_main___lam__1___closed__0;
x_11 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 2;
x_13 = lean_box(x_12);
x_14 = lean_box(x_11);
lean_inc_ref(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lam__0___boxed), 12, 4);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lean_Meta_Grind_GrindM_run___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = l_Lean_MVarId_admit(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 6);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 5);
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 4);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Grind_main___lam__1___closed__2;
x_31 = l_Lean_Meta_Grind_main___lam__1___closed__6;
x_32 = l_Lean_Meta_Grind_main___lam__1___closed__10;
x_33 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__43;
lean_ctor_set(x_2, 6, x_33);
lean_ctor_set(x_2, 5, x_32);
lean_ctor_set(x_2, 4, x_31);
lean_ctor_set(x_2, 3, x_30);
lean_ctor_set(x_2, 2, x_21);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_28);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_Grind_main___lam__1___closed__2;
x_38 = l_Lean_Meta_Grind_main___lam__1___closed__6;
x_39 = l_Lean_Meta_Grind_main___lam__1___closed__10;
x_40 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__43;
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
lean_ctor_set(x_41, 6, x_40);
lean_ctor_set(x_17, 0, x_41);
return x_17;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_44 = x_2;
} else {
 lean_dec_ref(x_2);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_Grind_main___lam__1___closed__2;
x_48 = l_Lean_Meta_Grind_main___lam__1___closed__6;
x_49 = l_Lean_Meta_Grind_main___lam__1___closed__10;
x_50 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__43;
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(0, 7, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_47);
lean_ctor_set(x_51, 4, x_48);
lean_ctor_set(x_51, 5, x_49);
lean_ctor_set(x_51, 6, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lam__1), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0;
x_12 = lean_box(0);
x_13 = l_Lean_profileitM___at___Lean_Meta_letToHave_spec__1___redArg(x_11, x_9, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_3);
x_14 = l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Meta_Grind_main___lam__0(x_13, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ReflCmp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Solve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_mkParams___closed__0 = _init_l_Lean_Meta_Grind_mkParams___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__0);
l_Lean_Meta_Grind_mkParams___closed__1 = _init_l_Lean_Meta_Grind_mkParams___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__1);
l_Lean_Meta_Grind_mkParams___closed__2 = _init_l_Lean_Meta_Grind_mkParams___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__2);
l_Lean_Meta_Grind_mkParams___closed__3 = _init_l_Lean_Meta_Grind_mkParams___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__3);
l_Lean_Meta_Grind_mkParams___closed__4 = _init_l_Lean_Meta_Grind_mkParams___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__4);
l_Lean_Meta_Grind_mkParams___closed__5 = _init_l_Lean_Meta_Grind_mkParams___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__5);
l_Lean_Meta_Grind_mkParams___closed__6 = _init_l_Lean_Meta_Grind_mkParams___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__6);
l_Lean_Meta_Grind_mkParams___closed__7 = _init_l_Lean_Meta_Grind_mkParams___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__7);
l_Lean_Meta_Grind_mkParams___closed__8 = _init_l_Lean_Meta_Grind_mkParams___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__8);
l_Lean_Meta_Grind_mkParams___closed__9 = _init_l_Lean_Meta_Grind_mkParams___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___closed__9);
l_Lean_Meta_Grind_mkMethods___redArg___closed__0 = _init_l_Lean_Meta_Grind_mkMethods___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mkMethods___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4);
l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__0 = _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__0);
l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__1 = _init_l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0___closed__1);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__0 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__0);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__1 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__1);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__2 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__2);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__3 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__3);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__4 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__4);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__5 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__5);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__6 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__6);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__7 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__7);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__8 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__8);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__9 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__9);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__10 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__10);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__11 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__11);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__12 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__12);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__13 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__13);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__14 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__14);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__15 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__15);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__16 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__16);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__17 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__17);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__18 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__18);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__19 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__19);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__20 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__20);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__21 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__21();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__21);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__22 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__22();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__22);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__23 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__23();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__23);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__24 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__24();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__24);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__25 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__25();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__25);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__26 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__26();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__26);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__27 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__27();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__27);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__28 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__28();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__28);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__29 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__29();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__29);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__30 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__30();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__30);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__31 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__31();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__31);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__32 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__32();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__32);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__33 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__33();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__33);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__34 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__34();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__34);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__35 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__35();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__35);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__36 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__36();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__36);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__37 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__37();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__37);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__38 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__38();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__38);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__39 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__39();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__39);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__40 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__40();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__40);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__41 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__41();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__41);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__42 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__42();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__42);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__43 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__43();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__43);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__44 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__44();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__44);
l_Lean_Meta_Grind_GrindM_run___redArg___closed__45 = _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__45();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___redArg___closed__45);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___closed__1);
l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__0 = _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__0);
l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1 = _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1);
l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__0 = _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__0);
l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__1 = _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1___closed__1);
l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__0 = _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__0);
l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1 = _init_l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__6);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__13);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__15);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__21 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__21();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__21);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__22 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__22();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__22);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__23 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__23();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__23);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__26 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__26();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__26);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__47 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__47();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__47);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__48 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__48();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__48);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__2 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__2);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__3);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__4);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0();
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__0 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__0);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__1 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__1);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__3 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__3);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__4 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__4);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__5 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__5);
l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__3);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__5);
l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0 = _init_l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0();
lean_mark_persistent(l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__0);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__3);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__8);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__9);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__11);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__12);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__13);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__14);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__15);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__18 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__18);
l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0 = _init_l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0);
l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1 = _init_l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1);
l_Lean_Meta_Grind_Result_toMessageData___closed__0 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__0);
l_Lean_Meta_Grind_Result_toMessageData___closed__1 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__1);
l_Lean_Meta_Grind_Result_toMessageData___closed__2 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__2);
l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__0);
l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__1 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__1);
l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__2 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__2);
l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__3 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__3);
l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__4 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___closed__4);
l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0);
l_Lean_Meta_Grind_main___lam__1___closed__0 = _init_l_Lean_Meta_Grind_main___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__0);
l_Lean_Meta_Grind_main___lam__1___closed__1 = _init_l_Lean_Meta_Grind_main___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__1);
l_Lean_Meta_Grind_main___lam__1___closed__2 = _init_l_Lean_Meta_Grind_main___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__2);
l_Lean_Meta_Grind_main___lam__1___closed__3 = _init_l_Lean_Meta_Grind_main___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__3);
l_Lean_Meta_Grind_main___lam__1___closed__4 = _init_l_Lean_Meta_Grind_main___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__4);
l_Lean_Meta_Grind_main___lam__1___closed__5 = _init_l_Lean_Meta_Grind_main___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__5);
l_Lean_Meta_Grind_main___lam__1___closed__6 = _init_l_Lean_Meta_Grind_main___lam__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__6);
l_Lean_Meta_Grind_main___lam__1___closed__7 = _init_l_Lean_Meta_Grind_main___lam__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__7);
l_Lean_Meta_Grind_main___lam__1___closed__8 = _init_l_Lean_Meta_Grind_main___lam__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__8);
l_Lean_Meta_Grind_main___lam__1___closed__9 = _init_l_Lean_Meta_Grind_main___lam__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__9);
l_Lean_Meta_Grind_main___lam__1___closed__10 = _init_l_Lean_Meta_Grind_main___lam__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_main___lam__1___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
