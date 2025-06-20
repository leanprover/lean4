// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Main
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Util Lean.Meta.Tactic.ExposeNames Lean.Meta.Tactic.Simp.Diagnostics Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Proj Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.Solve Lean.Meta.Tactic.Grind.SimpUtil Lean.Meta.Tactic.Grind.Cases
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27;
lean_object* l_Lean_Meta_Grind_getBoolFalseExpr___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__6;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__7;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__17;
lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_5528__spec__0(lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__3;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___closed__1;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkENodeCore___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__22;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__25;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__4;
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__3;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__12;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailed___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommonAlpha_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__7;
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
lean_object* l_Lean_Meta_Grind_getBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__17;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__37;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__7;
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__16;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__5;
lean_object* l_Lean_MVarId_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__5;
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
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_discharge_x3f___closed__4;
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0___closed__1;
extern lean_object* l_Lean_Meta_Grind_builtinPropagatorsRef;
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_shareCommon_spec__0(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__0;
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
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__1;
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
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_main___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__10;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___redArg___closed__2;
lean_object* l_Lean_Meta_Grind_getSimpContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__24;
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___closed__31;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
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
lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_dischargeRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0___closed__2;
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_exposeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4___boxed(lean_object**);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8;
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_5528__spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_mkParams___redArg___closed__3;
x_2 = l_Lean_Meta_Grind_mkParams___redArg___closed__2;
x_3 = l_Lean_Meta_Grind_mkParams___redArg___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___redArg___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___redArg___closed__8() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_mkParams___redArg___closed__6;
x_4 = l_Lean_Meta_Grind_mkParams___redArg___closed__7;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Meta_Grind_getSimpContext___redArg(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_Grind_getSimprocs___redArg(x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Meta_Grind_mkParams___redArg___closed__4;
x_13 = l_Lean_Meta_Grind_mkParams___redArg___closed__5;
x_14 = l_Lean_Meta_Grind_mkParams___redArg___closed__8;
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_7);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = l_Lean_Meta_Grind_mkParams___redArg___closed__4;
x_19 = l_Lean_Meta_Grind_mkParams___redArg___closed__5;
x_20 = l_Lean_Meta_Grind_mkParams___redArg___closed__8;
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_7);
lean_ctor_set(x_21, 5, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_mkParams___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_mkParams___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_mkParams(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_2);
x_12 = l_Lean_Meta_Grind_propagateForallPropUp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash___override(x_17);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = 1;
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_23, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_17, x_37);
lean_dec(x_37);
lean_dec(x_17);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set(x_18, 0, x_39);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_18);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_apply_10(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_ctor_get(x_42, 1);
x_45 = lean_array_get_size(x_44);
x_46 = l_Lean_Name_hash___override(x_17);
x_47 = 32;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = 16;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = 1;
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_44, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_17, x_58);
lean_dec(x_58);
lean_dec(x_17);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_43);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_apply_10(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
return x_63;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_10);
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
}
else
{
lean_object* x_64; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(0);
lean_ctor_set(x_12, 0, x_64);
return x_12;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
lean_dec(x_12);
x_66 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_66) == 4)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_68 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; 
x_69 = lean_ctor_get(x_1, 0);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_array_get_size(x_72);
x_74 = l_Lean_Name_hash___override(x_67);
x_75 = 32;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_72, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_67, x_86);
lean_dec(x_86);
lean_dec(x_67);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_71;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_70);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_71);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_apply_10(x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
return x_91;
}
}
else
{
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_68;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_66);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_65);
return x_93;
}
}
}
else
{
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_2);
x_12 = l_Lean_Meta_Grind_propagateForallPropDown(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_array_get_size(x_19);
x_21 = l_Lean_Name_hash___override(x_18);
x_22 = 32;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = 16;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = 1;
x_31 = lean_usize_sub(x_29, x_30);
x_32 = lean_usize_land(x_28, x_31);
x_33 = lean_array_uget(x_19, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_18, x_33);
lean_dec(x_33);
lean_dec(x_18);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_12, 0, x_35);
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_12);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_10(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_array_get_size(x_43);
x_45 = l_Lean_Name_hash___override(x_42);
x_46 = 32;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = 16;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_54 = 1;
x_55 = lean_usize_sub(x_53, x_54);
x_56 = lean_usize_land(x_52, x_55);
x_57 = lean_array_uget(x_43, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_42, x_57);
lean_dec(x_57);
lean_dec(x_42);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_39);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_apply_10(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_39);
return x_64;
}
}
}
else
{
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
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkMethods___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_mkMethods(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_11 = lean_simp(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_15 = l_Lean_Meta_Simp_dischargeRfl(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_isTrue(x_14);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_Simp_Result_getProof(x_12, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_15);
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
lean_dec(x_14);
lean_dec(x_10);
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
lean_dec(x_14);
lean_dec(x_10);
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
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__20;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__21;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__22;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__23;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__25;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__24;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__27;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__30;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__32() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__30;
x_4 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__31;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__32;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__29;
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__27;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__33;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__28;
x_4 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__24;
x_5 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__26;
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
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_192__spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__29;
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__36;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__30;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__39() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__30;
x_4 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__38;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___redArg___closed__40() {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
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
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__14;
x_17 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__17;
x_21 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__18;
x_25 = l_Lean_Meta_Grind_shareCommonAlpha_go(x_24, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_mkMethods___redArg(x_3, x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(1);
x_32 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__19;
x_33 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__34;
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_37 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__37;
x_40 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_38);
lean_ctor_set(x_41, 6, x_39);
lean_ctor_set(x_41, 7, x_40);
x_42 = lean_st_mk_ref(x_41, x_30);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 5);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__40;
x_49 = lean_unbox(x_31);
x_50 = l_Lean_Meta_Simp_mkMethods(x_47, x_48, x_49);
x_51 = lean_box(0);
x_52 = lean_box(6);
x_53 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_14);
lean_ctor_set(x_53, 5, x_10);
lean_ctor_set(x_53, 6, x_26);
lean_ctor_set(x_53, 7, x_22);
lean_ctor_set(x_53, 8, x_18);
x_54 = lean_unbox(x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*9, x_54);
x_55 = lean_unbox(x_31);
lean_ctor_set_uint8(x_53, sizeof(void*)*9 + 1, x_55);
lean_inc(x_43);
x_56 = lean_apply_8(x_1, x_29, x_53, x_43, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_43, x_58);
lean_dec(x_43);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_dec(x_43);
return x_56;
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_20);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_39);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_37);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_12);
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
lean_dec(x_36);
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
lean_dec(x_58);
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
lean_dec(x_83);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
lean_dec(x_9);
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
lean_dec(x_41);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_12);
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
lean_dec(x_11);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
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
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
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
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_1);
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
lean_dec(x_2);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
lean_inc(x_2);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_24);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
lean_inc(x_2);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_43);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_22);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_41);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_2);
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
lean_dec(x_16);
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
lean_dec(x_40);
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
lean_dec(x_62);
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
lean_dec(x_87);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_22);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_45);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_dec(x_2);
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
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_4, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
lean_dec(x_16);
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
lean_dec(x_15);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_19 = lean_st_mk_ref(x_1, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
x_32 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_2, x_3, x_4, x_5, x_20, x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_5);
x_34 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_6, x_3, x_4, x_5, x_20, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_5);
x_36 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_7, x_4, x_3, x_5, x_20, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_5);
x_38 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_8, x_4, x_3, x_5, x_20, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_5);
x_40 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_9, x_3, x_4, x_5, x_20, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
lean_inc(x_20);
x_43 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(x_5, x_42, x_10, x_42, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_22 = x_44;
goto block_31;
}
else
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_22 = x_45;
goto block_31;
}
else
{
uint8_t x_46; 
lean_dec(x_20);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
block_31:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_st_ref_get(x_20, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_20, x_25);
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__22;
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
x_2 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__22;
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
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__30;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__32;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__34;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__36;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__38;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__40;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
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
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__44;
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__43;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_93; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_93 = lean_ctor_get_uint8(x_11, sizeof(void*)*6 + 12);
lean_dec(x_11);
if (x_93 == 0)
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
goto block_92;
}
else
{
lean_object* x_94; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_94 = l_Lean_MVarId_exposeNames(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_15 = x_95;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_96;
goto block_92;
}
else
{
uint8_t x_97; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
block_92:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_17, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_17, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_getBoolTrueExpr___redArg(x_17, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Grind_getBoolFalseExpr___redArg(x_17, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_getNatZeroExpr___redArg(x_17, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_15);
x_39 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_15, x_2, x_19, x_20, x_21, x_22, x_38);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
x_43 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4;
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__7;
x_46 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__8;
x_47 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_box(0));
x_48 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__9;
x_49 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__10;
x_50 = lean_box(0);
x_51 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__11;
x_52 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__12;
x_53 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__14;
x_54 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_box(0));
x_55 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_44);
lean_ctor_set(x_56, 5, x_44);
lean_ctor_set(x_56, 6, x_54);
lean_ctor_set(x_56, 7, x_44);
lean_ctor_set(x_56, 8, x_55);
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__16;
x_59 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_box(0));
x_60 = lean_box(0);
x_61 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__18;
x_62 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__19;
x_63 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_13);
lean_ctor_set(x_63, 2, x_57);
lean_ctor_set(x_63, 3, x_58);
lean_ctor_set(x_63, 4, x_59);
lean_ctor_set(x_63, 5, x_60);
lean_ctor_set(x_63, 6, x_57);
lean_ctor_set(x_63, 7, x_61);
lean_ctor_set(x_63, 8, x_62);
x_64 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__20;
x_65 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__27;
x_66 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__28;
x_67 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__29;
x_68 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__31;
x_69 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__33;
x_70 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__35;
x_71 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__37;
x_72 = lean_box(0);
x_73 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__39;
x_74 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__41;
x_75 = lean_box(0);
x_76 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__42;
x_77 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_box(0));
x_78 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_78, 0, x_45);
lean_ctor_set(x_78, 1, x_64);
lean_ctor_set(x_78, 2, x_66);
lean_ctor_set(x_78, 3, x_67);
lean_ctor_set(x_78, 4, x_64);
lean_ctor_set(x_78, 5, x_68);
lean_ctor_set(x_78, 6, x_69);
lean_ctor_set(x_78, 7, x_69);
lean_ctor_set(x_78, 8, x_70);
lean_ctor_set(x_78, 9, x_71);
lean_ctor_set(x_78, 10, x_72);
lean_ctor_set(x_78, 11, x_73);
lean_ctor_set(x_78, 12, x_74);
lean_ctor_set(x_78, 13, x_44);
lean_ctor_set(x_78, 14, x_75);
lean_ctor_set(x_78, 15, x_76);
lean_ctor_set(x_78, 16, x_77);
x_79 = lean_unbox(x_50);
lean_ctor_set_uint8(x_78, sizeof(void*)*17, x_79);
x_80 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__45;
x_81 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__46;
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
lean_inc(x_15);
x_83 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_83, 0, x_15);
lean_ctor_set(x_83, 1, x_42);
lean_ctor_set(x_83, 2, x_43);
lean_ctor_set(x_83, 3, x_45);
lean_ctor_set(x_83, 4, x_46);
lean_ctor_set(x_83, 5, x_47);
lean_ctor_set(x_83, 6, x_48);
lean_ctor_set(x_83, 7, x_49);
lean_ctor_set(x_83, 8, x_44);
lean_ctor_set(x_83, 9, x_51);
lean_ctor_set(x_83, 10, x_45);
lean_ctor_set(x_83, 11, x_52);
lean_ctor_set(x_83, 12, x_56);
lean_ctor_set(x_83, 13, x_63);
lean_ctor_set(x_83, 14, x_82);
lean_ctor_set(x_83, 15, x_40);
x_84 = lean_unbox(x_50);
lean_ctor_set_uint8(x_83, sizeof(void*)*16, x_84);
x_85 = lean_box(1);
x_86 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed), 18, 10);
lean_closure_set(x_86, 0, x_83);
lean_closure_set(x_86, 1, x_28);
lean_closure_set(x_86, 2, x_85);
lean_closure_set(x_86, 3, x_50);
lean_closure_set(x_86, 4, x_44);
lean_closure_set(x_86, 5, x_25);
lean_closure_set(x_86, 6, x_31);
lean_closure_set(x_86, 7, x_34);
lean_closure_set(x_86, 8, x_37);
lean_closure_set(x_86, 9, x_14);
x_87 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(x_15, x_86, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_41);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_88 = !lean_is_exclusive(x_39);
if (x_88 == 0)
{
return x_39;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_39, 0);
x_90 = lean_ctor_get(x_39, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_39);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
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
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
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
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
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
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
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
lean_dec(x_17);
x_20 = lean_box(0);
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
lean_dec(x_5);
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
lean_dec(x_46);
x_49 = lean_box(0);
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
lean_dec(x_5);
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
lean_dec(x_6);
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
lean_object* x_9; lean_object* x_10; lean_object* x_40; lean_object* x_41; lean_object* x_44; uint8_t x_45; 
x_9 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_3);
x_45 = lean_nat_dec_eq(x_44, x_9);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_51; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_44, x_46);
lean_dec(x_44);
x_51 = lean_nat_dec_le(x_9, x_47);
if (x_51 == 0)
{
lean_inc(x_47);
x_48 = x_47;
goto block_50;
}
else
{
x_48 = x_9;
goto block_50;
}
block_50:
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_48, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_inc(x_48);
x_40 = x_48;
x_41 = x_48;
goto block_43;
}
else
{
x_40 = x_48;
x_41 = x_47;
goto block_43;
}
}
}
else
{
lean_dec(x_44);
x_10 = x_3;
goto block_39;
}
block_39:
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
lean_object* x_15; double x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_17 = lean_box(1);
x_18 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_16);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_20);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; double x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_27 = lean_box(1);
x_28 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_29 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_float(x_29, sizeof(void*)*2, x_26);
lean_ctor_set_float(x_29, sizeof(void*)*2 + 8, x_26);
x_30 = lean_unbox(x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 16, x_30);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_43:
{
lean_object* x_42; 
x_42 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_3, x_40, x_41);
lean_dec(x_41);
x_10 = x_42;
goto block_39;
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 4);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_array_uset(x_7, x_6, x_21);
x_30 = l_Lean_Meta_Grind_SplitSource_toMessageData(x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
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
lean_inc(x_2);
lean_inc(x_1);
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
lean_inc(x_40);
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
lean_inc(x_40);
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
lean_inc(x_40);
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
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_30, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
lean_dec(x_30);
x_23 = x_66;
x_24 = x_67;
goto block_29;
}
else
{
uint8_t x_68; 
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_1; lean_object* x_2; double x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_2 = lean_box(1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_6);
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
lean_dec(x_7);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData___closed__1;
x_17 = lean_array_size(x_1);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData_spec__0(x_13, x_14, x_15, x_16, x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_4);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_2);
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
lean_dec(x_11);
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
lean_dec(x_11);
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
lean_dec(x_11);
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
lean_object* x_1; lean_object* x_2; double x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
x_2 = lean_box(1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_6);
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
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
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
lean_dec(x_9);
x_14 = lean_array_mk(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_120 = lean_array_get_size(x_14);
x_121 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(x_14, x_15, x_120);
lean_dec(x_120);
lean_dec(x_14);
x_136 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__20___redArg(x_10);
lean_dec(x_10);
x_137 = lean_array_mk(x_136);
x_138 = lean_array_get_size(x_137);
x_139 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___closed__0;
x_140 = lean_nat_dec_lt(x_15, x_138);
if (x_140 == 0)
{
lean_dec(x_138);
lean_dec(x_137);
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
lean_dec(x_137);
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
lean_dec(x_137);
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
lean_dec(x_16);
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
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Lean_Meta_Simp_mkDiagMessages(x_33, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
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
lean_dec(x_27);
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
lean_dec(x_11);
x_57 = lean_array_mk(x_56);
x_58 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_54, x_55, x_57, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_2);
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
lean_dec(x_11);
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
lean_dec(x_77);
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
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
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
lean_dec(x_67);
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
lean_inc(x_90);
x_95 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_splitDiagInfoToMessageData(x_93, x_86, x_87, x_90, x_89, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_array_push(x_91, x_96);
x_67 = x_88;
x_68 = x_98;
x_69 = x_86;
x_70 = x_87;
x_71 = x_90;
x_72 = x_89;
x_73 = x_97;
goto block_85;
}
else
{
uint8_t x_99; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
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
lean_dec(x_93);
x_67 = x_88;
x_68 = x_91;
x_69 = x_86;
x_70 = x_87;
x_71 = x_90;
x_72 = x_89;
x_73 = x_92;
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
lean_dec(x_111);
x_86 = x_106;
x_87 = x_107;
x_88 = x_104;
x_89 = x_109;
x_90 = x_108;
x_91 = x_105;
x_92 = x_110;
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
lean_dec(x_111);
x_86 = x_106;
x_87 = x_107;
x_88 = x_104;
x_89 = x_109;
x_90 = x_108;
x_91 = x_105;
x_92 = x_110;
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
lean_dec(x_111);
x_86 = x_106;
x_87 = x_107;
x_88 = x_104;
x_89 = x_109;
x_90 = x_108;
x_91 = x_105;
x_92 = x_110;
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
lean_dec(x_127);
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
lean_dec(x_122);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_121);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(x_1, x_2);
lean_dec(x_2);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
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
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailed___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Result_hasFailed(x_1);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_inc(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_Grind_goalToMessageData(x_12, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_inc(x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Meta_Grind_goalToMessageData(x_23, x_25, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 6);
lean_inc(x_12);
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
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_19 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_10, x_11, x_12, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_12);
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
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_13, x_22, x_14, x_15, x_16, x_17, x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_9, sizeof(void*)*6 + 11);
lean_dec(x_9);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_40, x_42, x_2, x_3, x_4, x_5, x_41);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_MVarId_abstractMVars(x_1, x_6, x_7, x_8, x_9, x_10);
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
x_14 = l_Lean_MVarId_clearAuxDecls(x_12, x_6, x_7, x_8, x_9, x_13);
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
x_17 = l_Lean_MVarId_revertAll(x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_MVarId_unfoldReducible(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_MVarId_betaReduce(x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___closed__1;
lean_inc(x_24);
x_27 = l_Lean_Meta_appendTagSuffix(x_24, x_26, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_120; uint8_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_142; uint8_t x_159; uint8_t x_160; 
x_132 = lean_box(2);
x_159 = lean_unbox(x_132);
x_160 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_159);
if (x_160 == 0)
{
x_142 = x_160;
goto block_158;
}
else
{
uint8_t x_161; 
lean_inc(x_2);
x_161 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_142 = x_161;
goto block_158;
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
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_22, 6);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_13);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_10);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_16);
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
lean_ctor_set(x_47, 1, x_13);
x_48 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_14);
lean_ctor_set(x_48, 2, x_12);
lean_ctor_set(x_48, 3, x_10);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 1, x_16);
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
lean_dec(x_17);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_56, 7);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 8);
lean_inc(x_68);
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
lean_ctor_set(x_71, 1, x_13);
x_72 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_72, 0, x_15);
lean_ctor_set(x_72, 1, x_14);
lean_ctor_set(x_72, 2, x_12);
lean_ctor_set(x_72, 3, x_10);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 1, x_16);
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
block_108:
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_5, x_6, x_7, x_8, x_9);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_86);
x_93 = l_Lean_FileMap_toPosition(x_86, x_82);
lean_dec(x_82);
x_94 = l_Lean_FileMap_toPosition(x_86, x_88);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
if (x_84 == 0)
{
lean_free_object(x_89);
lean_dec(x_81);
x_10 = x_96;
x_11 = x_83;
x_12 = x_95;
x_13 = x_91;
x_14 = x_93;
x_15 = x_85;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_92;
goto block_80;
}
else
{
uint8_t x_97; 
lean_inc(x_91);
x_97 = l_Lean_MessageData_hasTag(x_81, x_91);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_85);
lean_dec(x_7);
x_98 = lean_box(0);
lean_ctor_set(x_89, 0, x_98);
return x_89;
}
else
{
lean_free_object(x_89);
x_10 = x_96;
x_11 = x_83;
x_12 = x_95;
x_13 = x_91;
x_14 = x_93;
x_15 = x_85;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_92;
goto block_80;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_89, 0);
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_89);
lean_inc(x_86);
x_101 = l_Lean_FileMap_toPosition(x_86, x_82);
lean_dec(x_82);
x_102 = l_Lean_FileMap_toPosition(x_86, x_88);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___closed__0;
if (x_84 == 0)
{
lean_dec(x_81);
x_10 = x_104;
x_11 = x_83;
x_12 = x_103;
x_13 = x_99;
x_14 = x_101;
x_15 = x_85;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_100;
goto block_80;
}
else
{
uint8_t x_105; 
lean_inc(x_99);
x_105 = l_Lean_MessageData_hasTag(x_81, x_99);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_7);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_100);
return x_107;
}
else
{
x_10 = x_104;
x_11 = x_83;
x_12 = x_103;
x_13 = x_99;
x_14 = x_101;
x_15 = x_85;
x_16 = x_87;
x_17 = x_7;
x_18 = x_8;
x_19 = x_100;
goto block_80;
}
}
}
}
block_119:
{
lean_object* x_117; 
x_117 = l_Lean_Syntax_getTailPos_x3f(x_112, x_110);
lean_dec(x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_inc(x_116);
x_81 = x_109;
x_82 = x_116;
x_83 = x_110;
x_84 = x_111;
x_85 = x_113;
x_86 = x_114;
x_87 = x_115;
x_88 = x_116;
goto block_108;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec(x_117);
x_81 = x_109;
x_82 = x_116;
x_83 = x_110;
x_84 = x_111;
x_85 = x_113;
x_86 = x_114;
x_87 = x_115;
x_88 = x_118;
goto block_108;
}
}
block_131:
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_replaceRef(x_1, x_123);
lean_dec(x_123);
x_128 = l_Lean_Syntax_getPos_x3f(x_127, x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_unsigned_to_nat(0u);
x_109 = x_120;
x_110 = x_121;
x_111 = x_122;
x_112 = x_127;
x_113 = x_124;
x_114 = x_125;
x_115 = x_126;
x_116 = x_129;
goto block_119;
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_109 = x_120;
x_110 = x_121;
x_111 = x_122;
x_112 = x_127;
x_113 = x_124;
x_114 = x_125;
x_115 = x_126;
x_116 = x_130;
goto block_119;
}
}
block_141:
{
if (x_139 == 0)
{
x_120 = x_135;
x_121 = x_138;
x_122 = x_133;
x_123 = x_134;
x_124 = x_136;
x_125 = x_137;
x_126 = x_3;
goto block_131;
}
else
{
uint8_t x_140; 
x_140 = lean_unbox(x_132);
x_120 = x_135;
x_121 = x_138;
x_122 = x_133;
x_123 = x_134;
x_124 = x_136;
x_125 = x_137;
x_126 = x_140;
goto block_131;
}
}
block_158:
{
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
x_143 = lean_ctor_get(x_7, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_7, 1);
lean_inc(x_144);
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
x_151 = lean_box(1);
x_152 = lean_unbox(x_151);
x_153 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_152);
if (x_153 == 0)
{
lean_dec(x_145);
x_133 = x_147;
x_134 = x_146;
x_135 = x_150;
x_136 = x_143;
x_137 = x_144;
x_138 = x_142;
x_139 = x_153;
goto block_141;
}
else
{
lean_object* x_154; uint8_t x_155; 
x_154 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___closed__0;
x_155 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_145, x_154);
lean_dec(x_145);
x_133 = x_147;
x_134 = x_146;
x_135 = x_150;
x_136 = x_143;
x_137 = x_144;
x_138 = x_142;
x_139 = x_155;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_7);
lean_dec(x_2);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_9);
return x_157;
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_11);
x_14 = l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(x_1, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_22 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_Grind_solve(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_7, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
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
lean_inc(x_43);
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
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_35, 6);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_ctor_get(x_39, 7);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_43, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 5);
lean_inc(x_51);
lean_dec(x_43);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_50);
if (lean_obj_tag(x_26) == 0)
{
goto block_73;
}
else
{
if (x_4 == 0)
{
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = x_44;
goto block_56;
}
else
{
goto block_73;
}
}
block_56:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_47);
lean_ctor_set(x_54, 4, x_48);
lean_ctor_set(x_54, 5, x_37);
lean_ctor_set(x_54, 6, x_49);
if (lean_is_scalar(x_45)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_45;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
block_73:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_44);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_52 = x_60;
goto block_56;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_37);
lean_inc(x_48);
x_62 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_48, x_37, x_49, x_8, x_9, x_10, x_11, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_52 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_66, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_65);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_52 = x_68;
goto block_56;
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
return x_62;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_62);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_74 = lean_ctor_get(x_37, 0);
x_75 = lean_ctor_get(x_37, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_37);
x_76 = lean_st_ref_get(x_7, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 2);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_29, 4);
lean_inc(x_81);
lean_dec(x_29);
x_82 = lean_ctor_get(x_32, 5);
lean_inc(x_82);
lean_dec(x_32);
x_83 = lean_ctor_get(x_35, 6);
lean_inc(x_83);
lean_dec(x_35);
x_84 = lean_ctor_get(x_74, 7);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_ctor_get(x_78, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 5);
lean_inc(x_86);
lean_dec(x_78);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
if (lean_obj_tag(x_26) == 0)
{
goto block_109;
}
else
{
if (x_4 == 0)
{
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_88 = x_79;
goto block_92;
}
else
{
goto block_109;
}
}
block_92:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_3, 0);
lean_inc(x_89);
lean_dec(x_3);
x_90 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_90, 0, x_26);
lean_ctor_set(x_90, 1, x_81);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_82);
lean_ctor_set(x_90, 4, x_83);
lean_ctor_set(x_90, 5, x_87);
lean_ctor_set(x_90, 6, x_84);
if (lean_is_scalar(x_80)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_80;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
block_109:
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_79);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_88 = x_96;
goto block_92;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_87);
lean_inc(x_83);
x_98 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_83, x_87, x_84, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_88 = x_100;
goto block_92;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_102, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_101);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_88 = x_104;
goto block_92;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_105 = lean_ctor_get(x_98, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_107 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_25);
if (x_110 == 0)
{
return x_25;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_25, 0);
x_112 = lean_ctor_get(x_25, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_25);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_22);
if (x_114 == 0)
{
return x_22;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_22, 0);
x_116 = lean_ctor_get(x_22, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_22);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint64_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; lean_object* x_142; 
x_118 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_119 = lean_ctor_get_uint8(x_14, 0);
x_120 = lean_ctor_get_uint8(x_14, 1);
x_121 = lean_ctor_get_uint8(x_14, 2);
x_122 = lean_ctor_get_uint8(x_14, 3);
x_123 = lean_ctor_get_uint8(x_14, 4);
x_124 = lean_ctor_get_uint8(x_14, 5);
x_125 = lean_ctor_get_uint8(x_14, 6);
x_126 = lean_ctor_get_uint8(x_14, 7);
x_127 = lean_ctor_get_uint8(x_14, 8);
x_128 = lean_ctor_get_uint8(x_14, 10);
x_129 = lean_ctor_get_uint8(x_14, 11);
x_130 = lean_ctor_get_uint8(x_14, 12);
x_131 = lean_ctor_get_uint8(x_14, 13);
x_132 = lean_ctor_get_uint8(x_14, 14);
x_133 = lean_ctor_get_uint8(x_14, 15);
x_134 = lean_ctor_get_uint8(x_14, 16);
x_135 = lean_ctor_get_uint8(x_14, 17);
lean_dec(x_14);
x_136 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_136, 0, x_119);
lean_ctor_set_uint8(x_136, 1, x_120);
lean_ctor_set_uint8(x_136, 2, x_121);
lean_ctor_set_uint8(x_136, 3, x_122);
lean_ctor_set_uint8(x_136, 4, x_123);
lean_ctor_set_uint8(x_136, 5, x_124);
lean_ctor_set_uint8(x_136, 6, x_125);
lean_ctor_set_uint8(x_136, 7, x_126);
lean_ctor_set_uint8(x_136, 8, x_127);
lean_ctor_set_uint8(x_136, 9, x_1);
lean_ctor_set_uint8(x_136, 10, x_128);
lean_ctor_set_uint8(x_136, 11, x_129);
lean_ctor_set_uint8(x_136, 12, x_130);
lean_ctor_set_uint8(x_136, 13, x_131);
lean_ctor_set_uint8(x_136, 14, x_132);
lean_ctor_set_uint8(x_136, 15, x_133);
lean_ctor_set_uint8(x_136, 16, x_134);
lean_ctor_set_uint8(x_136, 17, x_135);
x_137 = 2;
x_138 = lean_uint64_shift_right(x_118, x_137);
x_139 = lean_uint64_shift_left(x_138, x_137);
x_140 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_141 = lean_uint64_lor(x_139, x_140);
lean_ctor_set(x_8, 0, x_136);
lean_ctor_set_uint64(x_8, sizeof(void*)*7, x_141);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_142 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_145 = l_Lean_Meta_Grind_solve(x_143, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_st_ref_get(x_7, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_st_ref_get(x_7, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_get(x_7, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_st_ref_get(x_7, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_st_ref_get(x_7, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 2);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_165 = x_161;
} else {
 lean_dec_ref(x_161);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_149, 4);
lean_inc(x_166);
lean_dec(x_149);
x_167 = lean_ctor_get(x_152, 5);
lean_inc(x_167);
lean_dec(x_152);
x_168 = lean_ctor_get(x_155, 6);
lean_inc(x_168);
lean_dec(x_155);
x_169 = lean_ctor_get(x_158, 7);
lean_inc(x_169);
lean_dec(x_158);
x_170 = lean_ctor_get(x_163, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_163, 5);
lean_inc(x_171);
lean_dec(x_163);
if (lean_is_scalar(x_160)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_160;
}
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
if (lean_obj_tag(x_146) == 0)
{
goto block_194;
}
else
{
if (x_4 == 0)
{
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_173 = x_164;
goto block_177;
}
else
{
goto block_194;
}
}
block_177:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_3, 0);
lean_inc(x_174);
lean_dec(x_3);
x_175 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_175, 0, x_146);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_167);
lean_ctor_set(x_175, 4, x_168);
lean_ctor_set(x_175, 5, x_172);
lean_ctor_set(x_175, 6, x_169);
if (lean_is_scalar(x_165)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_165;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
block_194:
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_164);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_173 = x_181;
goto block_177;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_172);
lean_inc(x_168);
x_183 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_168, x_172, x_169, x_8, x_9, x_10, x_11, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_173 = x_185;
goto block_177;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
lean_dec(x_184);
x_188 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_187, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_186);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_173 = x_189;
goto block_177;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_146);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_190 = lean_ctor_get(x_183, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_183, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_192 = x_183;
} else {
 lean_dec_ref(x_183);
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
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_195 = lean_ctor_get(x_145, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_145, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_197 = x_145;
} else {
 lean_dec_ref(x_145);
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
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_199 = lean_ctor_get(x_142, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_142, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_201 = x_142;
} else {
 lean_dec_ref(x_142);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; uint64_t x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; lean_object* x_238; lean_object* x_239; 
x_203 = lean_ctor_get(x_8, 0);
x_204 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_205 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_206 = lean_ctor_get(x_8, 1);
x_207 = lean_ctor_get(x_8, 2);
x_208 = lean_ctor_get(x_8, 3);
x_209 = lean_ctor_get(x_8, 4);
x_210 = lean_ctor_get(x_8, 5);
x_211 = lean_ctor_get(x_8, 6);
x_212 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_213 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_203);
lean_dec(x_8);
x_214 = lean_ctor_get_uint8(x_203, 0);
x_215 = lean_ctor_get_uint8(x_203, 1);
x_216 = lean_ctor_get_uint8(x_203, 2);
x_217 = lean_ctor_get_uint8(x_203, 3);
x_218 = lean_ctor_get_uint8(x_203, 4);
x_219 = lean_ctor_get_uint8(x_203, 5);
x_220 = lean_ctor_get_uint8(x_203, 6);
x_221 = lean_ctor_get_uint8(x_203, 7);
x_222 = lean_ctor_get_uint8(x_203, 8);
x_223 = lean_ctor_get_uint8(x_203, 10);
x_224 = lean_ctor_get_uint8(x_203, 11);
x_225 = lean_ctor_get_uint8(x_203, 12);
x_226 = lean_ctor_get_uint8(x_203, 13);
x_227 = lean_ctor_get_uint8(x_203, 14);
x_228 = lean_ctor_get_uint8(x_203, 15);
x_229 = lean_ctor_get_uint8(x_203, 16);
x_230 = lean_ctor_get_uint8(x_203, 17);
if (lean_is_exclusive(x_203)) {
 x_231 = x_203;
} else {
 lean_dec_ref(x_203);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 0, 18);
} else {
 x_232 = x_231;
}
lean_ctor_set_uint8(x_232, 0, x_214);
lean_ctor_set_uint8(x_232, 1, x_215);
lean_ctor_set_uint8(x_232, 2, x_216);
lean_ctor_set_uint8(x_232, 3, x_217);
lean_ctor_set_uint8(x_232, 4, x_218);
lean_ctor_set_uint8(x_232, 5, x_219);
lean_ctor_set_uint8(x_232, 6, x_220);
lean_ctor_set_uint8(x_232, 7, x_221);
lean_ctor_set_uint8(x_232, 8, x_222);
lean_ctor_set_uint8(x_232, 9, x_1);
lean_ctor_set_uint8(x_232, 10, x_223);
lean_ctor_set_uint8(x_232, 11, x_224);
lean_ctor_set_uint8(x_232, 12, x_225);
lean_ctor_set_uint8(x_232, 13, x_226);
lean_ctor_set_uint8(x_232, 14, x_227);
lean_ctor_set_uint8(x_232, 15, x_228);
lean_ctor_set_uint8(x_232, 16, x_229);
lean_ctor_set_uint8(x_232, 17, x_230);
x_233 = 2;
x_234 = lean_uint64_shift_right(x_204, x_233);
x_235 = lean_uint64_shift_left(x_234, x_233);
x_236 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_237 = lean_uint64_lor(x_235, x_236);
x_238 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_238, 0, x_232);
lean_ctor_set(x_238, 1, x_206);
lean_ctor_set(x_238, 2, x_207);
lean_ctor_set(x_238, 3, x_208);
lean_ctor_set(x_238, 4, x_209);
lean_ctor_set(x_238, 5, x_210);
lean_ctor_set(x_238, 6, x_211);
lean_ctor_set_uint64(x_238, sizeof(void*)*7, x_237);
lean_ctor_set_uint8(x_238, sizeof(void*)*7 + 8, x_205);
lean_ctor_set_uint8(x_238, sizeof(void*)*7 + 9, x_212);
lean_ctor_set_uint8(x_238, sizeof(void*)*7 + 10, x_213);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_238);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_239 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_5, x_6, x_7, x_238, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_238);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_242 = l_Lean_Meta_Grind_solve(x_240, x_5, x_6, x_7, x_238, x_9, x_10, x_11, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_st_ref_get(x_7, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_st_ref_get(x_7, x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_st_ref_get(x_7, x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_st_ref_get(x_7, x_253);
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
x_258 = lean_st_ref_get(x_7, x_256);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 2);
lean_inc(x_260);
lean_dec(x_259);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_262 = x_258;
} else {
 lean_dec_ref(x_258);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_246, 4);
lean_inc(x_263);
lean_dec(x_246);
x_264 = lean_ctor_get(x_249, 5);
lean_inc(x_264);
lean_dec(x_249);
x_265 = lean_ctor_get(x_252, 6);
lean_inc(x_265);
lean_dec(x_252);
x_266 = lean_ctor_get(x_255, 7);
lean_inc(x_266);
lean_dec(x_255);
x_267 = lean_ctor_get(x_260, 3);
lean_inc(x_267);
x_268 = lean_ctor_get(x_260, 5);
lean_inc(x_268);
lean_dec(x_260);
if (lean_is_scalar(x_257)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_257;
}
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
if (lean_obj_tag(x_243) == 0)
{
goto block_291;
}
else
{
if (x_4 == 0)
{
lean_dec(x_238);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_270 = x_261;
goto block_274;
}
else
{
goto block_291;
}
}
block_274:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_3, 0);
lean_inc(x_271);
lean_dec(x_3);
x_272 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_272, 0, x_243);
lean_ctor_set(x_272, 1, x_263);
lean_ctor_set(x_272, 2, x_271);
lean_ctor_set(x_272, 3, x_264);
lean_ctor_set(x_272, 4, x_265);
lean_ctor_set(x_272, 5, x_269);
lean_ctor_set(x_272, 6, x_266);
if (lean_is_scalar(x_262)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_262;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
block_291:
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_275 = l_Lean_isDiagnosticsEnabled___redArg(x_10, x_261);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_unbox(x_276);
lean_dec(x_276);
if (x_277 == 0)
{
lean_object* x_278; 
lean_dec(x_238);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_dec(x_275);
x_270 = x_278;
goto block_274;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_275, 1);
lean_inc(x_279);
lean_dec(x_275);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_238);
lean_inc(x_269);
lean_inc(x_265);
x_280 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_265, x_269, x_266, x_238, x_9, x_10, x_11, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
lean_dec(x_238);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_270 = x_282;
goto block_274;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
lean_dec(x_281);
x_285 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_284, x_5, x_6, x_7, x_238, x_9, x_10, x_11, x_283);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_238);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_270 = x_286;
goto block_274;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_243);
lean_dec(x_238);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_287 = lean_ctor_get(x_280, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_289 = x_280;
} else {
 lean_dec_ref(x_280);
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
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_238);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_292 = lean_ctor_get(x_242, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_242, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_294 = x_242;
} else {
 lean_dec_ref(x_242);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_238);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_296 = lean_ctor_get(x_239, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_239, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_298 = x_239;
} else {
 lean_dec_ref(x_239);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
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
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__35;
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
x_1 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__32;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(2);
x_13 = lean_box(x_11);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lam__0___boxed), 12, 4);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lean_Meta_Grind_GrindM_run___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_MVarId_admit(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_main___lam__1___closed__2;
x_23 = l_Lean_Meta_Grind_main___lam__1___closed__6;
x_24 = l_Lean_Meta_Grind_main___lam__1___closed__10;
x_25 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_26, 6, x_25);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Grind_main___lam__1___closed__2;
x_32 = l_Lean_Meta_Grind_main___lam__1___closed__6;
x_33 = l_Lean_Meta_Grind_main___lam__1___closed__10;
x_34 = l_Lean_Meta_Grind_GrindM_run___redArg___closed__39;
x_35 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
lean_ctor_set(x_35, 6, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
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
x_13 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__1___redArg(x_11, x_9, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
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
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
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
l_Lean_Meta_Grind_mkParams___redArg___closed__0 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__0);
l_Lean_Meta_Grind_mkParams___redArg___closed__1 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__1);
l_Lean_Meta_Grind_mkParams___redArg___closed__2 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__2);
l_Lean_Meta_Grind_mkParams___redArg___closed__3 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__3);
l_Lean_Meta_Grind_mkParams___redArg___closed__4 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__4);
l_Lean_Meta_Grind_mkParams___redArg___closed__5 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__5);
l_Lean_Meta_Grind_mkParams___redArg___closed__6 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__6);
l_Lean_Meta_Grind_mkParams___redArg___closed__7 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__7);
l_Lean_Meta_Grind_mkParams___redArg___closed__8 = _init_l_Lean_Meta_Grind_mkParams___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_mkParams___redArg___closed__8);
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
