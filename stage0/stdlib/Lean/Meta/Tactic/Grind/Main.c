// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Main
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Util Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Proj Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.Solve Lean.Meta.Tactic.Grind.SimpUtil Lean.Meta.Tactic.Grind.Cases
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedTrace___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__14;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___closed__1;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__2___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__5(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
static lean_object* l_Lean_Meta_Grind_main___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__11;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3;
lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__8;
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__3;
lean_object* l_Lean_Meta_Grind_getSimprocs___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__5;
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__9;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1;
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__4;
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__4;
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__3;
lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__1;
lean_object* l_Std_Queue_empty(lean_object*);
static double l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___boxed(lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Grind_Result_toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1;
lean_object* l_Lean_Meta_Grind_getFalseExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkParams___closed__5;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Grind_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__10;
lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getTrueExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__2;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkMethods___closed__1;
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__4;
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_reportIssue___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_builtinPropagatorsRef;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5;
lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_reportIssue___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__3;
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__2;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lambda__3___closed__2;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getNatZeroExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__3;
static lean_object* l_Lean_Meta_Grind_main___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailures___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__1;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__1;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Grind_main___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_transformTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_0__Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkENodeCore(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__5___boxed(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
static lean_object* l_Lean_Meta_Grind_mkParams___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__2;
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__9;
lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__6;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4;
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__5;
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__2;
static lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__4;
lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__4;
lean_object* l_Lean_Meta_Grind_ppGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Result_toMessageData___closed__7;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkParams___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_mkParams___closed__5;
x_3 = l_Lean_Meta_Grind_mkParams___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_Grind_getSimpContext(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Grind_getSimprocs___rarg(x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Meta_Grind_mkParams___closed__3;
x_14 = l_Lean_Meta_Grind_mkParams___closed__2;
x_15 = l_Lean_Meta_Grind_mkParams___closed__6;
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_8);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Lean_Meta_Grind_mkParams___closed__3;
x_20 = l_Lean_Meta_Grind_mkParams___closed__2;
x_21 = l_Lean_Meta_Grind_mkParams___closed__6;
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_8);
lean_ctor_set(x_22, 5, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_38 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_17, x_37);
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
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_17, x_58);
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
uint8_t x_64; 
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
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
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
x_68 = lean_box(0);
lean_ctor_set(x_12, 0, x_68);
return x_12;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_12, 1);
lean_inc(x_69);
lean_dec(x_12);
x_70 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_70) == 4)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_72 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_array_get_size(x_76);
x_78 = l_Lean_Name_hash___override(x_71);
x_79 = 32;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = 16;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_87 = 1;
x_88 = lean_usize_sub(x_86, x_87);
x_89 = lean_usize_land(x_85, x_88);
x_90 = lean_array_uget(x_76, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_71, x_90);
lean_dec(x_90);
lean_dec(x_71);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
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
if (lean_is_scalar(x_75)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_75;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_74);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_apply_10(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_72, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_72, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_98 = x_72;
} else {
 lean_dec_ref(x_72);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_69);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_34 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_18, x_33);
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
x_58 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_42, x_57);
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
uint8_t x_65; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_12);
if (x_65 == 0)
{
return x_12;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_12, 0);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_12);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkMethods___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_builtinPropagatorsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Meta_Grind_mkMethods___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___lambda__1___boxed), 11, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___lambda__2___boxed), 11, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___lambda__1___boxed), 11, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___lambda__2___boxed), 11, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkMethods___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkMethods___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ShareCommon_objectFactory;
x_2 = l_ShareCommon_mkStateImpl(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_ShareCommon_objectFactory;
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__1;
x_3 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__4;
x_4 = lean_state_sharecommon(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__2;
x_2 = l_Lean_Meta_Grind_mkParams___closed__6;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__10;
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedTrace___spec__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__5;
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_Lean_ShareCommon_objectFactory;
x_15 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__8;
x_16 = lean_state_sharecommon(x_14, x_13, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__9;
x_20 = lean_state_sharecommon(x_14, x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_3, 5);
x_24 = lean_ctor_get(x_3, 4);
x_25 = lean_ctor_get(x_3, 0);
x_26 = l_Lean_Meta_Grind_mkMethods(x_4, x_7, x_8, x_9);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_24);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_2);
lean_ctor_set(x_29, 3, x_25);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Meta_Grind_mkParams___closed__2;
x_32 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__12;
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_35 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__14;
x_36 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_17);
lean_ctor_set(x_36, 5, x_12);
lean_ctor_set(x_36, 6, x_21);
lean_ctor_set(x_36, 7, x_33);
lean_ctor_set(x_36, 8, x_10);
lean_ctor_set(x_36, 9, x_34);
lean_ctor_set(x_36, 10, x_35);
x_37 = lean_st_mk_ref(x_36, x_28);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_38);
x_40 = lean_apply_8(x_1, x_27, x_29, x_38, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_38, x_42);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_38);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GrindM_run___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_GrindM_run___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_5, x_7);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_24 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3(x_1, x_20, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
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
lean_dec(x_22);
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
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
x_42 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3(x_1, x_20, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_7, x_52);
x_7 = x_53;
x_8 = x_51;
x_17 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_Grind_activateTheorem(x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
lean_inc(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_24;
x_16 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_array_size(x_13);
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__4(x_1, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_array_size(x_36);
x_41 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__5(x_36, x_37, x_38, x_36, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1(x_46, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_Grind_activateTheorem(x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
lean_inc(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_24;
x_16 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3(x_2, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_23);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__6(x_23, x_24, x_25, x_23, x_27, x_28, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
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
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = 1;
x_15 = 0;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Meta_Grind_mkENodeCore(x_2, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_Grind_mkENodeCore(x_3, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_box(0);
lean_inc(x_5);
x_25 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2(x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_5, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_st_ref_get(x_5, x_29);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_27, 1, x_32);
lean_ctor_set(x_30, 0, x_27);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_27, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_st_ref_get(x_5, x_37);
lean_dec(x_5);
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
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_39);
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
else
{
uint8_t x_44; 
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkParams___closed__2;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_mkParams___closed__6;
x_3 = l_Lean_Meta_Grind_mkParams___closed__2;
x_4 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_11 = l_Lean_Meta_Grind_getTrueExpr___rarg(x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_getFalseExpr___rarg(x_5, x_6, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_getNatZeroExpr___rarg(x_5, x_6, x_7, x_8, x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
x_24 = l_Lean_Meta_Grind_mkParams___closed__2;
x_25 = l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1;
x_26 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_27 = 0;
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
x_30 = l_Lean_Meta_Grind_mkParams___closed__6;
x_31 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__2;
x_32 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__4;
x_33 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
x_34 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__3;
lean_inc(x_1);
x_35 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
lean_ctor_set(x_35, 5, x_24);
lean_ctor_set(x_35, 6, x_26);
lean_ctor_set(x_35, 7, x_28);
lean_ctor_set(x_35, 8, x_28);
lean_ctor_set(x_35, 9, x_29);
lean_ctor_set(x_35, 10, x_21);
lean_ctor_set(x_35, 11, x_30);
lean_ctor_set(x_35, 12, x_30);
lean_ctor_set(x_35, 13, x_20);
lean_ctor_set(x_35, 14, x_28);
lean_ctor_set(x_35, 15, x_28);
lean_ctor_set(x_35, 16, x_31);
lean_ctor_set(x_35, 17, x_32);
lean_ctor_set(x_35, 18, x_33);
lean_ctor_set(x_35, 19, x_22);
lean_ctor_set(x_35, 20, x_28);
lean_ctor_set(x_35, 21, x_34);
lean_ctor_set(x_35, 22, x_28);
lean_ctor_set(x_35, 23, x_30);
lean_ctor_set(x_35, 24, x_24);
lean_ctor_set_uint8(x_35, sizeof(void*)*25, x_27);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed), 9, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2___boxed), 13, 4);
lean_closure_set(x_37, 0, x_15);
lean_closure_set(x_37, 1, x_12);
lean_closure_set(x_37, 2, x_18);
lean_closure_set(x_37, 3, x_2);
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__5;
x_40 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
x_41 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__4___boxed(lean_object** _args) {
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
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__4(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__5(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__6(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Meta_Grind_Goal_checkInvariants(x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_13;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*25);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_1 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_betaReduce___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
lean_inc(x_1);
x_11 = l_Lean_MVarId_ensureProp(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_MVarId_ensureNoMVar(x_1, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_MVarId_clearAuxDecls(x_1, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_MVarId_revertAll(x_16, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_MVarId_transformTarget(x_19, x_21, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Lean_MVarId_transformTarget(x_23, x_25, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4;
lean_inc(x_27);
x_30 = l_Lean_Meta_appendTagSuffix(x_27, x_29, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Meta_Grind_intros(x_35, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = l_List_forM___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__1(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
x_43 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(x_37, x_42);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(x_37, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_37);
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
uint8_t x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_32);
if (x_56 == 0)
{
return x_32;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_32, 0);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_32);
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
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
return x_26;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_26);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_22);
if (x_68 == 0)
{
return x_22;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_22, 0);
x_70 = lean_ctor_get(x_22, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_22);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_18);
if (x_72 == 0)
{
return x_18;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_18, 0);
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_15);
if (x_76 == 0)
{
return x_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_15, 0);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_13);
if (x_80 == 0)
{
return x_13;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_13, 0);
x_82 = lean_ctor_get(x_13, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_13);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_11);
if (x_84 == 0)
{
return x_11;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_11, 0);
x_86 = lean_ctor_get(x_11, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_11);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
static double _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ↦ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; double x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
x_22 = 1;
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
lean_inc(x_1);
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_22);
x_25 = l_Lean_MessageData_ofConst(x_19);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_26);
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_38 = lean_array_uset(x_14, x_3, x_35);
x_3 = x_37;
x_4 = x_38;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_40; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
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
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(x_44, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; double x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
x_50 = 1;
x_51 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
lean_inc(x_1);
x_52 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_float(x_52, sizeof(void*)*2, x_49);
lean_ctor_set_float(x_52, sizeof(void*)*2 + 8, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*2 + 16, x_50);
x_53 = l_Lean_MessageData_ofConst(x_47);
x_54 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_MessageData_ofFormat(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
x_63 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_64 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
x_65 = 1;
x_66 = lean_usize_add(x_3, x_65);
x_67 = lean_array_uset(x_14, x_3, x_64);
x_3 = x_66;
x_4 = x_67;
x_9 = x_48;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_1);
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_71 = x_46;
} else {
 lean_dec_ref(x_46);
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
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___closed__1;
lean_inc(x_3);
x_9 = l___private_Init_Data_Array_QSort_0__Array_qpartition___rarg(x_1, x_2, x_8, x_3, x_4, lean_box(0), lean_box(0));
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_le(x_4, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2(x_1, x_11, x_3, x_10, lean_box(0), lean_box(0));
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_10, x_14);
lean_dec(x_10);
x_2 = x_13;
x_3 = x_15;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_9, x_12);
x_14 = 0;
if (x_13 == 0)
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_12, x_11);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_11);
x_43 = l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2(x_9, x_3, x_11, x_11, lean_box(0), lean_box(0));
lean_dec(x_11);
lean_dec(x_9);
x_15 = x_43;
goto block_41;
}
else
{
lean_object* x_44; 
x_44 = l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2(x_9, x_3, x_12, x_11, lean_box(0), lean_box(0));
lean_dec(x_11);
lean_dec(x_9);
x_15 = x_44;
goto block_41;
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
x_15 = x_3;
goto block_41;
}
block_41:
{
size_t x_16; lean_object* x_17; 
x_16 = lean_array_size(x_15);
lean_inc(x_2);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1(x_2, x_16, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; double x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
x_21 = 1;
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_21);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
x_30 = 1;
x_31 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_12);
x_13 = lean_array_push(x_4, x_6);
x_2 = x_8;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_push(x_4, x_17);
x_2 = x_8;
x_4 = x_18;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__4(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
x_11 = l_Lean_NameSet_contains(x_10, x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_4, x_6);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; double x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
x_3 = 1;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Counters", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1;
x_10 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__4;
x_11 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cases instances", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__1;
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__4;
x_12 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__3;
x_13 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_11, x_12, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_2, x_14);
x_17 = lean_box(0);
x_18 = lean_apply_7(x_9, x_16, x_17, x_4, x_5, x_6, x_7, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_7(x_9, x_2, x_23, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("thm", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("E-Matching instances", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1(x_7);
x_9 = lean_array_mk(x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_filterMapM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__3(x_9, x_11, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__5(x_13);
x_15 = lean_array_mk(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_lt(x_11, x_16);
x_18 = l_Array_isEmpty___rarg(x_12);
if (x_17 == 0)
{
lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_15);
x_37 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_19 = x_37;
goto block_36;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_16, x_16);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_16);
lean_dec(x_15);
x_39 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_19 = x_39;
goto block_36;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_42 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__7(x_15, x_40, x_41, x_42);
lean_dec(x_15);
x_19 = x_43;
goto block_36;
}
}
block_36:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__3;
x_21 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__2;
x_22 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_20, x_21, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2(x_19, x_26, x_27, x_2, x_3, x_4, x_5, x_24);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
x_33 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2(x_19, x_33, x_34, x_2, x_3, x_4, x_5, x_6);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Counters_toMessageData_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Counters_toMessageData_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailures___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Result_hasFailures(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Grind_Result_toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = l_List_reverse___rarg(x_3);
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
x_14 = lean_ctor_get(x_1, 3);
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
x_25 = lean_ctor_get(x_1, 3);
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
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__2;
x_9 = l_Lean_MessageData_joinSep(x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Result_toMessageData___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_Grind_Counters_toMessageData_x3f(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_Result_toMessageData___lambda__2___closed__1;
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_7(x_14, x_3, x_15, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_19 = l_List_appendTR___rarg(x_3, x_18);
x_20 = lean_box(0);
x_21 = lean_apply_7(x_14, x_19, x_20, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_List_isEmpty___rarg(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_List_reverse___rarg(x_3);
x_13 = lean_array_mk(x_12);
x_14 = l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1;
x_15 = l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__3;
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_13);
lean_inc(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = l_List_appendTR___rarg(x_4, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Grind_Result_toMessageData___lambda__2(x_1, x_2, x_18, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_Result_toMessageData___lambda__2(x_1, x_2, x_4, x_21, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" other goal(s) were not fully processed due to previous failures, threshold: `(failures := ", 91, 91);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")`", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issue", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Result_toMessageData___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Result_toMessageData___closed__9() {
_start:
{
lean_object* x_1; double x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Result_toMessageData___closed__8;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1;
x_3 = 1;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_List_mapM_loop___at_Lean_Meta_Grind_Result_toMessageData___spec__1(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_List_lengthTRAux___rarg(x_13, x_15);
lean_dec(x_13);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = l_Lean_Meta_Grind_Result_toMessageData___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_Grind_Result_toMessageData___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_MessageData_ofFormat(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_Grind_Result_toMessageData___closed__6;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_Grind_Result_toMessageData___closed__9;
x_33 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_Grind_Result_toMessageData___lambda__3(x_1, x_8, x_35, x_10, x_36, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Grind_Result_toMessageData___lambda__3(x_1, x_8, x_12, x_10, x_38, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_1);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Result_toMessageData___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Result_toMessageData___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Result_toMessageData___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_7, 6);
x_11 = lean_ctor_get(x_7, 7);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2;
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_5);
x_17 = lean_st_ref_take(x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 5);
x_22 = l_Lean_MessageLog_add(x_16, x_21);
lean_ctor_set(x_18, 5, x_22);
x_23 = lean_st_ref_set(x_8, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
x_37 = lean_ctor_get(x_18, 7);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_38 = l_Lean_MessageLog_add(x_16, x_35);
x_39 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set(x_39, 7, x_37);
x_40 = lean_st_ref_set(x_8, x_39, x_19);
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
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__2;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__3;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__4;
x_15 = lean_string_dec_eq(x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__5;
x_17 = lean_string_dec_eq(x_7, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
default: 
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_187; uint8_t x_188; 
x_187 = 2;
x_188 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_box(0);
x_12 = x_189;
goto block_186;
}
else
{
lean_object* x_190; uint8_t x_191; 
lean_inc(x_2);
x_190 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_12 = x_192;
goto block_186;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_9);
lean_dec(x_2);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_11);
return x_194;
}
}
block_186:
{
uint8_t x_13; lean_object* x_180; uint8_t x_181; uint8_t x_182; 
lean_dec(x_12);
x_180 = lean_ctor_get(x_9, 2);
lean_inc(x_180);
x_181 = 1;
x_182 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_181);
if (x_182 == 0)
{
lean_dec(x_180);
x_13 = x_3;
goto block_179;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__2;
x_184 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_180, x_183);
lean_dec(x_180);
if (x_184 == 0)
{
x_13 = x_3;
goto block_179;
}
else
{
uint8_t x_185; 
x_185 = 2;
x_13 = x_185;
goto block_179;
}
}
block_179:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 5);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
x_18 = l_Lean_replaceRef(x_1, x_16);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_Syntax_getPos_x3f(x_18, x_19);
x_21 = l_Lean_Syntax_getTailPos_x3f(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_FileMap_toPosition(x_15, x_26);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (x_17 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_22);
x_29 = lean_box(0);
x_30 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_24, x_14, x_27, x_28, x_13, x_29, x_9, x_10, x_25);
lean_dec(x_9);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_24);
x_32 = l_Lean_MessageData_hasTag(x_31, x_24);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_9);
x_33 = lean_box(0);
lean_ctor_set(x_22, 0, x_33);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_22);
x_34 = lean_box(0);
x_35 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_24, x_14, x_27, x_28, x_13, x_34, x_9, x_10, x_25);
lean_dec(x_9);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_FileMap_toPosition(x_15, x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
if (x_17 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_36, x_14, x_39, x_40, x_13, x_41, x_9, x_10, x_37);
lean_dec(x_9);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_36);
x_44 = l_Lean_MessageData_hasTag(x_43, x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_14);
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_36, x_14, x_39, x_40, x_13, x_47, x_9, x_10, x_37);
lean_dec(x_9);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_56 = l_Lean_FileMap_toPosition(x_15, x_55);
x_57 = l_Lean_FileMap_toPosition(x_15, x_50);
lean_dec(x_50);
lean_ctor_set(x_21, 0, x_57);
if (x_17 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_51);
x_58 = lean_box(0);
x_59 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_53, x_14, x_56, x_21, x_13, x_58, x_9, x_10, x_54);
lean_dec(x_9);
return x_59;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_53);
x_61 = l_Lean_MessageData_hasTag(x_60, x_53);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_21);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_14);
lean_dec(x_9);
x_62 = lean_box(0);
lean_ctor_set(x_51, 0, x_62);
return x_51;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_free_object(x_51);
x_63 = lean_box(0);
x_64 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_53, x_14, x_56, x_21, x_13, x_63, x_9, x_10, x_54);
lean_dec(x_9);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_67 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_68 = l_Lean_FileMap_toPosition(x_15, x_67);
x_69 = l_Lean_FileMap_toPosition(x_15, x_50);
lean_dec(x_50);
lean_ctor_set(x_21, 0, x_69);
if (x_17 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_65, x_14, x_68, x_21, x_13, x_70, x_9, x_10, x_66);
lean_dec(x_9);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_65);
x_73 = l_Lean_MessageData_hasTag(x_72, x_65);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_21);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_14);
lean_dec(x_9);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_box(0);
x_77 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_65, x_14, x_68, x_21, x_13, x_76, x_9, x_10, x_66);
lean_dec(x_9);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_78 = lean_ctor_get(x_21, 0);
lean_inc(x_78);
lean_dec(x_21);
x_79 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_84 = l_Lean_FileMap_toPosition(x_15, x_83);
x_85 = l_Lean_FileMap_toPosition(x_15, x_78);
lean_dec(x_78);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
if (x_17 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_80, x_14, x_84, x_86, x_13, x_87, x_9, x_10, x_81);
lean_dec(x_9);
return x_88;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_80);
x_90 = l_Lean_MessageData_hasTag(x_89, x_80);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_14);
lean_dec(x_9);
x_91 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_82;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_81);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
x_93 = lean_box(0);
x_94 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_80, x_14, x_84, x_86, x_13, x_93, x_9, x_10, x_81);
lean_dec(x_9);
return x_94;
}
}
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_20);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_20, 0);
x_97 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = l_Lean_FileMap_toPosition(x_15, x_96);
lean_dec(x_96);
lean_inc(x_101);
lean_ctor_set(x_20, 0, x_101);
if (x_17 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_free_object(x_97);
x_102 = lean_box(0);
x_103 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_99, x_14, x_101, x_20, x_13, x_102, x_9, x_10, x_100);
lean_dec(x_9);
return x_103;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_99);
x_105 = l_Lean_MessageData_hasTag(x_104, x_99);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_20);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_14);
lean_dec(x_9);
x_106 = lean_box(0);
lean_ctor_set(x_97, 0, x_106);
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_free_object(x_97);
x_107 = lean_box(0);
x_108 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_99, x_14, x_101, x_20, x_13, x_107, x_9, x_10, x_100);
lean_dec(x_9);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_97, 0);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_97);
x_111 = l_Lean_FileMap_toPosition(x_15, x_96);
lean_dec(x_96);
lean_inc(x_111);
lean_ctor_set(x_20, 0, x_111);
if (x_17 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_box(0);
x_113 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_109, x_14, x_111, x_20, x_13, x_112, x_9, x_10, x_110);
lean_dec(x_9);
return x_113;
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_109);
x_115 = l_Lean_MessageData_hasTag(x_114, x_109);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_20);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_14);
lean_dec(x_9);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_110);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_box(0);
x_119 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_109, x_14, x_111, x_20, x_13, x_118, x_9, x_10, x_110);
lean_dec(x_9);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_20, 0);
lean_inc(x_120);
lean_dec(x_20);
x_121 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = l_Lean_FileMap_toPosition(x_15, x_120);
lean_dec(x_120);
lean_inc(x_125);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (x_17 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_124);
x_127 = lean_box(0);
x_128 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_122, x_14, x_125, x_126, x_13, x_127, x_9, x_10, x_123);
lean_dec(x_9);
return x_128;
}
else
{
lean_object* x_129; uint8_t x_130; 
x_129 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_122);
x_130 = l_Lean_MessageData_hasTag(x_129, x_122);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_14);
lean_dec(x_9);
x_131 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_124;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_123);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_124);
x_133 = lean_box(0);
x_134 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_122, x_14, x_125, x_126, x_13, x_133, x_9, x_10, x_123);
lean_dec(x_9);
return x_134;
}
}
}
}
else
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_20, 0);
lean_inc(x_135);
lean_dec(x_20);
x_136 = !lean_is_exclusive(x_21);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_21, 0);
x_138 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_15);
x_142 = l_Lean_FileMap_toPosition(x_15, x_135);
lean_dec(x_135);
x_143 = l_Lean_FileMap_toPosition(x_15, x_137);
lean_dec(x_137);
lean_ctor_set(x_21, 0, x_143);
if (x_17 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_free_object(x_138);
x_144 = lean_box(0);
x_145 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_140, x_14, x_142, x_21, x_13, x_144, x_9, x_10, x_141);
lean_dec(x_9);
return x_145;
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_140);
x_147 = l_Lean_MessageData_hasTag(x_146, x_140);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_21);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_14);
lean_dec(x_9);
x_148 = lean_box(0);
lean_ctor_set(x_138, 0, x_148);
return x_138;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_free_object(x_138);
x_149 = lean_box(0);
x_150 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_140, x_14, x_142, x_21, x_13, x_149, x_9, x_10, x_141);
lean_dec(x_9);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_138, 0);
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_138);
lean_inc(x_15);
x_153 = l_Lean_FileMap_toPosition(x_15, x_135);
lean_dec(x_135);
x_154 = l_Lean_FileMap_toPosition(x_15, x_137);
lean_dec(x_137);
lean_ctor_set(x_21, 0, x_154);
if (x_17 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_box(0);
x_156 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_151, x_14, x_153, x_21, x_13, x_155, x_9, x_10, x_152);
lean_dec(x_9);
return x_156;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_151);
x_158 = l_Lean_MessageData_hasTag(x_157, x_151);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_21);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_14);
lean_dec(x_9);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_box(0);
x_162 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_151, x_14, x_153, x_21, x_13, x_161, x_9, x_10, x_152);
lean_dec(x_9);
return x_162;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_163 = lean_ctor_get(x_21, 0);
lean_inc(x_163);
lean_dec(x_21);
x_164 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
lean_inc(x_15);
x_168 = l_Lean_FileMap_toPosition(x_15, x_135);
lean_dec(x_135);
x_169 = l_Lean_FileMap_toPosition(x_15, x_163);
lean_dec(x_163);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
if (x_17 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_167);
x_171 = lean_box(0);
x_172 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_165, x_14, x_168, x_170, x_13, x_171, x_9, x_10, x_166);
lean_dec(x_9);
return x_172;
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1;
lean_inc(x_165);
x_174 = l_Lean_MessageData_hasTag(x_173, x_165);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_14);
lean_dec(x_9);
x_175 = lean_box(0);
if (lean_is_scalar(x_167)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_167;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_166);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_167);
x_177 = lean_box(0);
x_178 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_165, x_14, x_168, x_170, x_13, x_177, x_9, x_10, x_166);
lean_dec(x_9);
return x_178;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Grind_main___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set(x_17, 5, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 8);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 9);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_7, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 10);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_isEmpty___rarg(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Grind_main___lambda__1(x_1, x_2, x_3, x_16, x_20, x_24, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_isDiagnosticsEnabled(x_10, x_11, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Grind_main___lambda__1(x_1, x_2, x_3, x_16, x_20, x_24, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_35 = l_Lean_Meta_Grind_Counters_toMessageData_x3f(x_24, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Grind_main___lambda__1(x_1, x_2, x_3, x_16, x_20, x_24, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = 0;
lean_inc(x_10);
x_43 = l_Lean_log___at_Lean_Meta_Grind_main___spec__1(x_41, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_main___lambda__1(x_1, x_2, x_3, x_16, x_20, x_24, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
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
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("final", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3;
x_2 = l_Lean_Meta_Grind_main___lambda__3___closed__1;
x_3 = l_Lean_Meta_Grind_main___lambda__3___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_12 = l_Lean_Meta_Grind_solve(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = l_Lean_Meta_Grind_main___lambda__3___closed__3;
x_19 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_reportIssue___spec__1(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_13);
lean_dec(x_3);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_Meta_Grind_main___lambda__2(x_2, x_16, x_17, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_Grind_ppGoals(x_3, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_31);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_31);
lean_ctor_set(x_13, 0, x_19);
x_32 = l_Lean_addTrace___at_Lean_Meta_Grind_reportIssue___spec__2(x_18, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_main___lambda__2(x_2, x_16, x_17, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_19);
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
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
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Lean_Meta_Grind_ppGoals(x_3, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_44);
lean_ctor_set(x_13, 0, x_45);
x_46 = l_Lean_addTrace___at_Lean_Meta_Grind_reportIssue___spec__2(x_18, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_main___lambda__2(x_2, x_16, x_17, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
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
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = l_Lean_Meta_Grind_main___lambda__3___closed__3;
x_57 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_reportIssue___spec__1(x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_box(0);
x_62 = l_Lean_Meta_Grind_main___lambda__2(x_2, x_54, x_55, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_Meta_Grind_ppGoals(x_3, x_7, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3;
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_64;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_addTrace___at_Lean_Meta_Grind_reportIssue___spec__2(x_56, x_70, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_main___lambda__2(x_2, x_54, x_55, x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_77 = x_65;
} else {
 lean_dec_ref(x_65);
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
}
}
else
{
uint8_t x_79; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_12);
if (x_79 == 0)
{
return x_12;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_12, 0);
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_12);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore), 10, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_inc(x_2);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lambda__3___boxed), 11, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_2);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_Grind_GrindM_run___rarg(x_12, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Grind_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_log___at_Lean_Meta_Grind_main___spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_main___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
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
l_Lean_Meta_Grind_mkMethods___closed__1 = _init_l_Lean_Meta_Grind_mkMethods___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkMethods___closed__1);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__1 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__1);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__2 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__2);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__3 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__3);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__4 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__4);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__5 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__5);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__6 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__6);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__7 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__7);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__8 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__8);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__9 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__9);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__10 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__10);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__11 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__11);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__12 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__12);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__13 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__13);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__14 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__14);
l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1 = _init_l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1);
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
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__3);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__1();
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__1___closed__5);
l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___closed__1 = _init_l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___spec__2___closed__1);
l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1 = _init_l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_toList___at_Lean_Meta_Grind_Counters_toMessageData_x3f___spec__1___closed__1);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__1);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__2);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__3);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__1___closed__4);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__1);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__2);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__3);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___lambda__2___closed__4);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__1 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__1);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__2 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__2);
l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__3 = _init_l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Counters_toMessageData_x3f___closed__3);
l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__1);
l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lambda__1___closed__2);
l_Lean_Meta_Grind_Result_toMessageData___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lambda__2___closed__1);
l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__1);
l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__2);
l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___lambda__3___closed__3);
l_Lean_Meta_Grind_Result_toMessageData___closed__1 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__1);
l_Lean_Meta_Grind_Result_toMessageData___closed__2 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__2);
l_Lean_Meta_Grind_Result_toMessageData___closed__3 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__3);
l_Lean_Meta_Grind_Result_toMessageData___closed__4 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__4);
l_Lean_Meta_Grind_Result_toMessageData___closed__5 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__5);
l_Lean_Meta_Grind_Result_toMessageData___closed__6 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__6);
l_Lean_Meta_Grind_Result_toMessageData___closed__7 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__7);
l_Lean_Meta_Grind_Result_toMessageData___closed__8 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__8);
l_Lean_Meta_Grind_Result_toMessageData___closed__9 = _init_l_Lean_Meta_Grind_Result_toMessageData___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Result_toMessageData___closed__9);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__1 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__1);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__2 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__2);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__3 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__3();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__3);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__4 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__4();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__4);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__5 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__5();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___lambda__2___closed__5);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__1);
l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__2 = _init_l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__2();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Grind_main___spec__2___closed__2);
l_Lean_Meta_Grind_main___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_main___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__3___closed__1);
l_Lean_Meta_Grind_main___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_main___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__3___closed__2);
l_Lean_Meta_Grind_main___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_main___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__3___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
