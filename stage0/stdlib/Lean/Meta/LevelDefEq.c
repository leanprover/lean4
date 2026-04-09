// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: public import Lean.Util.CollectMVars public import Lean.Meta.DecLevel public import Lean.Meta.HasAssignableMVar
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
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_hasAssignableLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffset(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.LevelDefEq"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "_private.Lean.Meta.LevelDefEq.0.Lean.Meta.solveSelfMax"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "assertion violation: v.isMax\n  "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isLevelDefEq"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stuck"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 131, 35, 104, 114, 254, 231, 20)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_isLevelDefEqAuxImpl___closed__0;
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__1 = (const lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value;
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__2;
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LevelDefEq"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 184, 81, 18, 195, 210, 152, 110)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(30, 209, 144, 83, 13, 92, 153, 140)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 46, 128, 72, 56, 107, 184, 50)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 118, 41, 27, 129, 22, 6, 162)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 140, 12, 137, 237, 91, 220, 23)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 22, 128, 151, 69, 154, 194, 107)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 83, 161, 161, 122, 158, 1, 20)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 252, 13, 249, 138, 174, 25, 171)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 71, 113, 221, 79, 59, 169, 47)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1935786688) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 8, 214, 23, 23, 5, 229, 17)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 132, 61, 103, 235, 209, 75, 200)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 197, 4, 86, 142, 168, 54, 111)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(108, 210, 92, 10, 251, 40, 69, 139)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object* v_lvl_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_2_) == 2)
{
lean_object* v_a_3_; lean_object* v_a_4_; uint8_t v___x_5_; 
v_a_3_ = lean_ctor_get(v_a_2_, 0);
v_a_4_ = lean_ctor_get(v_a_2_, 1);
v___x_5_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_1_, v_a_3_);
if (v___x_5_ == 0)
{
v_a_2_ = v_a_4_;
goto _start;
}
else
{
return v___x_5_;
}
}
else
{
uint8_t v___x_7_; 
v___x_7_ = lean_level_eq(v_a_2_, v_lvl_1_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
v___x_8_ = l_Lean_Level_occurs(v_lvl_1_, v_a_2_);
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = 0;
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object* v_lvl_10_, lean_object* v_a_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_10_, v_a_11_);
lean_dec(v_a_11_);
lean_dec(v_lvl_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object* v_lvl_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 2)
{
lean_object* v_a_16_; lean_object* v_a_17_; uint8_t v___x_18_; 
v_a_16_ = lean_ctor_get(v_x_15_, 0);
v_a_17_ = lean_ctor_get(v_x_15_, 1);
v___x_18_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_14_, v_a_16_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_14_, v_a_17_);
return v___x_19_;
}
else
{
return v___x_18_;
}
}
else
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object* v_lvl_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_lvl_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec(v_lvl_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
switch(lean_obj_tag(v_x_26_))
{
case 2:
{
lean_object* v_a_28_; lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_28_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_28_);
v_a_29_ = lean_ctor_get(v_x_26_, 1);
lean_inc(v_a_29_);
lean_dec_ref(v_x_26_);
v___x_30_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_25_, v_a_28_, v_x_27_);
v_x_26_ = v_a_29_;
v_x_27_ = v___x_30_;
goto _start;
}
case 5:
{
lean_object* v_a_32_; uint8_t v___x_33_; 
v_a_32_ = lean_ctor_get(v_x_26_, 0);
v___x_33_ = l_Lean_instBEqLevelMVarId_beq(v_a_32_, v_mvarId_25_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_mkLevelMax_x27(v_x_27_, v_x_26_);
return v___x_34_;
}
else
{
lean_dec_ref(v_x_26_);
return v_x_27_;
}
}
default: 
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_mkLevelMax_x27(v_x_27_, v_x_26_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* v_mvarId_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_36_, v_x_37_, v_x_38_);
lean_dec(v_mvarId_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_214__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_214__overap_48_ = lean_panic_fn_borrowed(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_214__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(lean_object* v_msg_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v_msg_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
lean_object* v_ks_61_; lean_object* v_vs_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_86_; 
v_ks_61_ = lean_ctor_get(v_x_57_, 0);
v_vs_62_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_86_ == 0)
{
v___x_64_ = v_x_57_;
v_isShared_65_ = v_isSharedCheck_86_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_vs_62_);
lean_inc(v_ks_61_);
lean_dec(v_x_57_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_86_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_array_get_size(v_ks_61_);
v___x_67_ = lean_nat_dec_lt(v_x_58_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
lean_dec(v_x_58_);
v___x_68_ = lean_array_push(v_ks_61_, v_x_59_);
v___x_69_ = lean_array_push(v_vs_62_, v_x_60_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_69_);
lean_ctor_set(v___x_64_, 0, v___x_68_);
v___x_71_ = v___x_64_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
else
{
lean_object* v_k_x27_73_; uint8_t v___x_74_; 
v_k_x27_73_ = lean_array_fget_borrowed(v_ks_61_, v_x_58_);
v___x_74_ = l_Lean_instBEqLevelMVarId_beq(v_x_59_, v_k_x27_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_76_; 
if (v_isShared_65_ == 0)
{
v___x_76_ = v___x_64_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_ks_61_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_vs_62_);
v___x_76_ = v_reuseFailAlloc_80_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_x_58_, v___x_77_);
lean_dec(v_x_58_);
v_x_57_ = v___x_76_;
v_x_58_ = v___x_78_;
goto _start;
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_81_ = lean_array_fset(v_ks_61_, v_x_58_, v_x_59_);
v___x_82_ = lean_array_fset(v_vs_62_, v_x_58_, v_x_60_);
lean_dec(v_x_58_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_82_);
lean_ctor_set(v___x_64_, 0, v___x_81_);
v___x_84_ = v___x_64_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_87_, lean_object* v_k_88_, lean_object* v_v_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_87_, v___x_90_, v_k_88_, v_v_89_);
return v___x_91_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; 
v___x_92_ = ((size_t)5ULL);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_shift_left(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_97_ = lean_usize_sub(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(lean_object* v_x_99_, size_t v_x_100_, size_t v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_es_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; lean_object* v_j_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_es_104_ = lean_ctor_get(v_x_99_, 0);
v___x_105_ = ((size_t)5ULL);
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_108_ = lean_usize_land(v_x_100_, v___x_107_);
v_j_109_ = lean_usize_to_nat(v___x_108_);
v___x_110_ = lean_array_get_size(v_es_104_);
v___x_111_ = lean_nat_dec_lt(v_j_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec(v_j_109_);
lean_dec(v_x_103_);
lean_dec(v_x_102_);
return v_x_99_;
}
else
{
lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_148_; 
lean_inc_ref(v_es_104_);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v_x_99_, 0);
lean_dec(v_unused_149_);
v___x_113_ = v_x_99_;
v_isShared_114_ = v_isSharedCheck_148_;
goto v_resetjp_112_;
}
else
{
lean_dec(v_x_99_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_148_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_v_115_; lean_object* v___x_116_; lean_object* v_xs_x27_117_; lean_object* v___y_119_; 
v_v_115_ = lean_array_fget(v_es_104_, v_j_109_);
v___x_116_ = lean_box(0);
v_xs_x27_117_ = lean_array_fset(v_es_104_, v_j_109_, v___x_116_);
switch(lean_obj_tag(v_v_115_))
{
case 0:
{
lean_object* v_key_124_; lean_object* v_val_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_key_124_ = lean_ctor_get(v_v_115_, 0);
v_val_125_ = lean_ctor_get(v_v_115_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_v_115_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v_v_115_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_val_125_);
lean_inc(v_key_124_);
lean_dec(v_v_115_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_instBEqLevelMVarId_beq(v_x_102_, v_key_124_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_127_);
v___x_130_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_124_, v_val_125_, v_x_102_, v_x_103_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___y_119_ = v___x_131_;
goto v___jp_118_;
}
else
{
lean_object* v___x_133_; 
lean_dec(v_val_125_);
lean_dec(v_key_124_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_x_103_);
lean_ctor_set(v___x_127_, 0, v_x_102_);
v___x_133_ = v___x_127_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_x_102_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_x_103_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v___y_119_ = v___x_133_;
goto v___jp_118_;
}
}
}
}
case 1:
{
lean_object* v_node_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_146_; 
v_node_136_ = lean_ctor_get(v_v_115_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_v_115_);
if (v_isSharedCheck_146_ == 0)
{
v___x_138_ = v_v_115_;
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_node_136_);
lean_dec(v_v_115_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_140_ = lean_usize_shift_right(v_x_100_, v___x_105_);
v___x_141_ = lean_usize_add(v_x_101_, v___x_106_);
v___x_142_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_node_136_, v___x_140_, v___x_141_, v_x_102_, v_x_103_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_142_);
v___x_144_ = v___x_138_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v___y_119_ = v___x_144_;
goto v___jp_118_;
}
}
}
default: 
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_x_102_);
lean_ctor_set(v___x_147_, 1, v_x_103_);
v___y_119_ = v___x_147_;
goto v___jp_118_;
}
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_array_fset(v_xs_x27_117_, v_j_109_, v___y_119_);
lean_dec(v_j_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_120_);
v___x_122_ = v___x_113_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
else
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_171_; 
v_ks_150_ = lean_ctor_get(v_x_99_, 0);
v_vs_151_ = lean_ctor_get(v_x_99_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_171_ == 0)
{
v___x_153_ = v_x_99_;
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_vs_151_);
lean_inc(v_ks_150_);
lean_dec(v_x_99_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_ks_150_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_vs_151_);
v___x_156_ = v_reuseFailAlloc_170_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v_newNode_157_; uint8_t v___y_159_; size_t v___x_165_; uint8_t v___x_166_; 
v_newNode_157_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3___redArg(v___x_156_, v_x_102_, v_x_103_);
v___x_165_ = ((size_t)7ULL);
v___x_166_ = lean_usize_dec_le(v___x_165_, v_x_101_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_167_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_157_);
v___x_168_ = lean_unsigned_to_nat(4u);
v___x_169_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
lean_dec(v___x_167_);
v___y_159_ = v___x_169_;
goto v___jp_158_;
}
else
{
v___y_159_ = v___x_166_;
goto v___jp_158_;
}
v___jp_158_:
{
if (v___y_159_ == 0)
{
lean_object* v_ks_160_; lean_object* v_vs_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_ks_160_ = lean_ctor_get(v_newNode_157_, 0);
lean_inc_ref(v_ks_160_);
v_vs_161_ = lean_ctor_get(v_newNode_157_, 1);
lean_inc_ref(v_vs_161_);
lean_dec_ref(v_newNode_157_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg(v_x_101_, v_ks_160_, v_vs_161_, v___x_162_, v___x_163_);
lean_dec_ref(v_vs_161_);
lean_dec_ref(v_ks_160_);
return v___x_164_;
}
else
{
return v_newNode_157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_172_, lean_object* v_keys_173_, lean_object* v_vals_174_, lean_object* v_i_175_, lean_object* v_entries_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_array_get_size(v_keys_173_);
v___x_178_ = lean_nat_dec_lt(v_i_175_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec(v_i_175_);
return v_entries_176_;
}
else
{
lean_object* v_k_179_; lean_object* v_v_180_; uint64_t v___x_181_; size_t v_h_182_; size_t v___x_183_; lean_object* v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v_h_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_k_179_ = lean_array_fget_borrowed(v_keys_173_, v_i_175_);
v_v_180_ = lean_array_fget_borrowed(v_vals_174_, v_i_175_);
v___x_181_ = l_Lean_instHashableLevelMVarId_hash(v_k_179_);
v_h_182_ = lean_uint64_to_usize(v___x_181_);
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_sub(v_depth_172_, v___x_185_);
v___x_187_ = lean_usize_mul(v___x_183_, v___x_186_);
v_h_188_ = lean_usize_shift_right(v_h_182_, v___x_187_);
v___x_189_ = lean_nat_add(v_i_175_, v___x_184_);
lean_dec(v_i_175_);
lean_inc(v_v_180_);
lean_inc(v_k_179_);
v___x_190_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_entries_176_, v_h_188_, v_depth_172_, v_k_179_, v_v_180_);
v_i_175_ = v___x_189_;
v_entries_176_ = v___x_190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_192_, lean_object* v_keys_193_, lean_object* v_vals_194_, lean_object* v_i_195_, lean_object* v_entries_196_){
_start:
{
size_t v_depth_boxed_197_; lean_object* v_res_198_; 
v_depth_boxed_197_ = lean_unbox_usize(v_depth_192_);
lean_dec(v_depth_192_);
v_res_198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_197_, v_keys_193_, v_vals_194_, v_i_195_, v_entries_196_);
lean_dec_ref(v_vals_194_);
lean_dec_ref(v_keys_193_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
size_t v_x_729__boxed_204_; size_t v_x_730__boxed_205_; lean_object* v_res_206_; 
v_x_729__boxed_204_ = lean_unbox_usize(v_x_200_);
lean_dec(v_x_200_);
v_x_730__boxed_205_ = lean_unbox_usize(v_x_201_);
lean_dec(v_x_201_);
v_res_206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_199_, v_x_729__boxed_204_, v_x_730__boxed_205_, v_x_202_, v_x_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint64_t v___x_210_; size_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___x_210_ = l_Lean_instHashableLevelMVarId_hash(v_x_208_);
v___x_211_ = lean_uint64_to_usize(v___x_210_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_207_, v___x_211_, v___x_212_, v_x_208_, v_x_209_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object* v_mvarId_214_, lean_object* v_val_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; lean_object* v_mctx_219_; lean_object* v_cache_220_; lean_object* v_zetaDeltaFVarIds_221_; lean_object* v_postponed_222_; lean_object* v_diag_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_251_; 
v___x_218_ = lean_st_ref_take(v___y_216_);
v_mctx_219_ = lean_ctor_get(v___x_218_, 0);
v_cache_220_ = lean_ctor_get(v___x_218_, 1);
v_zetaDeltaFVarIds_221_ = lean_ctor_get(v___x_218_, 2);
v_postponed_222_ = lean_ctor_get(v___x_218_, 3);
v_diag_223_ = lean_ctor_get(v___x_218_, 4);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_251_ == 0)
{
v___x_225_ = v___x_218_;
v_isShared_226_ = v_isSharedCheck_251_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_diag_223_);
lean_inc(v_postponed_222_);
lean_inc(v_zetaDeltaFVarIds_221_);
lean_inc(v_cache_220_);
lean_inc(v_mctx_219_);
lean_dec(v___x_218_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_251_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_depth_227_; lean_object* v_levelAssignDepth_228_; lean_object* v_lmvarCounter_229_; lean_object* v_mvarCounter_230_; lean_object* v_lDecls_231_; lean_object* v_decls_232_; lean_object* v_userNames_233_; lean_object* v_lAssignment_234_; lean_object* v_eAssignment_235_; lean_object* v_dAssignment_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_250_; 
v_depth_227_ = lean_ctor_get(v_mctx_219_, 0);
v_levelAssignDepth_228_ = lean_ctor_get(v_mctx_219_, 1);
v_lmvarCounter_229_ = lean_ctor_get(v_mctx_219_, 2);
v_mvarCounter_230_ = lean_ctor_get(v_mctx_219_, 3);
v_lDecls_231_ = lean_ctor_get(v_mctx_219_, 4);
v_decls_232_ = lean_ctor_get(v_mctx_219_, 5);
v_userNames_233_ = lean_ctor_get(v_mctx_219_, 6);
v_lAssignment_234_ = lean_ctor_get(v_mctx_219_, 7);
v_eAssignment_235_ = lean_ctor_get(v_mctx_219_, 8);
v_dAssignment_236_ = lean_ctor_get(v_mctx_219_, 9);
v_isSharedCheck_250_ = !lean_is_exclusive(v_mctx_219_);
if (v_isSharedCheck_250_ == 0)
{
v___x_238_ = v_mctx_219_;
v_isShared_239_ = v_isSharedCheck_250_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_dAssignment_236_);
lean_inc(v_eAssignment_235_);
lean_inc(v_lAssignment_234_);
lean_inc(v_userNames_233_);
lean_inc(v_decls_232_);
lean_inc(v_lDecls_231_);
lean_inc(v_mvarCounter_230_);
lean_inc(v_lmvarCounter_229_);
lean_inc(v_levelAssignDepth_228_);
lean_inc(v_depth_227_);
lean_dec(v_mctx_219_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_250_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_234_, v_mvarId_214_, v_val_215_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 7, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_depth_227_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_levelAssignDepth_228_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_lmvarCounter_229_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_mvarCounter_230_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_lDecls_231_);
lean_ctor_set(v_reuseFailAlloc_249_, 5, v_decls_232_);
lean_ctor_set(v_reuseFailAlloc_249_, 6, v_userNames_233_);
lean_ctor_set(v_reuseFailAlloc_249_, 7, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 8, v_eAssignment_235_);
lean_ctor_set(v_reuseFailAlloc_249_, 9, v_dAssignment_236_);
v___x_242_ = v_reuseFailAlloc_249_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_242_);
v___x_244_ = v___x_225_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_zetaDeltaFVarIds_221_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_postponed_222_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_diag_223_);
v___x_244_ = v_reuseFailAlloc_248_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_st_ref_set(v___y_216_, v___x_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* v_mvarId_252_, lean_object* v_val_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_252_, v_val_253_, v___y_254_);
lean_dec(v___y_254_);
return v_res_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_261_ = lean_unsigned_to_nat(2u);
v___x_262_ = lean_unsigned_to_nat(39u);
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_265_ = l_mkPanicMessageWithDecl(v___x_264_, v___x_263_, v___x_262_, v___x_261_, v___x_260_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_266_, lean_object* v_v_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Lean_Level_isMax(v_v_267_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v_v_267_);
lean_dec(v_mvarId_266_);
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_275_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_274_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_mkFreshLevelMVar(v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v___x_278_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_266_, v_v_267_, v_a_277_);
v___x_279_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_266_, v___x_278_, v_a_269_);
return v___x_279_;
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v_v_267_);
lean_dec(v_mvarId_266_);
v_a_280_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_288_, lean_object* v_v_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_288_, v_v_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_296_, lean_object* v_val_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_296_, v_val_297_, v___y_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_304_, lean_object* v_val_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_304_, v_val_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_313_, v_x_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_317_, lean_object* v_x_318_, size_t v_x_319_, size_t v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_318_, v_x_319_, v_x_320_, v_x_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
size_t v_x_1034__boxed_330_; size_t v_x_1035__boxed_331_; lean_object* v_res_332_; 
v_x_1034__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_x_1035__boxed_331_ = lean_unbox_usize(v_x_327_);
lean_dec(v_x_327_);
v_res_332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_324_, v_x_325_, v_x_1034__boxed_330_, v_x_1035__boxed_331_, v_x_328_, v_x_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_333_, lean_object* v_n_334_, lean_object* v_k_335_, lean_object* v_v_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3___redArg(v_n_334_, v_k_335_, v_v_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_338_, size_t v_depth_339_, lean_object* v_keys_340_, lean_object* v_vals_341_, lean_object* v_heq_342_, lean_object* v_i_343_, lean_object* v_entries_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_339_, v_keys_340_, v_vals_341_, v_i_343_, v_entries_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_346_, lean_object* v_depth_347_, lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_heq_350_, lean_object* v_i_351_, lean_object* v_entries_352_){
_start:
{
size_t v_depth_boxed_353_; lean_object* v_res_354_; 
v_depth_boxed_353_ = lean_unbox_usize(v_depth_347_);
lean_dec(v_depth_347_);
v_res_354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_346_, v_depth_boxed_353_, v_keys_348_, v_vals_349_, v_heq_350_, v_i_351_, v_entries_352_);
lean_dec_ref(v_vals_349_);
lean_dec_ref(v_keys_348_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_356_, v_x_357_, v_x_358_, v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(lean_object* v_u_361_, lean_object* v_v_x27_362_, lean_object* v_mvarId_363_, lean_object* v_a_364_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_level_eq(v_u_361_, v_v_x27_362_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v_mvarId_363_);
lean_dec(v_u_361_);
v___x_367_ = lean_box(v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v___x_369_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_363_, v_u_361_, v_a_364_);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_378_);
v___x_371_ = v___x_369_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_369_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_box(v___x_366_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg___boxed(lean_object* v_u_379_, lean_object* v_v_x27_380_, lean_object* v_mvarId_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_379_, v_v_x27_380_, v_mvarId_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec(v_v_x27_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_385_, lean_object* v_v_x27_386_, lean_object* v_mvarId_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_385_, v_v_x27_386_, v_mvarId_387_, v_a_389_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_394_, lean_object* v_v_x27_395_, lean_object* v_mvarId_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_394_, v_v_x27_395_, v_mvarId_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_v_x27_395_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(lean_object* v_u_403_, lean_object* v_v_404_, lean_object* v_a_405_){
_start:
{
if (lean_obj_tag(v_v_404_) == 2)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v_v_404_, 1);
lean_inc(v_a_411_);
if (lean_obj_tag(v_a_411_) == 5)
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v_v_404_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v_v_404_);
v_a_413_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_a_413_);
lean_dec_ref(v_a_411_);
v___x_414_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_403_, v_a_412_, v_a_413_, v_a_405_);
lean_dec(v_a_412_);
return v___x_414_;
}
else
{
lean_object* v_a_415_; 
v_a_415_ = lean_ctor_get(v_v_404_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v_v_404_);
if (lean_obj_tag(v_a_415_) == 5)
{
lean_object* v_a_416_; lean_object* v___x_417_; 
v_a_416_ = lean_ctor_get(v_a_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v_a_415_);
v___x_417_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_403_, v_a_411_, v_a_416_, v_a_405_);
lean_dec(v_a_411_);
return v___x_417_;
}
else
{
lean_dec(v_a_415_);
lean_dec(v_a_411_);
lean_dec(v_u_403_);
goto v___jp_407_;
}
}
}
else
{
lean_dec(v_v_404_);
lean_dec(v_u_403_);
goto v___jp_407_;
}
v___jp_407_:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = 0;
v___x_409_ = lean_box(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg___boxed(lean_object* v_u_418_, lean_object* v_v_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_418_, v_v_419_, v_a_420_);
lean_dec(v_a_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_423_, lean_object* v_v_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_423_, v_v_424_, v_a_426_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_431_, lean_object* v_v_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_431_, v_v_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(lean_object* v_u_u2081_439_, lean_object* v_u_u2082_440_, lean_object* v_v_x27_441_, lean_object* v_mvarId_442_, lean_object* v_a_443_){
_start:
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_level_eq(v_u_u2081_439_, v_v_x27_441_);
v___x_446_ = 1;
if (v___x_445_ == 0)
{
uint8_t v___x_447_; 
v___x_447_ = lean_level_eq(v_u_u2082_440_, v_v_x27_441_);
lean_dec(v_u_u2082_440_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v_mvarId_442_);
lean_dec(v_u_u2081_439_);
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
v___x_450_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_442_, v_u_u2081_439_, v_a_443_);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_450_, 0);
lean_dec(v_unused_459_);
v___x_452_ = v___x_450_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_dec(v___x_450_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_box(v___x_446_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_u_u2081_439_);
v___x_460_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_442_, v_u_u2082_440_, v_a_443_);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_460_, 0);
lean_dec(v_unused_469_);
v___x_462_ = v___x_460_;
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
else
{
lean_dec(v___x_460_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_box(v___x_446_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg___boxed(lean_object* v_u_u2081_470_, lean_object* v_u_u2082_471_, lean_object* v_v_x27_472_, lean_object* v_mvarId_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_u_u2081_470_, v_u_u2082_471_, v_v_x27_472_, v_mvarId_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec(v_v_x27_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_477_, lean_object* v_u_u2082_478_, lean_object* v_v_x27_479_, lean_object* v_mvarId_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_u_u2081_477_, v_u_u2082_478_, v_v_x27_479_, v_mvarId_480_, v_a_482_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_487_, lean_object* v_u_u2082_488_, lean_object* v_v_x27_489_, lean_object* v_mvarId_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_487_, v_u_u2082_488_, v_v_x27_489_, v_mvarId_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_v_x27_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(lean_object* v_u_497_, lean_object* v_v_498_, lean_object* v_a_499_){
_start:
{
if (lean_obj_tag(v_u_497_) == 2)
{
if (lean_obj_tag(v_v_498_) == 2)
{
lean_object* v_a_505_; 
v_a_505_ = lean_ctor_get(v_v_498_, 1);
lean_inc(v_a_505_);
if (lean_obj_tag(v_a_505_) == 5)
{
lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_506_ = lean_ctor_get(v_u_497_, 0);
lean_inc(v_a_506_);
v_a_507_ = lean_ctor_get(v_u_497_, 1);
lean_inc(v_a_507_);
lean_dec_ref(v_u_497_);
v_a_508_ = lean_ctor_get(v_v_498_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v_v_498_);
v_a_509_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v_a_505_);
v___x_510_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_499_);
lean_dec(v_a_508_);
return v___x_510_;
}
else
{
lean_object* v_a_511_; 
v_a_511_ = lean_ctor_get(v_v_498_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v_v_498_);
if (lean_obj_tag(v_a_511_) == 5)
{
lean_object* v_a_512_; lean_object* v_a_513_; lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_512_ = lean_ctor_get(v_u_497_, 0);
lean_inc(v_a_512_);
v_a_513_ = lean_ctor_get(v_u_497_, 1);
lean_inc(v_a_513_);
lean_dec_ref(v_u_497_);
v_a_514_ = lean_ctor_get(v_a_511_, 0);
lean_inc(v_a_514_);
lean_dec_ref(v_a_511_);
v___x_515_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_a_512_, v_a_513_, v_a_505_, v_a_514_, v_a_499_);
lean_dec(v_a_505_);
return v___x_515_;
}
else
{
lean_dec(v_a_511_);
lean_dec(v_a_505_);
lean_dec_ref(v_u_497_);
goto v___jp_501_;
}
}
}
else
{
lean_dec_ref(v_u_497_);
lean_dec(v_v_498_);
goto v___jp_501_;
}
}
else
{
lean_dec(v_v_498_);
lean_dec(v_u_497_);
goto v___jp_501_;
}
v___jp_501_:
{
uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = 0;
v___x_503_ = lean_box(v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg___boxed(lean_object* v_u_516_, lean_object* v_v_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_516_, v_v_517_, v_a_518_);
lean_dec(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_521_, lean_object* v_v_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_521_, v_v_522_, v_a_524_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_529_, lean_object* v_v_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_529_, v_v_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(lean_object* v_msgData_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; lean_object* v_env_544_; lean_object* v___x_545_; lean_object* v_mctx_546_; lean_object* v_lctx_547_; lean_object* v_options_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_543_ = lean_st_ref_get(v___y_541_);
v_env_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc_ref(v_env_544_);
lean_dec(v___x_543_);
v___x_545_ = lean_st_ref_get(v___y_539_);
v_mctx_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref(v_mctx_546_);
lean_dec(v___x_545_);
v_lctx_547_ = lean_ctor_get(v___y_538_, 2);
v_options_548_ = lean_ctor_get(v___y_540_, 2);
lean_inc_ref(v_options_548_);
lean_inc_ref(v_lctx_547_);
v___x_549_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_549_, 0, v_env_544_);
lean_ctor_set(v___x_549_, 1, v_mctx_546_);
lean_ctor_set(v___x_549_, 2, v_lctx_547_);
lean_ctor_set(v___x_549_, 3, v_options_548_);
v___x_550_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_msgData_537_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(v_msgData_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_558_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_559_; double v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_float_of_nat(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(lean_object* v_cls_564_, lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_ref_571_; lean_object* v___x_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_617_; 
v_ref_571_ = lean_ctor_get(v___y_568_, 5);
v___x_572_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(v_msg_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_617_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_617_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_617_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v_traceState_578_; lean_object* v_env_579_; lean_object* v_nextMacroScope_580_; lean_object* v_ngen_581_; lean_object* v_auxDeclNGen_582_; lean_object* v_cache_583_; lean_object* v_messages_584_; lean_object* v_infoState_585_; lean_object* v_snapshotTasks_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_616_; 
v___x_577_ = lean_st_ref_take(v___y_569_);
v_traceState_578_ = lean_ctor_get(v___x_577_, 4);
v_env_579_ = lean_ctor_get(v___x_577_, 0);
v_nextMacroScope_580_ = lean_ctor_get(v___x_577_, 1);
v_ngen_581_ = lean_ctor_get(v___x_577_, 2);
v_auxDeclNGen_582_ = lean_ctor_get(v___x_577_, 3);
v_cache_583_ = lean_ctor_get(v___x_577_, 5);
v_messages_584_ = lean_ctor_get(v___x_577_, 6);
v_infoState_585_ = lean_ctor_get(v___x_577_, 7);
v_snapshotTasks_586_ = lean_ctor_get(v___x_577_, 8);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_616_ == 0)
{
v___x_588_ = v___x_577_;
v_isShared_589_ = v_isSharedCheck_616_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snapshotTasks_586_);
lean_inc(v_infoState_585_);
lean_inc(v_messages_584_);
lean_inc(v_cache_583_);
lean_inc(v_traceState_578_);
lean_inc(v_auxDeclNGen_582_);
lean_inc(v_ngen_581_);
lean_inc(v_nextMacroScope_580_);
lean_inc(v_env_579_);
lean_dec(v___x_577_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_616_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
uint64_t v_tid_590_; lean_object* v_traces_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_615_; 
v_tid_590_ = lean_ctor_get_uint64(v_traceState_578_, sizeof(void*)*1);
v_traces_591_ = lean_ctor_get(v_traceState_578_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_traceState_578_);
if (v_isSharedCheck_615_ == 0)
{
v___x_593_ = v_traceState_578_;
v_isShared_594_ = v_isSharedCheck_615_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_traces_591_);
lean_dec(v_traceState_578_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_615_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; double v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0);
v___x_597_ = 0;
v___x_598_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1));
v___x_599_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_599_, 0, v_cls_564_);
lean_ctor_set(v___x_599_, 1, v___x_595_);
lean_ctor_set(v___x_599_, 2, v___x_598_);
lean_ctor_set_float(v___x_599_, sizeof(void*)*3, v___x_596_);
lean_ctor_set_float(v___x_599_, sizeof(void*)*3 + 8, v___x_596_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*3 + 16, v___x_597_);
v___x_600_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__2));
v___x_601_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v_a_573_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
lean_inc(v_ref_571_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_ref_571_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_PersistentArray_push___redArg(v_traces_591_, v___x_602_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_603_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_603_);
lean_ctor_set_uint64(v_reuseFailAlloc_614_, sizeof(void*)*1, v_tid_590_);
v___x_605_ = v_reuseFailAlloc_614_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 4, v___x_605_);
v___x_607_ = v___x_588_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_env_579_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_nextMacroScope_580_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_ngen_581_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_auxDeclNGen_582_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v_cache_583_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_messages_584_);
lean_ctor_set(v_reuseFailAlloc_613_, 7, v_infoState_585_);
lean_ctor_set(v_reuseFailAlloc_613_, 8, v_snapshotTasks_586_);
v___x_607_ = v_reuseFailAlloc_613_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_st_ref_set(v___y_569_, v___x_607_);
v___x_609_ = lean_box(0);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_609_);
v___x_611_ = v___x_575_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___boxed(lean_object* v_cls_618_, lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v_cls_618_, v_msg_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_637_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5));
v___x_638_ = l_Lean_Name_append(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_642_, lean_object* v_rhs_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_options_649_; lean_object* v_ref_650_; lean_object* v_inheritedTraceOptions_651_; lean_object* v___y_653_; uint8_t v_hasTrace_673_; 
v_options_649_ = lean_ctor_get(v_a_646_, 2);
v_ref_650_ = lean_ctor_get(v_a_646_, 5);
v_inheritedTraceOptions_651_ = lean_ctor_get(v_a_646_, 13);
v_hasTrace_673_ = lean_ctor_get_uint8(v_options_649_, sizeof(void*)*1);
if (v_hasTrace_673_ == 0)
{
v___y_653_ = v_a_645_;
goto v___jp_652_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_675_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6);
v___x_676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_651_, v_options_649_, v___x_675_);
if (v___x_676_ == 0)
{
v___y_653_ = v_a_645_;
goto v___jp_652_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc(v_lhs_642_);
v___x_677_ = l_Lean_MessageData_ofLevel(v_lhs_642_);
v___x_678_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
lean_inc(v_rhs_643_);
v___x_680_ = l_Lean_MessageData_ofLevel(v_rhs_643_);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v___x_674_, v___x_681_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_dec_ref(v___x_682_);
v___y_653_ = v_a_645_;
goto v___jp_652_;
}
else
{
lean_dec(v_rhs_643_);
lean_dec(v_lhs_642_);
return v___x_682_;
}
}
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v_mctx_655_; lean_object* v_cache_656_; lean_object* v_zetaDeltaFVarIds_657_; lean_object* v_postponed_658_; lean_object* v_diag_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_672_; 
v___x_654_ = lean_st_ref_take(v___y_653_);
v_mctx_655_ = lean_ctor_get(v___x_654_, 0);
v_cache_656_ = lean_ctor_get(v___x_654_, 1);
v_zetaDeltaFVarIds_657_ = lean_ctor_get(v___x_654_, 2);
v_postponed_658_ = lean_ctor_get(v___x_654_, 3);
v_diag_659_ = lean_ctor_get(v___x_654_, 4);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_672_ == 0)
{
v___x_661_ = v___x_654_;
v_isShared_662_ = v_isSharedCheck_672_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_diag_659_);
lean_inc(v_postponed_658_);
lean_inc(v_zetaDeltaFVarIds_657_);
lean_inc(v_cache_656_);
lean_inc(v_mctx_655_);
lean_dec(v___x_654_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_672_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_defEqCtx_x3f_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_defEqCtx_x3f_663_ = lean_ctor_get(v_a_644_, 4);
lean_inc(v_defEqCtx_x3f_663_);
lean_inc(v_ref_650_);
v___x_664_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_664_, 0, v_ref_650_);
lean_ctor_set(v___x_664_, 1, v_lhs_642_);
lean_ctor_set(v___x_664_, 2, v_rhs_643_);
lean_ctor_set(v___x_664_, 3, v_defEqCtx_x3f_663_);
v___x_665_ = l_Lean_PersistentArray_push___redArg(v_postponed_658_, v___x_664_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 3, v___x_665_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_mctx_655_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_cache_656_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_zetaDeltaFVarIds_657_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_diag_659_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_st_ref_set(v___y_653_, v___x_667_);
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_683_, lean_object* v_rhs_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_683_, v_rhs_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_691_, lean_object* v_mvarId_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
if (lean_obj_tag(v_v_691_) == 5)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v_v_691_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v_v_691_);
v___x_699_ = l_Lean_LMVarId_getLevel(v_a_698_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
v___x_701_ = l_Lean_LMVarId_getLevel(v_mvarId_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_711_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_711_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = lean_nat_dec_lt(v_a_702_, v_a_700_);
lean_dec(v_a_700_);
lean_dec(v_a_702_);
v___x_707_ = lean_box(v___x_706_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_707_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_a_700_);
v_a_712_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_701_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_701_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_mvarId_692_);
v_a_720_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_699_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_699_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v_mvarId_692_);
lean_dec(v_v_691_);
v___x_728_ = 0;
v___x_729_ = lean_box(v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_731_, lean_object* v_mvarId_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_731_, v_mvarId_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_739_, lean_object* v_v_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___y_747_; lean_object* v___y_776_; lean_object* v___y_777_; 
switch(lean_obj_tag(v_u_739_))
{
case 5:
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v_u_739_, 0);
lean_inc(v_a_819_);
v___x_820_ = l_Lean_LMVarId_isReadOnly(v_a_819_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_901_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_901_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_901_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_901_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = lean_unbox(v_a_821_);
lean_dec(v_a_821_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_del_object(v___x_823_);
lean_inc(v_a_819_);
lean_inc(v_v_740_);
v___x_826_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_740_, v_a_819_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_887_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_887_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_887_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_887_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v___y_838_; uint8_t v___x_859_; 
v___x_859_ = lean_unbox(v_a_827_);
lean_dec(v_a_827_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; 
v___x_860_ = l_Lean_Level_occurs(v_u_739_, v_v_740_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_829_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec_ref(v_a_741_);
v___x_861_ = l_Lean_Level_mvarId_x21(v_u_739_);
lean_dec_ref(v_u_739_);
v___x_862_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_861_, v_v_740_, v_a_742_);
lean_dec(v_a_742_);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_862_, 0);
lean_dec(v_unused_872_);
v___x_864_ = v___x_862_;
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
else
{
lean_dec(v___x_862_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = 1;
v___x_867_ = lean_box(v___x_866_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Level_isMax(v_v_740_);
if (v___x_873_ == 0)
{
v___y_838_ = v___x_873_;
goto v___jp_837_;
}
else
{
uint8_t v___x_874_; 
v___x_874_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_739_, v_v_740_);
if (v___x_874_ == 0)
{
v___y_838_ = v___x_873_;
goto v___jp_837_;
}
else
{
lean_dec_ref(v_u_739_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
goto v___jp_831_;
}
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_829_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec_ref(v_a_741_);
v___x_875_ = l_Lean_Level_mvarId_x21(v_v_740_);
lean_dec(v_v_740_);
v___x_876_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_875_, v_u_739_, v_a_742_);
lean_dec(v_a_742_);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_876_, 0);
lean_dec(v_unused_886_);
v___x_878_ = v___x_876_;
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
else
{
lean_dec(v___x_876_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = 1;
v___x_881_ = lean_box(v___x_880_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
v___jp_831_:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = 2;
v___x_833_ = lean_box(v___x_832_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_833_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
v___jp_837_:
{
if (v___y_838_ == 0)
{
lean_dec_ref(v_u_739_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
goto v___jp_831_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_del_object(v___x_829_);
v___x_839_ = l_Lean_Level_mvarId_x21(v_u_739_);
lean_dec_ref(v_u_739_);
v___x_840_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_839_, v_v_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_850_);
v___x_842_ = v___x_840_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_dec(v___x_840_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = 1;
v___x_845_ = lean_box(v___x_844_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_840_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_840_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_u_739_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
v_a_888_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_826_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_826_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec_ref(v_u_739_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
v___x_896_ = 2;
v___x_897_ = lean_box(v___x_896_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_897_);
v___x_899_ = v___x_823_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_u_739_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
v_a_902_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_820_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_820_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_740_))
{
case 5:
{
lean_dec_ref(v_v_740_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
goto v___jp_767_;
}
case 2:
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v_v_740_, 0);
lean_inc(v_a_910_);
v_a_911_ = lean_ctor_get(v_v_740_, 1);
lean_inc(v_a_911_);
lean_dec_ref(v_v_740_);
lean_inc(v_a_744_);
lean_inc_ref(v_a_743_);
lean_inc(v_a_742_);
lean_inc_ref(v_a_741_);
v___x_912_ = lean_is_level_def_eq(v_u_739_, v_a_910_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
v___x_914_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
if (v___x_914_ == 0)
{
lean_dec(v_a_911_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
v___y_747_ = v___x_912_;
goto v___jp_746_;
}
else
{
lean_object* v___x_915_; 
lean_dec_ref(v___x_912_);
v___x_915_ = lean_is_level_def_eq(v_u_739_, v_a_911_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
v___y_747_ = v___x_915_;
goto v___jp_746_;
}
}
else
{
lean_dec(v_a_911_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
v___y_747_ = v___x_912_;
goto v___jp_746_;
}
}
case 3:
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v_v_740_, 1);
lean_inc(v_a_916_);
lean_dec_ref(v_v_740_);
v___x_917_ = lean_is_level_def_eq(v_u_739_, v_a_916_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_928_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_928_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_922_ = lean_unbox(v_a_918_);
lean_dec(v_a_918_);
v___x_923_ = l_Bool_toLBool(v___x_922_);
v___x_924_ = lean_box(v___x_923_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_924_);
v___x_926_ = v___x_920_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_917_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_917_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
case 1:
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_v_740_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
v___x_937_ = 0;
v___x_938_ = lean_box(v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
default: 
{
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
v___y_776_ = v_a_741_;
v___y_777_ = v_a_742_;
goto v___jp_775_;
}
}
}
case 1:
{
lean_object* v_a_940_; uint8_t v___y_942_; 
v_a_940_ = lean_ctor_get(v_u_739_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v_u_739_);
if (lean_obj_tag(v_v_740_) == 5)
{
lean_dec_ref(v_v_740_);
lean_dec(v_a_940_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
goto v___jp_767_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Level_isParam(v_v_740_);
if (v___x_986_ == 0)
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_Level_isMVar(v_a_940_);
if (v___x_987_ == 0)
{
v___y_942_ = v___x_987_;
goto v___jp_941_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_Level_occurs(v_a_940_, v_v_740_);
v___y_942_ = v___x_988_;
goto v___jp_941_;
}
}
else
{
uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_a_940_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
v___x_989_ = 0;
v___x_990_ = lean_box(v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
v___jp_941_:
{
if (v___y_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_decLevel_x3f(v_v_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_974_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_974_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_974_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_974_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
if (lean_obj_tag(v_a_944_) == 0)
{
uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec(v_a_940_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
v___x_948_ = 2;
v___x_949_ = lean_box(v___x_948_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v_val_953_; lean_object* v___x_954_; 
lean_del_object(v___x_946_);
v_val_953_ = lean_ctor_get(v_a_944_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v_a_944_);
v___x_954_ = lean_is_level_def_eq(v_a_940_, v_val_953_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_965_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_959_ = lean_unbox(v_a_955_);
lean_dec(v_a_955_);
v___x_960_ = l_Bool_toLBool(v___x_959_);
v___x_961_ = lean_box(v___x_960_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_961_);
v___x_963_ = v___x_957_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_954_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_954_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_940_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
v_a_975_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_943_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_943_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec(v_a_940_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_v_740_);
v___x_983_ = 2;
v___x_984_ = lean_box(v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
default: 
{
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
if (lean_obj_tag(v_v_740_) == 5)
{
lean_dec_ref(v_v_740_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_u_739_);
goto v___jp_767_;
}
else
{
v___y_776_ = v_a_741_;
v___y_777_ = v_a_742_;
goto v___jp_775_;
}
}
}
v___jp_746_:
{
if (lean_obj_tag(v___y_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_758_; 
v_a_748_ = lean_ctor_get(v___y_747_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___y_747_);
if (v_isSharedCheck_758_ == 0)
{
v___x_750_ = v___y_747_;
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___y_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
uint8_t v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_752_ = lean_unbox(v_a_748_);
lean_dec(v_a_748_);
v___x_753_ = l_Bool_toLBool(v___x_752_);
v___x_754_ = lean_box(v___x_753_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___y_747_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___y_747_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___y_747_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___y_747_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
v___jp_767_:
{
uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = 2;
v___x_769_ = lean_box(v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
v___jp_771_:
{
uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = 2;
v___x_773_ = lean_box(v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
v___jp_775_:
{
uint8_t v_univApprox_778_; 
v_univApprox_778_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*7 + 1);
lean_dec_ref(v___y_776_);
if (v_univApprox_778_ == 0)
{
lean_dec(v___y_777_);
lean_dec(v_v_740_);
lean_dec(v_u_739_);
goto v___jp_771_;
}
else
{
lean_object* v___x_779_; 
lean_inc(v_v_740_);
lean_inc(v_u_739_);
v___x_779_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_739_, v_v_740_, v___y_777_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_810_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_810_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
uint8_t v___x_784_; 
v___x_784_ = lean_unbox(v_a_780_);
lean_dec(v_a_780_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_del_object(v___x_782_);
v___x_785_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_739_, v_v_740_, v___y_777_);
lean_dec(v___y_777_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_796_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_796_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
if (v___x_790_ == 0)
{
lean_del_object(v___x_788_);
goto v___jp_771_;
}
else
{
uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = 1;
v___x_792_ = lean_box(v___x_791_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_792_);
v___x_794_ = v___x_788_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_785_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_785_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v___y_777_);
lean_dec(v_v_740_);
lean_dec(v_u_739_);
v___x_805_ = 1;
v___x_806_ = lean_box(v___x_805_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_806_);
v___x_808_ = v___x_782_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v___y_777_);
lean_dec(v_v_740_);
lean_dec(v_u_739_);
v_a_811_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_779_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_779_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_992_, lean_object* v_v_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_992_, v_v_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v_mctx_1004_; lean_object* v___x_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1008_; lean_object* v_cache_1009_; lean_object* v_zetaDeltaFVarIds_1010_; lean_object* v_postponed_1011_; lean_object* v_diag_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1021_; 
v___x_1003_ = lean_st_ref_get(v___y_1001_);
v_mctx_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_mctx_1004_);
lean_dec(v___x_1003_);
v___x_1005_ = lean_instantiate_level_mvars(v_mctx_1004_, v_l_1000_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_snd_1007_);
lean_dec_ref(v___x_1005_);
v___x_1008_ = lean_st_ref_take(v___y_1001_);
v_cache_1009_ = lean_ctor_get(v___x_1008_, 1);
v_zetaDeltaFVarIds_1010_ = lean_ctor_get(v___x_1008_, 2);
v_postponed_1011_ = lean_ctor_get(v___x_1008_, 3);
v_diag_1012_ = lean_ctor_get(v___x_1008_, 4);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1008_, 0);
lean_dec(v_unused_1022_);
v___x_1014_ = v___x_1008_;
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_diag_1012_);
lean_inc(v_postponed_1011_);
lean_inc(v_zetaDeltaFVarIds_1010_);
lean_inc(v_cache_1009_);
lean_dec(v___x_1008_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_fst_1006_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_fst_1006_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_cache_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_zetaDeltaFVarIds_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_postponed_1011_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_diag_1012_);
v___x_1017_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_st_ref_set(v___y_1001_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_snd_1007_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1023_, v___y_1024_);
lean_dec(v___y_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1027_, v___y_1029_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_unsigned_to_nat(32u);
v___x_1042_ = lean_mk_empty_array_with_capacity(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1044_ = ((size_t)5ULL);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_unsigned_to_nat(32u);
v___x_1047_ = lean_mk_empty_array_with_capacity(v___x_1046_);
v___x_1048_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1049_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_1045_);
lean_ctor_set(v___x_1049_, 3, v___x_1045_);
lean_ctor_set_usize(v___x_1049_, 4, v___x_1044_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_traceState_1053_; lean_object* v_traces_1054_; lean_object* v___x_1055_; lean_object* v_traceState_1056_; lean_object* v_env_1057_; lean_object* v_nextMacroScope_1058_; lean_object* v_ngen_1059_; lean_object* v_auxDeclNGen_1060_; lean_object* v_cache_1061_; lean_object* v_messages_1062_; lean_object* v_infoState_1063_; lean_object* v_snapshotTasks_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1083_; 
v___x_1052_ = lean_st_ref_get(v___y_1050_);
v_traceState_1053_ = lean_ctor_get(v___x_1052_, 4);
lean_inc_ref(v_traceState_1053_);
lean_dec(v___x_1052_);
v_traces_1054_ = lean_ctor_get(v_traceState_1053_, 0);
lean_inc_ref(v_traces_1054_);
lean_dec_ref(v_traceState_1053_);
v___x_1055_ = lean_st_ref_take(v___y_1050_);
v_traceState_1056_ = lean_ctor_get(v___x_1055_, 4);
v_env_1057_ = lean_ctor_get(v___x_1055_, 0);
v_nextMacroScope_1058_ = lean_ctor_get(v___x_1055_, 1);
v_ngen_1059_ = lean_ctor_get(v___x_1055_, 2);
v_auxDeclNGen_1060_ = lean_ctor_get(v___x_1055_, 3);
v_cache_1061_ = lean_ctor_get(v___x_1055_, 5);
v_messages_1062_ = lean_ctor_get(v___x_1055_, 6);
v_infoState_1063_ = lean_ctor_get(v___x_1055_, 7);
v_snapshotTasks_1064_ = lean_ctor_get(v___x_1055_, 8);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1066_ = v___x_1055_;
v_isShared_1067_ = v_isSharedCheck_1083_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snapshotTasks_1064_);
lean_inc(v_infoState_1063_);
lean_inc(v_messages_1062_);
lean_inc(v_cache_1061_);
lean_inc(v_traceState_1056_);
lean_inc(v_auxDeclNGen_1060_);
lean_inc(v_ngen_1059_);
lean_inc(v_nextMacroScope_1058_);
lean_inc(v_env_1057_);
lean_dec(v___x_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1083_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint64_t v_tid_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1081_; 
v_tid_1068_ = lean_ctor_get_uint64(v_traceState_1056_, sizeof(void*)*1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_traceState_1056_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_traceState_1056_, 0);
lean_dec(v_unused_1082_);
v___x_1070_ = v_traceState_1056_;
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v_traceState_1056_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1072_);
lean_ctor_set_uint64(v_reuseFailAlloc_1080_, sizeof(void*)*1, v_tid_1068_);
v___x_1074_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 4, v___x_1074_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_env_1057_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_nextMacroScope_1058_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_ngen_1059_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_auxDeclNGen_1060_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_cache_1061_);
lean_ctor_set(v_reuseFailAlloc_1079_, 6, v_messages_1062_);
lean_ctor_set(v_reuseFailAlloc_1079_, 7, v_infoState_1063_);
lean_ctor_set(v_reuseFailAlloc_1079_, 8, v_snapshotTasks_1064_);
v___x_1076_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_st_ref_set(v___y_1050_, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_traces_1054_);
return v___x_1078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1084_);
lean_dec(v___y_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1098_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_opts_1099_, lean_object* v_opt_1100_){
_start:
{
lean_object* v_name_1101_; lean_object* v_defValue_1102_; lean_object* v_map_1103_; lean_object* v___x_1104_; 
v_name_1101_ = lean_ctor_get(v_opt_1100_, 0);
v_defValue_1102_ = lean_ctor_get(v_opt_1100_, 1);
v_map_1103_ = lean_ctor_get(v_opts_1099_, 0);
v___x_1104_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1103_, v_name_1101_);
if (lean_obj_tag(v___x_1104_) == 0)
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_unbox(v_defValue_1102_);
return v___x_1105_;
}
else
{
lean_object* v_val_1106_; 
v_val_1106_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v___x_1104_);
if (lean_obj_tag(v_val_1106_) == 1)
{
uint8_t v_v_1107_; 
v_v_1107_ = lean_ctor_get_uint8(v_val_1106_, 0);
lean_dec_ref(v_val_1106_);
return v_v_1107_;
}
else
{
uint8_t v___x_1108_; 
lean_dec(v_val_1106_);
v___x_1108_ = lean_unbox(v_defValue_1102_);
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_opts_1109_, lean_object* v_opt_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_opts_1109_, v_opt_1110_);
lean_dec_ref(v_opt_1110_);
lean_dec_ref(v_opts_1109_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1113_, lean_object* v_lhs_1114_, lean_object* v_rhs_1115_, lean_object* v___x_1116_, lean_object* v___x_1117_, uint8_t v___x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___y_1151_; 
if (v___x_1113_ == 0)
{
lean_object* v___x_1188_; lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
lean_inc(v_lhs_1114_);
v___x_1188_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1114_, v___y_1120_);
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___x_1188_);
lean_inc(v_rhs_1115_);
v___x_1190_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1115_, v___y_1120_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = l_Lean_Level_normalize(v_a_1189_);
lean_dec(v_a_1189_);
v___x_1193_ = l_Lean_Level_normalize(v_a_1191_);
lean_dec(v_a_1191_);
v___x_1194_ = lean_level_eq(v_lhs_1114_, v___x_1192_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
lean_inc(v___y_1122_);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
v___x_1195_ = lean_is_level_def_eq(v___x_1192_, v___x_1193_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1195_;
}
else
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_level_eq(v_rhs_1115_, v___x_1193_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
lean_inc(v___y_1122_);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
v___x_1197_ = lean_is_level_def_eq(v___x_1192_, v___x_1193_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; 
lean_dec(v___x_1193_);
lean_dec(v___x_1192_);
lean_inc(v___y_1122_);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
lean_inc(v_rhs_1115_);
lean_inc(v_lhs_1114_);
v___x_1198_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1114_, v_rhs_1115_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1240_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1240_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1240_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
uint8_t v___x_1203_; uint8_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1203_ = 2;
v___x_1204_ = lean_unbox(v_a_1199_);
v___x_1205_ = l_Lean_instBEqLBool_beq(v___x_1204_, v___x_1203_);
if (v___x_1205_ == 0)
{
uint8_t v___x_1206_; uint8_t v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v___x_1206_ = 1;
v___x_1207_ = lean_unbox(v_a_1199_);
lean_dec(v_a_1199_);
v___x_1208_ = l_Lean_instBEqLBool_beq(v___x_1207_, v___x_1206_);
v___x_1209_ = lean_box(v___x_1208_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1209_);
v___x_1211_ = v___x_1201_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
else
{
lean_object* v___x_1213_; 
lean_del_object(v___x_1201_);
lean_dec(v_a_1199_);
lean_inc(v___y_1122_);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
lean_inc(v_lhs_1114_);
lean_inc(v_rhs_1115_);
v___x_1213_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1115_, v_lhs_1114_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1231_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
uint8_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_unbox(v_a_1214_);
v___x_1219_ = l_Lean_instBEqLBool_beq(v___x_1218_, v___x_1203_);
if (v___x_1219_ == 0)
{
uint8_t v___x_1220_; uint8_t v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v___x_1220_ = 1;
v___x_1221_ = lean_unbox(v_a_1214_);
lean_dec(v_a_1214_);
v___x_1222_ = l_Lean_instBEqLBool_beq(v___x_1221_, v___x_1220_);
v___x_1223_ = lean_box(v___x_1222_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1223_);
v___x_1225_ = v___x_1216_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
else
{
lean_object* v___x_1227_; 
lean_del_object(v___x_1216_);
lean_dec(v_a_1214_);
lean_inc(v_lhs_1114_);
v___x_1227_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1114_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; uint8_t v___x_1229_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
v___x_1229_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v___x_1227_);
lean_inc(v_rhs_1115_);
v___x_1230_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1115_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
v___y_1151_ = v___x_1230_;
goto v___jp_1150_;
}
else
{
v___y_1151_ = v___x_1227_;
goto v___jp_1150_;
}
}
else
{
v___y_1151_ = v___x_1227_;
goto v___jp_1150_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v_a_1232_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1213_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1213_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v_a_1241_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1198_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1198_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
v___x_1249_ = l_Lean_Level_getOffset(v_lhs_1114_);
lean_dec(v_lhs_1114_);
v___x_1250_ = l_Lean_Level_getOffset(v_rhs_1115_);
lean_dec(v_rhs_1115_);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
v___jp_1124_:
{
lean_object* v_options_1125_; uint8_t v_hasTrace_1126_; 
v_options_1125_ = lean_ctor_get(v___y_1121_, 2);
v_hasTrace_1126_ = lean_ctor_get_uint8(v_options_1125_, sizeof(void*)*1);
if (v_hasTrace_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v___x_1127_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1127_;
}
else
{
lean_object* v_inheritedTraceOptions_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_inheritedTraceOptions_1128_ = lean_ctor_get(v___y_1121_, 13);
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2));
v___x_1130_ = l_Lean_Name_mkStr3(v___x_1116_, v___x_1117_, v___x_1129_);
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5));
lean_inc(v___x_1130_);
v___x_1132_ = l_Lean_Name_append(v___x_1131_, v___x_1130_);
v___x_1133_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1128_, v_options_1125_, v___x_1132_);
lean_dec(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1130_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v___x_1134_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1135_ = l_Lean_MessageData_ofLevel(v_lhs_1114_);
v___x_1136_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_ofLevel(v_rhs_1115_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v___x_1130_, v___x_1139_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_1140_);
v___x_1141_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1141_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
v___jp_1150_:
{
if (lean_obj_tag(v___y_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1187_; 
v_a_1152_ = lean_ctor_get(v___y_1151_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___y_1151_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1154_ = v___y_1151_;
v_isShared_1155_ = v_isSharedCheck_1187_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___y_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1187_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_unbox(v_a_1152_);
lean_dec(v_a_1152_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; uint8_t v_isDefEqStuckEx_1158_; 
v___x_1157_ = l_Lean_Meta_Context_config(v___y_1119_);
v_isDefEqStuckEx_1158_ = lean_ctor_get_uint8(v___x_1157_, 4);
lean_dec_ref(v___x_1157_);
if (v_isDefEqStuckEx_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v___x_1159_ = lean_box(v_isDefEqStuckEx_1158_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1159_);
v___x_1161_ = v___x_1154_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = l_Lean_Level_isMVar(v_lhs_1114_);
if (v___x_1163_ == 0)
{
uint8_t v___x_1164_; 
v___x_1164_ = l_Lean_Level_isMVar(v_rhs_1115_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
v___x_1165_ = lean_box(v___x_1164_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1165_);
v___x_1167_ = v___x_1154_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
else
{
lean_del_object(v___x_1154_);
goto v___jp_1124_;
}
}
else
{
lean_del_object(v___x_1154_);
goto v___jp_1124_;
}
}
}
else
{
lean_object* v___x_1169_; 
lean_del_object(v___x_1154_);
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
v___x_1169_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1114_, v_rhs_1115_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1177_; 
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v___x_1169_, 0);
lean_dec(v_unused_1178_);
v___x_1171_ = v___x_1169_;
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
else
{
lean_dec(v___x_1169_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(v___x_1118_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_a_1179_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1169_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1169_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1117_);
lean_dec_ref(v___x_1116_);
lean_dec(v_rhs_1115_);
lean_dec(v_lhs_1114_);
return v___y_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1254_, lean_object* v_lhs_1255_, lean_object* v_rhs_1256_, lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_12632__boxed_1265_; uint8_t v___x_12635__boxed_1266_; lean_object* v_res_1267_; 
v___x_12632__boxed_1265_ = lean_unbox(v___x_1254_);
v___x_12635__boxed_1266_ = lean_unbox(v___x_1259_);
v_res_1267_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_12632__boxed_1265_, v_lhs_1255_, v_rhs_1256_, v___x_1257_, v___x_1258_, v___x_12635__boxed_1266_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(lean_object* v_lhs_1268_, lean_object* v_rhs_1269_, lean_object* v_x_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1276_ = l_Lean_MessageData_ofLevel(v_lhs_1268_);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_MessageData_ofLevel(v_rhs_1269_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object* v_lhs_1282_, lean_object* v_rhs_1283_, lean_object* v_x_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(v_lhs_1282_, v_rhs_1283_, v_x_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v_x_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg(lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v_x_1291_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v_x_1291_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v_x_1291_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 1);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v_x_1291_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v_x_1291_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v_x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 0);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg___boxed(lean_object* v_x_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg(v_x_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__3(lean_object* v_e_1312_){
_start:
{
if (lean_obj_tag(v_e_1312_) == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = 2;
return v___x_1313_;
}
else
{
lean_object* v_a_1314_; uint8_t v___x_1315_; 
v_a_1314_ = lean_ctor_get(v_e_1312_, 0);
v___x_1315_ = lean_unbox(v_a_1314_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
v___x_1316_ = 1;
return v___x_1316_;
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = 0;
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__3___boxed(lean_object* v_e_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__3(v_e_1318_);
lean_dec_ref(v_e_1318_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4_spec__5(size_t v_sz_1321_, size_t v_i_1322_, lean_object* v_bs_1323_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_lt(v_i_1322_, v_sz_1321_);
if (v___x_1324_ == 0)
{
return v_bs_1323_;
}
else
{
lean_object* v_v_1325_; lean_object* v_msg_1326_; lean_object* v___x_1327_; lean_object* v_bs_x27_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v_v_1325_ = lean_array_uget_borrowed(v_bs_1323_, v_i_1322_);
v_msg_1326_ = lean_ctor_get(v_v_1325_, 1);
lean_inc_ref(v_msg_1326_);
v___x_1327_ = lean_unsigned_to_nat(0u);
v_bs_x27_1328_ = lean_array_uset(v_bs_1323_, v_i_1322_, v___x_1327_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1322_, v___x_1329_);
v___x_1331_ = lean_array_uset(v_bs_x27_1328_, v_i_1322_, v_msg_1326_);
v_i_1322_ = v___x_1330_;
v_bs_1323_ = v___x_1331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_1333_, lean_object* v_i_1334_, lean_object* v_bs_1335_){
_start:
{
size_t v_sz_boxed_1336_; size_t v_i_boxed_1337_; lean_object* v_res_1338_; 
v_sz_boxed_1336_ = lean_unbox_usize(v_sz_1333_);
lean_dec(v_sz_1333_);
v_i_boxed_1337_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_res_1338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4_spec__5(v_sz_boxed_1336_, v_i_boxed_1337_, v_bs_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4(lean_object* v_oldTraces_1339_, lean_object* v_data_1340_, lean_object* v_ref_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_fileName_1348_; lean_object* v_fileMap_1349_; lean_object* v_options_1350_; lean_object* v_currRecDepth_1351_; lean_object* v_maxRecDepth_1352_; lean_object* v_ref_1353_; lean_object* v_currNamespace_1354_; lean_object* v_openDecls_1355_; lean_object* v_initHeartbeats_1356_; lean_object* v_maxHeartbeats_1357_; lean_object* v_quotContext_1358_; lean_object* v_currMacroScope_1359_; uint8_t v_diag_1360_; lean_object* v_cancelTk_x3f_1361_; uint8_t v_suppressElabErrors_1362_; lean_object* v_inheritedTraceOptions_1363_; lean_object* v___x_1364_; lean_object* v_traceState_1365_; lean_object* v_traces_1366_; lean_object* v_ref_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; size_t v_sz_1370_; size_t v___x_1371_; lean_object* v___x_1372_; lean_object* v_msg_1373_; lean_object* v___x_1374_; lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1412_; 
v_fileName_1348_ = lean_ctor_get(v___y_1345_, 0);
v_fileMap_1349_ = lean_ctor_get(v___y_1345_, 1);
v_options_1350_ = lean_ctor_get(v___y_1345_, 2);
v_currRecDepth_1351_ = lean_ctor_get(v___y_1345_, 3);
v_maxRecDepth_1352_ = lean_ctor_get(v___y_1345_, 4);
v_ref_1353_ = lean_ctor_get(v___y_1345_, 5);
v_currNamespace_1354_ = lean_ctor_get(v___y_1345_, 6);
v_openDecls_1355_ = lean_ctor_get(v___y_1345_, 7);
v_initHeartbeats_1356_ = lean_ctor_get(v___y_1345_, 8);
v_maxHeartbeats_1357_ = lean_ctor_get(v___y_1345_, 9);
v_quotContext_1358_ = lean_ctor_get(v___y_1345_, 10);
v_currMacroScope_1359_ = lean_ctor_get(v___y_1345_, 11);
v_diag_1360_ = lean_ctor_get_uint8(v___y_1345_, sizeof(void*)*14);
v_cancelTk_x3f_1361_ = lean_ctor_get(v___y_1345_, 12);
v_suppressElabErrors_1362_ = lean_ctor_get_uint8(v___y_1345_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1363_ = lean_ctor_get(v___y_1345_, 13);
v___x_1364_ = lean_st_ref_get(v___y_1346_);
v_traceState_1365_ = lean_ctor_get(v___x_1364_, 4);
lean_inc_ref(v_traceState_1365_);
lean_dec(v___x_1364_);
v_traces_1366_ = lean_ctor_get(v_traceState_1365_, 0);
lean_inc_ref(v_traces_1366_);
lean_dec_ref(v_traceState_1365_);
v_ref_1367_ = l_Lean_replaceRef(v_ref_1341_, v_ref_1353_);
lean_inc_ref(v_inheritedTraceOptions_1363_);
lean_inc(v_cancelTk_x3f_1361_);
lean_inc(v_currMacroScope_1359_);
lean_inc(v_quotContext_1358_);
lean_inc(v_maxHeartbeats_1357_);
lean_inc(v_initHeartbeats_1356_);
lean_inc(v_openDecls_1355_);
lean_inc(v_currNamespace_1354_);
lean_inc(v_maxRecDepth_1352_);
lean_inc(v_currRecDepth_1351_);
lean_inc_ref(v_options_1350_);
lean_inc_ref(v_fileMap_1349_);
lean_inc_ref(v_fileName_1348_);
v___x_1368_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1368_, 0, v_fileName_1348_);
lean_ctor_set(v___x_1368_, 1, v_fileMap_1349_);
lean_ctor_set(v___x_1368_, 2, v_options_1350_);
lean_ctor_set(v___x_1368_, 3, v_currRecDepth_1351_);
lean_ctor_set(v___x_1368_, 4, v_maxRecDepth_1352_);
lean_ctor_set(v___x_1368_, 5, v_ref_1367_);
lean_ctor_set(v___x_1368_, 6, v_currNamespace_1354_);
lean_ctor_set(v___x_1368_, 7, v_openDecls_1355_);
lean_ctor_set(v___x_1368_, 8, v_initHeartbeats_1356_);
lean_ctor_set(v___x_1368_, 9, v_maxHeartbeats_1357_);
lean_ctor_set(v___x_1368_, 10, v_quotContext_1358_);
lean_ctor_set(v___x_1368_, 11, v_currMacroScope_1359_);
lean_ctor_set(v___x_1368_, 12, v_cancelTk_x3f_1361_);
lean_ctor_set(v___x_1368_, 13, v_inheritedTraceOptions_1363_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*14, v_diag_1360_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*14 + 1, v_suppressElabErrors_1362_);
v___x_1369_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1366_);
lean_dec_ref(v_traces_1366_);
v_sz_1370_ = lean_array_size(v___x_1369_);
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4_spec__5(v_sz_1370_, v___x_1371_, v___x_1369_);
v_msg_1373_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1373_, 0, v_data_1340_);
lean_ctor_set(v_msg_1373_, 1, v_msg_1342_);
lean_ctor_set(v_msg_1373_, 2, v___x_1372_);
v___x_1374_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(v_msg_1373_, v___y_1343_, v___y_1344_, v___x_1368_, v___y_1346_);
lean_dec_ref(v___x_1368_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1412_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1412_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v_traceState_1380_; lean_object* v_env_1381_; lean_object* v_nextMacroScope_1382_; lean_object* v_ngen_1383_; lean_object* v_auxDeclNGen_1384_; lean_object* v_cache_1385_; lean_object* v_messages_1386_; lean_object* v_infoState_1387_; lean_object* v_snapshotTasks_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1411_; 
v___x_1379_ = lean_st_ref_take(v___y_1346_);
v_traceState_1380_ = lean_ctor_get(v___x_1379_, 4);
v_env_1381_ = lean_ctor_get(v___x_1379_, 0);
v_nextMacroScope_1382_ = lean_ctor_get(v___x_1379_, 1);
v_ngen_1383_ = lean_ctor_get(v___x_1379_, 2);
v_auxDeclNGen_1384_ = lean_ctor_get(v___x_1379_, 3);
v_cache_1385_ = lean_ctor_get(v___x_1379_, 5);
v_messages_1386_ = lean_ctor_get(v___x_1379_, 6);
v_infoState_1387_ = lean_ctor_get(v___x_1379_, 7);
v_snapshotTasks_1388_ = lean_ctor_get(v___x_1379_, 8);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1390_ = v___x_1379_;
v_isShared_1391_ = v_isSharedCheck_1411_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_snapshotTasks_1388_);
lean_inc(v_infoState_1387_);
lean_inc(v_messages_1386_);
lean_inc(v_cache_1385_);
lean_inc(v_traceState_1380_);
lean_inc(v_auxDeclNGen_1384_);
lean_inc(v_ngen_1383_);
lean_inc(v_nextMacroScope_1382_);
lean_inc(v_env_1381_);
lean_dec(v___x_1379_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1411_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
uint64_t v_tid_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1409_; 
v_tid_1392_ = lean_ctor_get_uint64(v_traceState_1380_, sizeof(void*)*1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_traceState_1380_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_traceState_1380_, 0);
lean_dec(v_unused_1410_);
v___x_1394_ = v_traceState_1380_;
v_isShared_1395_ = v_isSharedCheck_1409_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_traceState_1380_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1409_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_ref_1341_);
lean_ctor_set(v___x_1396_, 1, v_a_1375_);
v___x_1397_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1339_, v___x_1396_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1397_);
lean_ctor_set_uint64(v_reuseFailAlloc_1408_, sizeof(void*)*1, v_tid_1392_);
v___x_1399_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 4, v___x_1399_);
v___x_1401_ = v___x_1390_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_env_1381_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_nextMacroScope_1382_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_ngen_1383_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_auxDeclNGen_1384_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1407_, 5, v_cache_1385_);
lean_ctor_set(v_reuseFailAlloc_1407_, 6, v_messages_1386_);
lean_ctor_set(v_reuseFailAlloc_1407_, 7, v_infoState_1387_);
lean_ctor_set(v_reuseFailAlloc_1407_, 8, v_snapshotTasks_1388_);
v___x_1401_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1402_ = lean_st_ref_set(v___y_1346_, v___x_1401_);
v___x_1403_ = lean_box(0);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1403_);
v___x_1405_ = v___x_1377_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4___boxed(lean_object* v_oldTraces_1413_, lean_object* v_data_1414_, lean_object* v_ref_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4(v_oldTraces_1413_, v_data_1414_, v_ref_1415_, v_msg_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6(lean_object* v_opts_1423_, lean_object* v_opt_1424_){
_start:
{
lean_object* v_name_1425_; lean_object* v_defValue_1426_; lean_object* v_map_1427_; lean_object* v___x_1428_; 
v_name_1425_ = lean_ctor_get(v_opt_1424_, 0);
v_defValue_1426_ = lean_ctor_get(v_opt_1424_, 1);
v_map_1427_ = lean_ctor_get(v_opts_1423_, 0);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1427_, v_name_1425_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_inc(v_defValue_1426_);
return v_defValue_1426_;
}
else
{
lean_object* v_val_1429_; 
v_val_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1429_);
lean_dec_ref(v___x_1428_);
if (lean_obj_tag(v_val_1429_) == 3)
{
lean_object* v_v_1430_; 
v_v_1430_ = lean_ctor_get(v_val_1429_, 0);
lean_inc(v_v_1430_);
lean_dec_ref(v_val_1429_);
return v_v_1430_;
}
else
{
lean_dec(v_val_1429_);
lean_inc(v_defValue_1426_);
return v_defValue_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6___boxed(lean_object* v_opts_1431_, lean_object* v_opt_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6(v_opts_1431_, v_opt_1432_);
lean_dec_ref(v_opt_1432_);
lean_dec_ref(v_opts_1431_);
return v_res_1433_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__0));
v___x_1436_ = l_Lean_stringToMessageData(v___x_1435_);
return v___x_1436_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__2));
v___x_1439_ = l_Lean_stringToMessageData(v___x_1438_);
return v___x_1439_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1440_; double v___x_1441_; 
v___x_1440_ = lean_unsigned_to_nat(1000u);
v___x_1441_ = lean_float_of_nat(v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_cls_1442_, uint8_t v_collapsed_1443_, lean_object* v_tag_1444_, lean_object* v_opts_1445_, uint8_t v_clsEnabled_1446_, lean_object* v_oldTraces_1447_, lean_object* v_msg_1448_, lean_object* v_resStartStop_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_fst_1455_; lean_object* v_snd_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1554_; 
v_fst_1455_ = lean_ctor_get(v_resStartStop_1449_, 0);
v_snd_1456_ = lean_ctor_get(v_resStartStop_1449_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_resStartStop_1449_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1458_ = v_resStartStop_1449_;
v_isShared_1459_ = v_isSharedCheck_1554_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_snd_1456_);
lean_inc(v_fst_1455_);
lean_dec(v_resStartStop_1449_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1554_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v_data_1463_; lean_object* v_fst_1474_; lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1553_; 
v_fst_1474_ = lean_ctor_get(v_snd_1456_, 0);
v_snd_1475_ = lean_ctor_get(v_snd_1456_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_snd_1456_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1477_ = v_snd_1456_;
v_isShared_1478_ = v_isSharedCheck_1553_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_inc(v_fst_1474_);
lean_dec(v_snd_1456_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1553_;
goto v_resetjp_1476_;
}
v___jp_1460_:
{
lean_object* v___x_1464_; 
lean_inc(v___y_1462_);
v___x_1464_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__4(v_oldTraces_1447_, v_data_1463_, v___y_1462_, v___y_1461_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref(v___x_1464_);
v___x_1465_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg(v_fst_1455_);
return v___x_1465_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_fst_1455_);
v_a_1466_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; lean_object* v___y_1482_; lean_object* v_a_1483_; uint8_t v___y_1507_; double v___y_1538_; 
v___x_1479_ = l_Lean_trace_profiler;
v___x_1480_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_opts_1445_, v___x_1479_);
if (v___x_1480_ == 0)
{
v___y_1507_ = v___x_1480_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1544_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_opts_1445_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; double v___x_1547_; double v___x_1548_; double v___x_1549_; 
v___x_1545_ = l_Lean_trace_profiler_threshold;
v___x_1546_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6(v_opts_1445_, v___x_1545_);
v___x_1547_ = lean_float_of_nat(v___x_1546_);
v___x_1548_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__4);
v___x_1549_ = lean_float_div(v___x_1547_, v___x_1548_);
v___y_1538_ = v___x_1549_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; double v___x_1552_; 
v___x_1550_ = l_Lean_trace_profiler_threshold;
v___x_1551_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__6(v_opts_1445_, v___x_1550_);
v___x_1552_ = lean_float_of_nat(v___x_1551_);
v___y_1538_ = v___x_1552_;
goto v___jp_1537_;
}
}
v___jp_1481_:
{
uint8_t v_result_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v_result_1484_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__3(v_fst_1455_);
v___x_1485_ = l_Lean_TraceResult_toEmoji(v_result_1484_);
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
v___x_1487_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__1);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 7);
lean_ctor_set(v___x_1477_, 1, v___x_1487_);
lean_ctor_set(v___x_1477_, 0, v___x_1486_);
v___x_1489_ = v___x_1477_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v_m_1491_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 7);
lean_ctor_set(v___x_1458_, 1, v_a_1483_);
lean_ctor_set(v___x_1458_, 0, v___x_1489_);
v_m_1491_ = v___x_1458_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1483_);
v_m_1491_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; double v___x_1494_; lean_object* v_data_1495_; 
v___x_1492_ = lean_box(v_result_1484_);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
v___x_1494_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0);
lean_inc_ref(v_tag_1444_);
lean_inc_ref(v___x_1493_);
lean_inc(v_cls_1442_);
v_data_1495_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1495_, 0, v_cls_1442_);
lean_ctor_set(v_data_1495_, 1, v___x_1493_);
lean_ctor_set(v_data_1495_, 2, v_tag_1444_);
lean_ctor_set_float(v_data_1495_, sizeof(void*)*3, v___x_1494_);
lean_ctor_set_float(v_data_1495_, sizeof(void*)*3 + 8, v___x_1494_);
lean_ctor_set_uint8(v_data_1495_, sizeof(void*)*3 + 16, v_collapsed_1443_);
if (v___x_1480_ == 0)
{
lean_dec_ref(v___x_1493_);
lean_dec(v_snd_1475_);
lean_dec(v_fst_1474_);
lean_dec_ref(v_tag_1444_);
lean_dec(v_cls_1442_);
v___y_1461_ = v_m_1491_;
v___y_1462_ = v___y_1482_;
v_data_1463_ = v_data_1495_;
goto v___jp_1460_;
}
else
{
lean_object* v_data_1496_; double v___x_1497_; double v___x_1498_; 
lean_dec_ref(v_data_1495_);
v_data_1496_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1496_, 0, v_cls_1442_);
lean_ctor_set(v_data_1496_, 1, v___x_1493_);
lean_ctor_set(v_data_1496_, 2, v_tag_1444_);
v___x_1497_ = lean_unbox_float(v_fst_1474_);
lean_dec(v_fst_1474_);
lean_ctor_set_float(v_data_1496_, sizeof(void*)*3, v___x_1497_);
v___x_1498_ = lean_unbox_float(v_snd_1475_);
lean_dec(v_snd_1475_);
lean_ctor_set_float(v_data_1496_, sizeof(void*)*3 + 8, v___x_1498_);
lean_ctor_set_uint8(v_data_1496_, sizeof(void*)*3 + 16, v_collapsed_1443_);
v___y_1461_ = v_m_1491_;
v___y_1462_ = v___y_1482_;
v_data_1463_ = v_data_1496_;
goto v___jp_1460_;
}
}
}
}
v___jp_1501_:
{
lean_object* v_ref_1502_; lean_object* v___x_1503_; 
v_ref_1502_ = lean_ctor_get(v___y_1452_, 5);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v_fst_1455_);
v___x_1503_ = lean_apply_6(v_msg_1448_, v_fst_1455_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, lean_box(0));
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
v___y_1482_ = v_ref_1502_;
v_a_1483_ = v_a_1504_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1505_; 
lean_dec_ref(v___x_1503_);
v___x_1505_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___closed__3);
v___y_1482_ = v_ref_1502_;
v_a_1483_ = v___x_1505_;
goto v___jp_1481_;
}
}
v___jp_1506_:
{
if (v_clsEnabled_1446_ == 0)
{
if (v___y_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v_traceState_1509_; lean_object* v_env_1510_; lean_object* v_nextMacroScope_1511_; lean_object* v_ngen_1512_; lean_object* v_auxDeclNGen_1513_; lean_object* v_cache_1514_; lean_object* v_messages_1515_; lean_object* v_infoState_1516_; lean_object* v_snapshotTasks_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1536_; 
lean_del_object(v___x_1477_);
lean_dec(v_snd_1475_);
lean_dec(v_fst_1474_);
lean_del_object(v___x_1458_);
lean_dec_ref(v_msg_1448_);
lean_dec_ref(v_tag_1444_);
lean_dec(v_cls_1442_);
v___x_1508_ = lean_st_ref_take(v___y_1453_);
v_traceState_1509_ = lean_ctor_get(v___x_1508_, 4);
v_env_1510_ = lean_ctor_get(v___x_1508_, 0);
v_nextMacroScope_1511_ = lean_ctor_get(v___x_1508_, 1);
v_ngen_1512_ = lean_ctor_get(v___x_1508_, 2);
v_auxDeclNGen_1513_ = lean_ctor_get(v___x_1508_, 3);
v_cache_1514_ = lean_ctor_get(v___x_1508_, 5);
v_messages_1515_ = lean_ctor_get(v___x_1508_, 6);
v_infoState_1516_ = lean_ctor_get(v___x_1508_, 7);
v_snapshotTasks_1517_ = lean_ctor_get(v___x_1508_, 8);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1519_ = v___x_1508_;
v_isShared_1520_ = v_isSharedCheck_1536_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snapshotTasks_1517_);
lean_inc(v_infoState_1516_);
lean_inc(v_messages_1515_);
lean_inc(v_cache_1514_);
lean_inc(v_traceState_1509_);
lean_inc(v_auxDeclNGen_1513_);
lean_inc(v_ngen_1512_);
lean_inc(v_nextMacroScope_1511_);
lean_inc(v_env_1510_);
lean_dec(v___x_1508_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1536_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
uint64_t v_tid_1521_; lean_object* v_traces_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1535_; 
v_tid_1521_ = lean_ctor_get_uint64(v_traceState_1509_, sizeof(void*)*1);
v_traces_1522_ = lean_ctor_get(v_traceState_1509_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_traceState_1509_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1524_ = v_traceState_1509_;
v_isShared_1525_ = v_isSharedCheck_1535_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_traces_1522_);
lean_dec(v_traceState_1509_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1535_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1447_, v_traces_1522_);
lean_dec_ref(v_traces_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1526_);
v___x_1528_ = v___x_1524_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1526_);
lean_ctor_set_uint64(v_reuseFailAlloc_1534_, sizeof(void*)*1, v_tid_1521_);
v___x_1528_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 4, v___x_1528_);
v___x_1530_ = v___x_1519_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_env_1510_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_nextMacroScope_1511_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_ngen_1512_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_auxDeclNGen_1513_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1533_, 5, v_cache_1514_);
lean_ctor_set(v_reuseFailAlloc_1533_, 6, v_messages_1515_);
lean_ctor_set(v_reuseFailAlloc_1533_, 7, v_infoState_1516_);
lean_ctor_set(v_reuseFailAlloc_1533_, 8, v_snapshotTasks_1517_);
v___x_1530_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_st_ref_set(v___y_1453_, v___x_1530_);
v___x_1532_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg(v_fst_1455_);
return v___x_1532_;
}
}
}
}
}
else
{
goto v___jp_1501_;
}
}
else
{
goto v___jp_1501_;
}
}
v___jp_1537_:
{
double v___x_1539_; double v___x_1540_; double v___x_1541_; uint8_t v___x_1542_; 
v___x_1539_ = lean_unbox_float(v_snd_1475_);
v___x_1540_ = lean_unbox_float(v_fst_1474_);
v___x_1541_ = lean_float_sub(v___x_1539_, v___x_1540_);
v___x_1542_ = lean_float_decLt(v___y_1538_, v___x_1541_);
v___y_1507_ = v___x_1542_;
goto v___jp_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_cls_1555_, lean_object* v_collapsed_1556_, lean_object* v_tag_1557_, lean_object* v_opts_1558_, lean_object* v_clsEnabled_1559_, lean_object* v_oldTraces_1560_, lean_object* v_msg_1561_, lean_object* v_resStartStop_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_collapsed_boxed_1568_; uint8_t v_clsEnabled_boxed_1569_; lean_object* v_res_1570_; 
v_collapsed_boxed_1568_ = lean_unbox(v_collapsed_1556_);
v_clsEnabled_boxed_1569_ = lean_unbox(v_clsEnabled_1559_);
v_res_1570_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_cls_1555_, v_collapsed_boxed_1568_, v_tag_1557_, v_opts_1558_, v_clsEnabled_boxed_1569_, v_oldTraces_1560_, v_msg_1561_, v_resStartStop_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_opts_1558_);
return v_res_1570_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1571_; double v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(1000000000u);
v___x_1572_ = lean_float_of_nat(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_1577_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5));
v___x_1578_ = l_Lean_Name_append(v___x_1577_, v___x_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; uint8_t v___y_1595_; uint8_t v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v_a_1599_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; uint8_t v___y_1620_; uint8_t v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v_a_1624_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; uint8_t v___y_1640_; uint8_t v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v_lhs_1686_; lean_object* v_rhs_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; 
if (lean_obj_tag(v_x_1579_) == 1)
{
if (lean_obj_tag(v_x_1580_) == 1)
{
lean_object* v_a_1713_; lean_object* v_a_1714_; lean_object* v___x_1715_; 
v_a_1713_ = lean_ctor_get(v_x_1579_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v_x_1579_);
v_a_1714_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v_x_1580_);
v___x_1715_ = lean_is_level_def_eq(v_a_1713_, v_a_1714_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1715_;
}
else
{
v_lhs_1686_ = v_x_1579_;
v_rhs_1687_ = v_x_1580_;
v___y_1688_ = v_a_1581_;
v___y_1689_ = v_a_1582_;
v___y_1690_ = v_a_1583_;
v___y_1691_ = v_a_1584_;
goto v___jp_1685_;
}
}
else
{
v_lhs_1686_ = v_x_1579_;
v_rhs_1687_ = v_x_1580_;
v___y_1688_ = v_a_1581_;
v___y_1689_ = v_a_1582_;
v___y_1690_ = v_a_1583_;
v___y_1691_ = v_a_1584_;
goto v___jp_1685_;
}
v___jp_1586_:
{
lean_object* v___x_1600_; double v___x_1601_; double v___x_1602_; double v___x_1603_; double v___x_1604_; double v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1600_ = lean_io_mono_nanos_now();
v___x_1601_ = lean_float_of_nat(v___y_1587_);
v___x_1602_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1603_ = lean_float_div(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_float_of_nat(v___x_1600_);
v___x_1605_ = lean_float_div(v___x_1604_, v___x_1602_);
v___x_1606_ = lean_box_float(v___x_1603_);
v___x_1607_ = lean_box_float(v___x_1605_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1599_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
lean_inc_ref(v___y_1598_);
lean_inc(v___y_1597_);
v___x_1610_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1597_, v___y_1596_, v___y_1598_, v___y_1589_, v___y_1595_, v___y_1593_, v___y_1588_, v___x_1609_, v___y_1594_, v___y_1591_, v___y_1590_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___y_1589_);
return v___x_1610_;
}
v___jp_1611_:
{
lean_object* v___x_1625_; double v___x_1626_; double v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1625_ = lean_io_get_num_heartbeats();
v___x_1626_ = lean_float_of_nat(v___y_1613_);
v___x_1627_ = lean_float_of_nat(v___x_1625_);
v___x_1628_ = lean_box_float(v___x_1626_);
v___x_1629_ = lean_box_float(v___x_1627_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_a_1624_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
v___x_1632_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1622_, v___y_1621_, v___y_1623_, v___y_1614_, v___y_1620_, v___y_1618_, v___y_1612_, v___x_1631_, v___y_1619_, v___y_1616_, v___y_1615_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v___y_1614_);
return v___x_1632_;
}
v___jp_1633_:
{
lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1639_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1648_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1636_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_io_mono_nanos_now();
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1637_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1642_);
v___x_1650_ = lean_apply_5(v___y_1635_, v___y_1642_, v___y_1638_, v___y_1637_, v___y_1639_, lean_box(0));
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 1);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
v___y_1587_ = v___x_1649_;
v___y_1588_ = v___y_1634_;
v___y_1589_ = v___y_1636_;
v___y_1590_ = v___y_1637_;
v___y_1591_ = v___y_1638_;
v___y_1592_ = v___y_1639_;
v___y_1593_ = v_a_1646_;
v___y_1594_ = v___y_1642_;
v___y_1595_ = v___y_1641_;
v___y_1596_ = v___y_1640_;
v___y_1597_ = v___y_1643_;
v___y_1598_ = v___y_1644_;
v_a_1599_ = v___x_1656_;
goto v___jp_1586_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1650_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1650_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 0);
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
v___y_1587_ = v___x_1649_;
v___y_1588_ = v___y_1634_;
v___y_1589_ = v___y_1636_;
v___y_1590_ = v___y_1637_;
v___y_1591_ = v___y_1638_;
v___y_1592_ = v___y_1639_;
v___y_1593_ = v_a_1646_;
v___y_1594_ = v___y_1642_;
v___y_1595_ = v___y_1641_;
v___y_1596_ = v___y_1640_;
v___y_1597_ = v___y_1643_;
v___y_1598_ = v___y_1644_;
v_a_1599_ = v___x_1664_;
goto v___jp_1586_;
}
}
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1637_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1642_);
v___x_1668_ = lean_apply_5(v___y_1635_, v___y_1642_, v___y_1638_, v___y_1637_, v___y_1639_, lean_box(0));
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 1);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
v___y_1612_ = v___y_1634_;
v___y_1613_ = v___x_1667_;
v___y_1614_ = v___y_1636_;
v___y_1615_ = v___y_1637_;
v___y_1616_ = v___y_1638_;
v___y_1617_ = v___y_1639_;
v___y_1618_ = v_a_1646_;
v___y_1619_ = v___y_1642_;
v___y_1620_ = v___y_1641_;
v___y_1621_ = v___y_1640_;
v___y_1622_ = v___y_1643_;
v___y_1623_ = v___y_1644_;
v_a_1624_ = v___x_1674_;
goto v___jp_1611_;
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1668_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1668_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 0);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v___y_1612_ = v___y_1634_;
v___y_1613_ = v___x_1667_;
v___y_1614_ = v___y_1636_;
v___y_1615_ = v___y_1637_;
v___y_1616_ = v___y_1638_;
v___y_1617_ = v___y_1639_;
v___y_1618_ = v_a_1646_;
v___y_1619_ = v___y_1642_;
v___y_1620_ = v___y_1641_;
v___y_1621_ = v___y_1640_;
v___y_1622_ = v___y_1643_;
v___y_1623_ = v___y_1644_;
v_a_1624_ = v___x_1682_;
goto v___jp_1611_;
}
}
}
}
}
v___jp_1685_:
{
lean_object* v_options_1692_; lean_object* v_inheritedTraceOptions_1693_; uint8_t v_hasTrace_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___y_1703_; 
v_options_1692_ = lean_ctor_get(v___y_1690_, 2);
v_inheritedTraceOptions_1693_ = lean_ctor_get(v___y_1690_, 13);
v_hasTrace_1694_ = lean_ctor_get_uint8(v_options_1692_, sizeof(void*)*1);
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1696_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_1697_ = l_Lean_Level_getLevelOffset(v_lhs_1686_);
v___x_1698_ = l_Lean_Level_getLevelOffset(v_rhs_1687_);
v___x_1699_ = lean_level_eq(v___x_1697_, v___x_1698_);
lean_dec(v___x_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = 1;
v___x_1701_ = lean_box(v___x_1699_);
v___x_1702_ = lean_box(v___x_1700_);
lean_inc(v_rhs_1687_);
lean_inc(v_lhs_1686_);
v___y_1703_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1703_, 0, v___x_1701_);
lean_closure_set(v___y_1703_, 1, v_lhs_1686_);
lean_closure_set(v___y_1703_, 2, v_rhs_1687_);
lean_closure_set(v___y_1703_, 3, v___x_1695_);
lean_closure_set(v___y_1703_, 4, v___x_1696_);
lean_closure_set(v___y_1703_, 5, v___x_1702_);
if (v_hasTrace_1694_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v___y_1703_);
v___x_1704_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1699_, v_lhs_1686_, v_rhs_1687_, v___x_1695_, v___x_1696_, v___x_1700_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v___x_1704_;
}
else
{
lean_object* v___f_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
lean_inc(v_rhs_1687_);
lean_inc(v_lhs_1686_);
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1705_, 0, v_lhs_1686_);
lean_closure_set(v___f_1705_, 1, v_rhs_1687_);
v___x_1706_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_1707_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1));
v___x_1708_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1693_, v_options_1692_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = l_Lean_trace_profiler;
v___x_1711_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_options_1692_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec_ref(v___f_1705_);
lean_dec_ref(v___y_1703_);
v___x_1712_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1699_, v_lhs_1686_, v_rhs_1687_, v___x_1695_, v___x_1696_, v___x_1700_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v___x_1712_;
}
else
{
lean_inc_ref(v_options_1692_);
lean_dec(v_rhs_1687_);
lean_dec(v_lhs_1686_);
v___y_1634_ = v___f_1705_;
v___y_1635_ = v___y_1703_;
v___y_1636_ = v_options_1692_;
v___y_1637_ = v___y_1690_;
v___y_1638_ = v___y_1689_;
v___y_1639_ = v___y_1691_;
v___y_1640_ = v___x_1700_;
v___y_1641_ = v___x_1709_;
v___y_1642_ = v___y_1688_;
v___y_1643_ = v___x_1706_;
v___y_1644_ = v___x_1707_;
goto v___jp_1633_;
}
}
else
{
lean_inc_ref(v_options_1692_);
lean_dec(v_rhs_1687_);
lean_dec(v_lhs_1686_);
v___y_1634_ = v___f_1705_;
v___y_1635_ = v___y_1703_;
v___y_1636_ = v_options_1692_;
v___y_1637_ = v___y_1690_;
v___y_1638_ = v___y_1689_;
v___y_1639_ = v___y_1691_;
v___y_1640_ = v___x_1700_;
v___y_1641_ = v___x_1709_;
v___y_1642_ = v___y_1688_;
v___y_1643_ = v___x_1706_;
v___y_1644_ = v___x_1707_;
goto v___jp_1633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = lean_is_level_def_eq(v_x_1716_, v_x_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5(lean_object* v_00_u03b1_1724_, lean_object* v_x_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___redArg(v_x_1725_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_x_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3_spec__5(v_00_u03b1_1732_, v_x_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_1797_ = 0;
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_1799_ = l_Lean_registerTraceClass(v___x_1796_, v___x_1797_, v___x_1798_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v___x_1799_);
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_1801_ = 1;
v___x_1802_ = l_Lean_registerTraceClass(v___x_1800_, v___x_1801_, v___x_1798_);
return v___x_1802_;
}
else
{
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_1804_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LevelDefEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasAssignableMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_LevelDefEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LevelDefEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasAssignableMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LevelDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_LevelDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_LevelDefEq(builtin);
}
#ifdef __cplusplus
}
#endif
