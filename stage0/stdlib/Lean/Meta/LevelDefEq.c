// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: public import Lean.Util.CollectMVars public import Lean.Meta.DecLevel
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__1 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__2 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__3 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__4 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.isLevelMVarAssignable"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__1_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unknown universe metavariable "};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__2 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_isLevelDefEqAuxImpl___closed__0;
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__1 = (const lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_value;
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__2;
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_725__boxed_204_; size_t v_x_726__boxed_205_; lean_object* v_res_206_; 
v_x_725__boxed_204_ = lean_unbox_usize(v_x_200_);
lean_dec(v_x_200_);
v_x_726__boxed_205_ = lean_unbox_usize(v_x_201_);
lean_dec(v_x_201_);
v_res_206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_199_, v_x_725__boxed_204_, v_x_726__boxed_205_, v_x_202_, v_x_203_);
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
lean_object* v___x_218_; lean_object* v_mctx_219_; lean_object* v_cache_220_; lean_object* v_zetaDeltaFVarIds_221_; lean_object* v_postponed_222_; lean_object* v_diag_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_250_; 
v___x_218_ = lean_st_ref_take(v___y_216_);
v_mctx_219_ = lean_ctor_get(v___x_218_, 0);
v_cache_220_ = lean_ctor_get(v___x_218_, 1);
v_zetaDeltaFVarIds_221_ = lean_ctor_get(v___x_218_, 2);
v_postponed_222_ = lean_ctor_get(v___x_218_, 3);
v_diag_223_ = lean_ctor_get(v___x_218_, 4);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_250_ == 0)
{
v___x_225_ = v___x_218_;
v_isShared_226_ = v_isSharedCheck_250_;
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
v_isShared_226_ = v_isSharedCheck_250_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_depth_227_; lean_object* v_levelAssignDepth_228_; lean_object* v_mvarCounter_229_; lean_object* v_lDepth_230_; lean_object* v_decls_231_; lean_object* v_userNames_232_; lean_object* v_lAssignment_233_; lean_object* v_eAssignment_234_; lean_object* v_dAssignment_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_249_; 
v_depth_227_ = lean_ctor_get(v_mctx_219_, 0);
v_levelAssignDepth_228_ = lean_ctor_get(v_mctx_219_, 1);
v_mvarCounter_229_ = lean_ctor_get(v_mctx_219_, 2);
v_lDepth_230_ = lean_ctor_get(v_mctx_219_, 3);
v_decls_231_ = lean_ctor_get(v_mctx_219_, 4);
v_userNames_232_ = lean_ctor_get(v_mctx_219_, 5);
v_lAssignment_233_ = lean_ctor_get(v_mctx_219_, 6);
v_eAssignment_234_ = lean_ctor_get(v_mctx_219_, 7);
v_dAssignment_235_ = lean_ctor_get(v_mctx_219_, 8);
v_isSharedCheck_249_ = !lean_is_exclusive(v_mctx_219_);
if (v_isSharedCheck_249_ == 0)
{
v___x_237_ = v_mctx_219_;
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_dAssignment_235_);
lean_inc(v_eAssignment_234_);
lean_inc(v_lAssignment_233_);
lean_inc(v_userNames_232_);
lean_inc(v_decls_231_);
lean_inc(v_lDepth_230_);
lean_inc(v_mvarCounter_229_);
lean_inc(v_levelAssignDepth_228_);
lean_inc(v_depth_227_);
lean_dec(v_mctx_219_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_233_, v_mvarId_214_, v_val_215_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 6, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_depth_227_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_levelAssignDepth_228_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_mvarCounter_229_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_lDepth_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_decls_231_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_userNames_232_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_eAssignment_234_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_dAssignment_235_);
v___x_241_ = v_reuseFailAlloc_248_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_241_);
v___x_243_ = v___x_225_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_zetaDeltaFVarIds_221_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v_postponed_222_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v_diag_223_);
v___x_243_ = v_reuseFailAlloc_247_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_st_ref_set(v___y_216_, v___x_243_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* v_mvarId_251_, lean_object* v_val_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_251_, v_val_252_, v___y_253_);
lean_dec(v___y_253_);
return v_res_255_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_260_ = lean_unsigned_to_nat(2u);
v___x_261_ = lean_unsigned_to_nat(38u);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_264_ = l_mkPanicMessageWithDecl(v___x_263_, v___x_262_, v___x_261_, v___x_260_, v___x_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_265_, lean_object* v_v_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = l_Lean_Level_isMax(v_v_266_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_v_266_);
lean_dec(v_mvarId_265_);
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_274_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_273_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_mkFreshLevelMVar(v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v___x_277_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_265_, v_v_266_, v_a_276_);
v___x_278_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_265_, v___x_277_, v_a_268_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v_v_266_);
lean_dec(v_mvarId_265_);
v_a_279_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_275_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_287_, lean_object* v_v_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_287_, v_v_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_295_, lean_object* v_val_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_295_, v_val_296_, v___y_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_303_, lean_object* v_val_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_303_, v_val_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_312_, v_x_313_, v_x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_316_, lean_object* v_x_317_, size_t v_x_318_, size_t v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_317_, v_x_318_, v_x_319_, v_x_320_, v_x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_323_, lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
size_t v_x_1030__boxed_329_; size_t v_x_1031__boxed_330_; lean_object* v_res_331_; 
v_x_1030__boxed_329_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_x_1031__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_323_, v_x_324_, v_x_1030__boxed_329_, v_x_1031__boxed_330_, v_x_327_, v_x_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_332_, lean_object* v_n_333_, lean_object* v_k_334_, lean_object* v_v_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3___redArg(v_n_333_, v_k_334_, v_v_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_337_, size_t v_depth_338_, lean_object* v_keys_339_, lean_object* v_vals_340_, lean_object* v_heq_341_, lean_object* v_i_342_, lean_object* v_entries_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_338_, v_keys_339_, v_vals_340_, v_i_342_, v_entries_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_345_, lean_object* v_depth_346_, lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_heq_349_, lean_object* v_i_350_, lean_object* v_entries_351_){
_start:
{
size_t v_depth_boxed_352_; lean_object* v_res_353_; 
v_depth_boxed_352_ = lean_unbox_usize(v_depth_346_);
lean_dec(v_depth_346_);
v_res_353_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_345_, v_depth_boxed_352_, v_keys_347_, v_vals_348_, v_heq_349_, v_i_350_, v_entries_351_);
lean_dec_ref(v_vals_348_);
lean_dec_ref(v_keys_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_355_, v_x_356_, v_x_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(lean_object* v_u_360_, lean_object* v_v_x27_361_, lean_object* v_mvarId_362_, lean_object* v_a_363_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_level_eq(v_u_360_, v_v_x27_361_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_mvarId_362_);
lean_dec(v_u_360_);
v___x_366_ = lean_box(v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v___x_368_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_362_, v_u_360_, v_a_363_);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_368_, 0);
lean_dec(v_unused_377_);
v___x_370_ = v___x_368_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_dec(v___x_368_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_box(v___x_365_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg___boxed(lean_object* v_u_378_, lean_object* v_v_x27_379_, lean_object* v_mvarId_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_378_, v_v_x27_379_, v_mvarId_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec(v_v_x27_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_384_, lean_object* v_v_x27_385_, lean_object* v_mvarId_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_384_, v_v_x27_385_, v_mvarId_386_, v_a_388_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_393_, lean_object* v_v_x27_394_, lean_object* v_mvarId_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_393_, v_v_x27_394_, v_mvarId_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_v_x27_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(lean_object* v_u_402_, lean_object* v_v_403_, lean_object* v_a_404_){
_start:
{
if (lean_obj_tag(v_v_403_) == 2)
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v_v_403_, 1);
lean_inc(v_a_410_);
if (lean_obj_tag(v_a_410_) == 5)
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_411_ = lean_ctor_get(v_v_403_, 0);
lean_inc(v_a_411_);
lean_dec_ref(v_v_403_);
v_a_412_ = lean_ctor_get(v_a_410_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v_a_410_);
v___x_413_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_402_, v_a_411_, v_a_412_, v_a_404_);
lean_dec(v_a_411_);
return v___x_413_;
}
else
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v_v_403_, 0);
lean_inc(v_a_414_);
lean_dec_ref(v_v_403_);
if (lean_obj_tag(v_a_414_) == 5)
{
lean_object* v_a_415_; lean_object* v___x_416_; 
v_a_415_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v_a_414_);
v___x_416_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(v_u_402_, v_a_410_, v_a_415_, v_a_404_);
lean_dec(v_a_410_);
return v___x_416_;
}
else
{
lean_dec(v_a_414_);
lean_dec(v_a_410_);
lean_dec(v_u_402_);
goto v___jp_406_;
}
}
}
else
{
lean_dec(v_v_403_);
lean_dec(v_u_402_);
goto v___jp_406_;
}
v___jp_406_:
{
uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = 0;
v___x_408_ = lean_box(v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg___boxed(lean_object* v_u_417_, lean_object* v_v_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_417_, v_v_418_, v_a_419_);
lean_dec(v_a_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_422_, lean_object* v_v_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_422_, v_v_423_, v_a_425_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_430_, lean_object* v_v_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_430_, v_v_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(lean_object* v_u_u2081_438_, lean_object* v_u_u2082_439_, lean_object* v_v_x27_440_, lean_object* v_mvarId_441_, lean_object* v_a_442_){
_start:
{
uint8_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_level_eq(v_u_u2081_438_, v_v_x27_440_);
v___x_445_ = 1;
if (v___x_444_ == 0)
{
uint8_t v___x_446_; 
v___x_446_ = lean_level_eq(v_u_u2082_439_, v_v_x27_440_);
lean_dec(v_u_u2082_439_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_mvarId_441_);
lean_dec(v_u_u2081_438_);
v___x_447_ = lean_box(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v___x_449_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_441_, v_u_u2081_438_, v_a_442_);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_458_);
v___x_451_ = v___x_449_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___x_449_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_box(v___x_445_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_u_u2081_438_);
v___x_459_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_441_, v_u_u2082_439_, v_a_442_);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_459_, 0);
lean_dec(v_unused_468_);
v___x_461_ = v___x_459_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_dec(v___x_459_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_box(v___x_445_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg___boxed(lean_object* v_u_u2081_469_, lean_object* v_u_u2082_470_, lean_object* v_v_x27_471_, lean_object* v_mvarId_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_u_u2081_469_, v_u_u2082_470_, v_v_x27_471_, v_mvarId_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec(v_v_x27_471_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_476_, lean_object* v_u_u2082_477_, lean_object* v_v_x27_478_, lean_object* v_mvarId_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_u_u2081_476_, v_u_u2082_477_, v_v_x27_478_, v_mvarId_479_, v_a_481_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_486_, lean_object* v_u_u2082_487_, lean_object* v_v_x27_488_, lean_object* v_mvarId_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_486_, v_u_u2082_487_, v_v_x27_488_, v_mvarId_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_v_x27_488_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(lean_object* v_u_496_, lean_object* v_v_497_, lean_object* v_a_498_){
_start:
{
if (lean_obj_tag(v_u_496_) == 2)
{
if (lean_obj_tag(v_v_497_) == 2)
{
lean_object* v_a_504_; 
v_a_504_ = lean_ctor_get(v_v_497_, 1);
lean_inc(v_a_504_);
if (lean_obj_tag(v_a_504_) == 5)
{
lean_object* v_a_505_; lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_505_ = lean_ctor_get(v_u_496_, 0);
lean_inc(v_a_505_);
v_a_506_ = lean_ctor_get(v_u_496_, 1);
lean_inc(v_a_506_);
lean_dec_ref(v_u_496_);
v_a_507_ = lean_ctor_get(v_v_497_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v_v_497_);
v_a_508_ = lean_ctor_get(v_a_504_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v_a_504_);
v___x_509_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_498_);
lean_dec(v_a_507_);
return v___x_509_;
}
else
{
lean_object* v_a_510_; 
v_a_510_ = lean_ctor_get(v_v_497_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v_v_497_);
if (lean_obj_tag(v_a_510_) == 5)
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_511_ = lean_ctor_get(v_u_496_, 0);
lean_inc(v_a_511_);
v_a_512_ = lean_ctor_get(v_u_496_, 1);
lean_inc(v_a_512_);
lean_dec_ref(v_u_496_);
v_a_513_ = lean_ctor_get(v_a_510_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v_a_510_);
v___x_514_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(v_a_511_, v_a_512_, v_a_504_, v_a_513_, v_a_498_);
lean_dec(v_a_504_);
return v___x_514_;
}
else
{
lean_dec(v_a_510_);
lean_dec(v_a_504_);
lean_dec_ref(v_u_496_);
goto v___jp_500_;
}
}
}
else
{
lean_dec_ref(v_u_496_);
lean_dec(v_v_497_);
goto v___jp_500_;
}
}
else
{
lean_dec(v_v_497_);
lean_dec(v_u_496_);
goto v___jp_500_;
}
v___jp_500_:
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = 0;
v___x_502_ = lean_box(v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg___boxed(lean_object* v_u_515_, lean_object* v_v_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_515_, v_v_516_, v_a_517_);
lean_dec(v_a_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_520_, lean_object* v_v_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_520_, v_v_521_, v_a_523_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_528_, lean_object* v_v_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_528_, v_v_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(lean_object* v_msgData_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v_env_543_; lean_object* v___x_544_; lean_object* v_mctx_545_; lean_object* v_lctx_546_; lean_object* v_options_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_542_ = lean_st_ref_get(v___y_540_);
v_env_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_ref(v_env_543_);
lean_dec(v___x_542_);
v___x_544_ = lean_st_ref_get(v___y_538_);
v_mctx_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_mctx_545_);
lean_dec(v___x_544_);
v_lctx_546_ = lean_ctor_get(v___y_537_, 2);
v_options_547_ = lean_ctor_get(v___y_539_, 2);
lean_inc_ref(v_options_547_);
lean_inc_ref(v_lctx_546_);
v___x_548_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_548_, 0, v_env_543_);
lean_ctor_set(v___x_548_, 1, v_mctx_545_);
lean_ctor_set(v___x_548_, 2, v_lctx_546_);
lean_ctor_set(v___x_548_, 3, v_options_547_);
v___x_549_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_msgData_536_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(v_msgData_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_557_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_558_; double v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_float_of_nat(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(lean_object* v_cls_563_, lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_ref_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_616_; 
v_ref_570_ = lean_ctor_get(v___y_567_, 5);
v___x_571_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(v_msg_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_616_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_616_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_616_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v_traceState_577_; lean_object* v_env_578_; lean_object* v_nextMacroScope_579_; lean_object* v_ngen_580_; lean_object* v_auxDeclNGen_581_; lean_object* v_cache_582_; lean_object* v_messages_583_; lean_object* v_infoState_584_; lean_object* v_snapshotTasks_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_615_; 
v___x_576_ = lean_st_ref_take(v___y_568_);
v_traceState_577_ = lean_ctor_get(v___x_576_, 4);
v_env_578_ = lean_ctor_get(v___x_576_, 0);
v_nextMacroScope_579_ = lean_ctor_get(v___x_576_, 1);
v_ngen_580_ = lean_ctor_get(v___x_576_, 2);
v_auxDeclNGen_581_ = lean_ctor_get(v___x_576_, 3);
v_cache_582_ = lean_ctor_get(v___x_576_, 5);
v_messages_583_ = lean_ctor_get(v___x_576_, 6);
v_infoState_584_ = lean_ctor_get(v___x_576_, 7);
v_snapshotTasks_585_ = lean_ctor_get(v___x_576_, 8);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_615_ == 0)
{
v___x_587_ = v___x_576_;
v_isShared_588_ = v_isSharedCheck_615_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snapshotTasks_585_);
lean_inc(v_infoState_584_);
lean_inc(v_messages_583_);
lean_inc(v_cache_582_);
lean_inc(v_traceState_577_);
lean_inc(v_auxDeclNGen_581_);
lean_inc(v_ngen_580_);
lean_inc(v_nextMacroScope_579_);
lean_inc(v_env_578_);
lean_dec(v___x_576_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_615_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint64_t v_tid_589_; lean_object* v_traces_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_614_; 
v_tid_589_ = lean_ctor_get_uint64(v_traceState_577_, sizeof(void*)*1);
v_traces_590_ = lean_ctor_get(v_traceState_577_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_traceState_577_);
if (v_isSharedCheck_614_ == 0)
{
v___x_592_ = v_traceState_577_;
v_isShared_593_ = v_isSharedCheck_614_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_traces_590_);
lean_dec(v_traceState_577_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_614_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; double v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_594_ = lean_box(0);
v___x_595_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0);
v___x_596_ = 0;
v___x_597_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1));
v___x_598_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_598_, 0, v_cls_563_);
lean_ctor_set(v___x_598_, 1, v___x_594_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_ctor_set_float(v___x_598_, sizeof(void*)*3, v___x_595_);
lean_ctor_set_float(v___x_598_, sizeof(void*)*3 + 8, v___x_595_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3 + 16, v___x_596_);
v___x_599_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__2));
v___x_600_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v_a_572_);
lean_ctor_set(v___x_600_, 2, v___x_599_);
lean_inc(v_ref_570_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_ref_570_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_PersistentArray_push___redArg(v_traces_590_, v___x_601_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_602_);
v___x_604_ = v___x_592_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_602_);
lean_ctor_set_uint64(v_reuseFailAlloc_613_, sizeof(void*)*1, v_tid_589_);
v___x_604_ = v_reuseFailAlloc_613_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v___x_604_);
v___x_606_ = v___x_587_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_env_578_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_nextMacroScope_579_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_ngen_580_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_auxDeclNGen_581_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v_cache_582_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v_messages_583_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v_infoState_584_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v_snapshotTasks_585_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = lean_st_ref_set(v___y_568_, v___x_606_);
v___x_608_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_608_);
v___x_610_ = v___x_574_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___boxed(lean_object* v_cls_617_, lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v_cls_617_, v_msg_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_636_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5));
v___x_637_ = l_Lean_Name_append(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_641_, lean_object* v_rhs_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_options_648_; lean_object* v_ref_649_; lean_object* v_inheritedTraceOptions_650_; lean_object* v___y_652_; uint8_t v_hasTrace_672_; 
v_options_648_ = lean_ctor_get(v_a_645_, 2);
v_ref_649_ = lean_ctor_get(v_a_645_, 5);
v_inheritedTraceOptions_650_ = lean_ctor_get(v_a_645_, 13);
v_hasTrace_672_ = lean_ctor_get_uint8(v_options_648_, sizeof(void*)*1);
if (v_hasTrace_672_ == 0)
{
v___y_652_ = v_a_644_;
goto v___jp_651_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_674_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6);
v___x_675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_650_, v_options_648_, v___x_674_);
if (v___x_675_ == 0)
{
v___y_652_ = v_a_644_;
goto v___jp_651_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc(v_lhs_641_);
v___x_676_ = l_Lean_MessageData_ofLevel(v_lhs_641_);
v___x_677_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
lean_inc(v_rhs_642_);
v___x_679_ = l_Lean_MessageData_ofLevel(v_rhs_642_);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v___x_673_, v___x_680_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_dec_ref(v___x_681_);
v___y_652_ = v_a_644_;
goto v___jp_651_;
}
else
{
lean_dec(v_rhs_642_);
lean_dec(v_lhs_641_);
return v___x_681_;
}
}
}
v___jp_651_:
{
lean_object* v___x_653_; lean_object* v_mctx_654_; lean_object* v_cache_655_; lean_object* v_zetaDeltaFVarIds_656_; lean_object* v_postponed_657_; lean_object* v_diag_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_671_; 
v___x_653_ = lean_st_ref_take(v___y_652_);
v_mctx_654_ = lean_ctor_get(v___x_653_, 0);
v_cache_655_ = lean_ctor_get(v___x_653_, 1);
v_zetaDeltaFVarIds_656_ = lean_ctor_get(v___x_653_, 2);
v_postponed_657_ = lean_ctor_get(v___x_653_, 3);
v_diag_658_ = lean_ctor_get(v___x_653_, 4);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_671_ == 0)
{
v___x_660_ = v___x_653_;
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_diag_658_);
lean_inc(v_postponed_657_);
lean_inc(v_zetaDeltaFVarIds_656_);
lean_inc(v_cache_655_);
lean_inc(v_mctx_654_);
lean_dec(v___x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_defEqCtx_x3f_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_defEqCtx_x3f_662_ = lean_ctor_get(v_a_643_, 4);
lean_inc(v_defEqCtx_x3f_662_);
lean_inc(v_ref_649_);
v___x_663_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_663_, 0, v_ref_649_);
lean_ctor_set(v___x_663_, 1, v_lhs_641_);
lean_ctor_set(v___x_663_, 2, v_rhs_642_);
lean_ctor_set(v___x_663_, 3, v_defEqCtx_x3f_662_);
v___x_664_ = l_Lean_PersistentArray_push___redArg(v_postponed_657_, v___x_663_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_mctx_654_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_cache_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_zetaDeltaFVarIds_656_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_diag_658_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_st_ref_set(v___y_652_, v___x_666_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_682_, lean_object* v_rhs_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_682_, v_rhs_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_690_, lean_object* v_mvarId_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
if (lean_obj_tag(v_v_690_) == 5)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v_v_690_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v_v_690_);
v___x_698_ = l_Lean_LMVarId_getLevel(v_a_697_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = l_Lean_LMVarId_getLevel(v_mvarId_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_710_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_710_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_nat_dec_lt(v_a_701_, v_a_699_);
lean_dec(v_a_699_);
lean_dec(v_a_701_);
v___x_706_ = lean_box(v___x_705_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_699_);
v_a_711_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_700_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_700_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_mvarId_691_);
v_a_719_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_698_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_698_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_mvarId_691_);
lean_dec(v_v_690_);
v___x_727_ = 0;
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_730_, lean_object* v_mvarId_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_730_, v_mvarId_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_738_, lean_object* v_v_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___y_746_; lean_object* v___y_775_; lean_object* v___y_776_; 
switch(lean_obj_tag(v_u_738_))
{
case 5:
{
lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_818_ = lean_ctor_get(v_u_738_, 0);
lean_inc(v_a_818_);
v___x_819_ = l_Lean_LMVarId_isReadOnly(v_a_818_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_900_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_900_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_900_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_900_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = lean_unbox(v_a_820_);
lean_dec(v_a_820_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_del_object(v___x_822_);
lean_inc(v_a_818_);
lean_inc(v_v_739_);
v___x_825_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_739_, v_a_818_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_886_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_886_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_886_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_886_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v___y_837_; uint8_t v___x_858_; 
v___x_858_ = lean_unbox(v_a_826_);
lean_dec(v_a_826_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = l_Lean_Level_occurs(v_u_738_, v_v_739_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
lean_del_object(v___x_828_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec_ref(v_a_740_);
v___x_860_ = l_Lean_Level_mvarId_x21(v_u_738_);
lean_dec_ref(v_u_738_);
v___x_861_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_860_, v_v_739_, v_a_741_);
lean_dec(v_a_741_);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_861_, 0);
lean_dec(v_unused_871_);
v___x_863_ = v___x_861_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_861_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = 1;
v___x_866_ = lean_box(v___x_865_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_Level_isMax(v_v_739_);
if (v___x_872_ == 0)
{
v___y_837_ = v___x_872_;
goto v___jp_836_;
}
else
{
uint8_t v___x_873_; 
v___x_873_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_738_, v_v_739_);
if (v___x_873_ == 0)
{
v___y_837_ = v___x_872_;
goto v___jp_836_;
}
else
{
lean_dec_ref(v_u_738_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
goto v___jp_830_;
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_884_; 
lean_del_object(v___x_828_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec_ref(v_a_740_);
v___x_874_ = l_Lean_Level_mvarId_x21(v_v_739_);
lean_dec(v_v_739_);
v___x_875_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_874_, v_u_738_, v_a_741_);
lean_dec(v_a_741_);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_875_, 0);
lean_dec(v_unused_885_);
v___x_877_ = v___x_875_;
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_875_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = 1;
v___x_880_ = lean_box(v___x_879_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
v___jp_830_:
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = 2;
v___x_832_ = lean_box(v___x_831_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_832_);
v___x_834_ = v___x_828_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
v___jp_836_:
{
if (v___y_837_ == 0)
{
lean_dec_ref(v_u_738_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
goto v___jp_830_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_del_object(v___x_828_);
v___x_838_ = l_Lean_Level_mvarId_x21(v_u_738_);
lean_dec_ref(v_u_738_);
v___x_839_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_838_, v_v_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_848_; 
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_839_, 0);
lean_dec(v_unused_849_);
v___x_841_ = v___x_839_;
v_isShared_842_ = v_isSharedCheck_848_;
goto v_resetjp_840_;
}
else
{
lean_dec(v___x_839_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_848_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = 1;
v___x_844_ = lean_box(v___x_843_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_839_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_839_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_u_738_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
v_a_887_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_825_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_825_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec_ref(v_u_738_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
v___x_895_ = 2;
v___x_896_ = lean_box(v___x_895_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_896_);
v___x_898_ = v___x_822_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_u_738_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
v_a_901_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_819_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_819_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_739_))
{
case 5:
{
lean_dec_ref(v_v_739_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
goto v___jp_766_;
}
case 2:
{
lean_object* v_a_909_; lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_909_ = lean_ctor_get(v_v_739_, 0);
lean_inc(v_a_909_);
v_a_910_ = lean_ctor_get(v_v_739_, 1);
lean_inc(v_a_910_);
lean_dec_ref(v_v_739_);
lean_inc(v_a_743_);
lean_inc_ref(v_a_742_);
lean_inc(v_a_741_);
lean_inc_ref(v_a_740_);
v___x_911_ = lean_is_level_def_eq(v_u_738_, v_a_909_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; uint8_t v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
v___x_913_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_913_ == 0)
{
lean_dec(v_a_910_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
v___y_746_ = v___x_911_;
goto v___jp_745_;
}
else
{
lean_object* v___x_914_; 
lean_dec_ref(v___x_911_);
v___x_914_ = lean_is_level_def_eq(v_u_738_, v_a_910_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
v___y_746_ = v___x_914_;
goto v___jp_745_;
}
}
else
{
lean_dec(v_a_910_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
v___y_746_ = v___x_911_;
goto v___jp_745_;
}
}
case 3:
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v_v_739_, 1);
lean_inc(v_a_915_);
lean_dec_ref(v_v_739_);
v___x_916_ = lean_is_level_def_eq(v_u_738_, v_a_915_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_927_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
uint8_t v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_921_ = lean_unbox(v_a_917_);
lean_dec(v_a_917_);
v___x_922_ = l_Bool_toLBool(v___x_921_);
v___x_923_ = lean_box(v___x_922_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_923_);
v___x_925_ = v___x_919_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_916_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_916_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
case 1:
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_v_739_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
v___x_936_ = 0;
v___x_937_ = lean_box(v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
default: 
{
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
v___y_775_ = v_a_740_;
v___y_776_ = v_a_741_;
goto v___jp_774_;
}
}
}
case 1:
{
lean_object* v_a_939_; uint8_t v___y_941_; 
v_a_939_ = lean_ctor_get(v_u_738_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v_u_738_);
if (lean_obj_tag(v_v_739_) == 5)
{
lean_dec_ref(v_v_739_);
lean_dec(v_a_939_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
goto v___jp_766_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_Level_isParam(v_v_739_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Level_isMVar(v_a_939_);
if (v___x_986_ == 0)
{
v___y_941_ = v___x_986_;
goto v___jp_940_;
}
else
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_Level_occurs(v_a_939_, v_v_739_);
v___y_941_ = v___x_987_;
goto v___jp_940_;
}
}
else
{
uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_a_939_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
v___x_988_ = 0;
v___x_989_ = lean_box(v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
v___jp_940_:
{
if (v___y_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Meta_decLevel_x3f(v_v_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_973_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_973_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_973_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_973_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
if (lean_obj_tag(v_a_943_) == 0)
{
uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_a_939_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
v___x_947_ = 2;
v___x_948_ = lean_box(v___x_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_948_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_val_952_; lean_object* v___x_953_; 
lean_del_object(v___x_945_);
v_val_952_ = lean_ctor_get(v_a_943_, 0);
lean_inc(v_val_952_);
lean_dec_ref(v_a_943_);
v___x_953_ = lean_is_level_def_eq(v_a_939_, v_val_952_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
uint8_t v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_958_ = lean_unbox(v_a_954_);
lean_dec(v_a_954_);
v___x_959_ = l_Bool_toLBool(v___x_958_);
v___x_960_ = lean_box(v___x_959_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_953_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_953_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_a_939_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
v_a_974_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_942_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_942_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_a_939_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_v_739_);
v___x_982_ = 2;
v___x_983_ = lean_box(v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
default: 
{
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
if (lean_obj_tag(v_v_739_) == 5)
{
lean_dec_ref(v_v_739_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_u_738_);
goto v___jp_766_;
}
else
{
v___y_775_ = v_a_740_;
v___y_776_ = v_a_741_;
goto v___jp_774_;
}
}
}
v___jp_745_:
{
if (lean_obj_tag(v___y_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_757_; 
v_a_747_ = lean_ctor_get(v___y_746_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___y_746_);
if (v_isSharedCheck_757_ == 0)
{
v___x_749_ = v___y_746_;
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___y_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
uint8_t v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_751_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
v___x_752_ = l_Bool_toLBool(v___x_751_);
v___x_753_ = lean_box(v___x_752_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___y_746_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___y_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___y_746_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___y_746_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
v___jp_766_:
{
uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = 2;
v___x_768_ = lean_box(v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
v___jp_770_:
{
uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = 2;
v___x_772_ = lean_box(v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
v___jp_774_:
{
uint8_t v_univApprox_777_; 
v_univApprox_777_ = lean_ctor_get_uint8(v___y_775_, sizeof(void*)*7 + 1);
lean_dec_ref(v___y_775_);
if (v_univApprox_777_ == 0)
{
lean_dec(v___y_776_);
lean_dec(v_v_739_);
lean_dec(v_u_738_);
goto v___jp_770_;
}
else
{
lean_object* v___x_778_; 
lean_inc(v_v_739_);
lean_inc(v_u_738_);
v___x_778_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_738_, v_v_739_, v___y_776_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_809_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_809_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_809_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_809_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_unbox(v_a_779_);
lean_dec(v_a_779_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_del_object(v___x_781_);
v___x_784_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_738_, v_v_739_, v___y_776_);
lean_dec(v___y_776_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_795_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_795_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_795_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_795_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint8_t v___x_789_; 
v___x_789_ = lean_unbox(v_a_785_);
lean_dec(v_a_785_);
if (v___x_789_ == 0)
{
lean_del_object(v___x_787_);
goto v___jp_770_;
}
else
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_790_ = 1;
v___x_791_ = lean_box(v___x_790_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_791_);
v___x_793_ = v___x_787_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_784_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_784_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v___y_776_);
lean_dec(v_v_739_);
lean_dec(v_u_738_);
v___x_804_ = 1;
v___x_805_ = lean_box(v___x_804_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_805_);
v___x_807_ = v___x_781_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v___y_776_);
lean_dec(v_v_739_);
lean_dec(v_u_738_);
v_a_810_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_778_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_778_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_991_, lean_object* v_v_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_991_, v_v_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_mctx_1003_; lean_object* v___x_1004_; lean_object* v_fst_1005_; lean_object* v_snd_1006_; lean_object* v___x_1007_; lean_object* v_cache_1008_; lean_object* v_zetaDeltaFVarIds_1009_; lean_object* v_postponed_1010_; lean_object* v_diag_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1020_; 
v___x_1002_ = lean_st_ref_get(v___y_1000_);
v_mctx_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc_ref(v_mctx_1003_);
lean_dec(v___x_1002_);
v___x_1004_ = lean_instantiate_level_mvars(v_mctx_1003_, v_l_999_);
v_fst_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_fst_1005_);
v_snd_1006_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_snd_1006_);
lean_dec_ref(v___x_1004_);
v___x_1007_ = lean_st_ref_take(v___y_1000_);
v_cache_1008_ = lean_ctor_get(v___x_1007_, 1);
v_zetaDeltaFVarIds_1009_ = lean_ctor_get(v___x_1007_, 2);
v_postponed_1010_ = lean_ctor_get(v___x_1007_, 3);
v_diag_1011_ = lean_ctor_get(v___x_1007_, 4);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1021_);
v___x_1013_ = v___x_1007_;
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_diag_1011_);
lean_inc(v_postponed_1010_);
lean_inc(v_zetaDeltaFVarIds_1009_);
lean_inc(v_cache_1008_);
lean_dec(v___x_1007_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v_fst_1005_);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_fst_1005_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_cache_1008_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_zetaDeltaFVarIds_1009_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_postponed_1010_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_diag_1011_);
v___x_1016_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_st_ref_set(v___y_1000_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_snd_1006_);
return v___x_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1022_, v___y_1023_);
lean_dec(v___y_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1026_, v___y_1028_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1039_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_unsigned_to_nat(32u);
v___x_1041_ = lean_mk_empty_array_with_capacity(v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1043_ = ((size_t)5ULL);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_unsigned_to_nat(32u);
v___x_1046_ = lean_mk_empty_array_with_capacity(v___x_1045_);
v___x_1047_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0);
v___x_1048_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_1046_);
lean_ctor_set(v___x_1048_, 2, v___x_1044_);
lean_ctor_set(v___x_1048_, 3, v___x_1044_);
lean_ctor_set_usize(v___x_1048_, 4, v___x_1043_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v_traceState_1052_; lean_object* v_traces_1053_; lean_object* v___x_1054_; lean_object* v_traceState_1055_; lean_object* v_env_1056_; lean_object* v_nextMacroScope_1057_; lean_object* v_ngen_1058_; lean_object* v_auxDeclNGen_1059_; lean_object* v_cache_1060_; lean_object* v_messages_1061_; lean_object* v_infoState_1062_; lean_object* v_snapshotTasks_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1082_; 
v___x_1051_ = lean_st_ref_get(v___y_1049_);
v_traceState_1052_ = lean_ctor_get(v___x_1051_, 4);
lean_inc_ref(v_traceState_1052_);
lean_dec(v___x_1051_);
v_traces_1053_ = lean_ctor_get(v_traceState_1052_, 0);
lean_inc_ref(v_traces_1053_);
lean_dec_ref(v_traceState_1052_);
v___x_1054_ = lean_st_ref_take(v___y_1049_);
v_traceState_1055_ = lean_ctor_get(v___x_1054_, 4);
v_env_1056_ = lean_ctor_get(v___x_1054_, 0);
v_nextMacroScope_1057_ = lean_ctor_get(v___x_1054_, 1);
v_ngen_1058_ = lean_ctor_get(v___x_1054_, 2);
v_auxDeclNGen_1059_ = lean_ctor_get(v___x_1054_, 3);
v_cache_1060_ = lean_ctor_get(v___x_1054_, 5);
v_messages_1061_ = lean_ctor_get(v___x_1054_, 6);
v_infoState_1062_ = lean_ctor_get(v___x_1054_, 7);
v_snapshotTasks_1063_ = lean_ctor_get(v___x_1054_, 8);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1065_ = v___x_1054_;
v_isShared_1066_ = v_isSharedCheck_1082_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_snapshotTasks_1063_);
lean_inc(v_infoState_1062_);
lean_inc(v_messages_1061_);
lean_inc(v_cache_1060_);
lean_inc(v_traceState_1055_);
lean_inc(v_auxDeclNGen_1059_);
lean_inc(v_ngen_1058_);
lean_inc(v_nextMacroScope_1057_);
lean_inc(v_env_1056_);
lean_dec(v___x_1054_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1082_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint64_t v_tid_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1080_; 
v_tid_1067_ = lean_ctor_get_uint64(v_traceState_1055_, sizeof(void*)*1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_traceState_1055_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_traceState_1055_, 0);
lean_dec(v_unused_1081_);
v___x_1069_ = v_traceState_1055_;
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_traceState_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1071_);
lean_ctor_set_uint64(v_reuseFailAlloc_1079_, sizeof(void*)*1, v_tid_1067_);
v___x_1073_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1073_);
v___x_1075_ = v___x_1065_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_env_1056_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_nextMacroScope_1057_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_ngen_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_auxDeclNGen_1059_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1078_, 5, v_cache_1060_);
lean_ctor_set(v_reuseFailAlloc_1078_, 6, v_messages_1061_);
lean_ctor_set(v_reuseFailAlloc_1078_, 7, v_infoState_1062_);
lean_ctor_set(v_reuseFailAlloc_1078_, 8, v_snapshotTasks_1063_);
v___x_1075_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_st_ref_set(v___y_1049_, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_traces_1053_);
return v___x_1077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___boxed(lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(v___y_1083_);
lean_dec(v___y_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1098_, lean_object* v_opt_1099_){
_start:
{
lean_object* v_name_1100_; lean_object* v_defValue_1101_; lean_object* v_map_1102_; lean_object* v___x_1103_; 
v_name_1100_ = lean_ctor_get(v_opt_1099_, 0);
v_defValue_1101_ = lean_ctor_get(v_opt_1099_, 1);
v_map_1102_ = lean_ctor_get(v_opts_1098_, 0);
v___x_1103_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1102_, v_name_1100_);
if (lean_obj_tag(v___x_1103_) == 0)
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_unbox(v_defValue_1101_);
return v___x_1104_;
}
else
{
lean_object* v_val_1105_; 
v_val_1105_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1105_);
lean_dec_ref(v___x_1103_);
if (lean_obj_tag(v_val_1105_) == 1)
{
uint8_t v_v_1106_; 
v_v_1106_ = lean_ctor_get_uint8(v_val_1105_, 0);
lean_dec_ref(v_val_1105_);
return v_v_1106_;
}
else
{
uint8_t v___x_1107_; 
lean_dec(v_val_1105_);
v___x_1107_ = lean_unbox(v_defValue_1101_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1108_, lean_object* v_opt_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1108_, v_opt_1109_);
lean_dec_ref(v_opt_1109_);
lean_dec_ref(v_opts_1108_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_instMonadEIO(lean_box(0));
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_toApplicative_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1187_; 
v___x_1123_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0);
v___x_1124_ = l_StateRefT_x27_instMonad___redArg(v___x_1123_);
v_toApplicative_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v___x_1124_, 1);
lean_dec(v_unused_1188_);
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1187_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_toApplicative_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1187_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_toFunctor_1129_; lean_object* v_toSeq_1130_; lean_object* v_toSeqLeft_1131_; lean_object* v_toSeqRight_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1185_; 
v_toFunctor_1129_ = lean_ctor_get(v_toApplicative_1125_, 0);
v_toSeq_1130_ = lean_ctor_get(v_toApplicative_1125_, 2);
v_toSeqLeft_1131_ = lean_ctor_get(v_toApplicative_1125_, 3);
v_toSeqRight_1132_ = lean_ctor_get(v_toApplicative_1125_, 4);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_toApplicative_1125_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v_toApplicative_1125_, 1);
lean_dec(v_unused_1186_);
v___x_1134_ = v_toApplicative_1125_;
v_isShared_1135_ = v_isSharedCheck_1185_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_toSeqRight_1132_);
lean_inc(v_toSeqLeft_1131_);
lean_inc(v_toSeq_1130_);
lean_inc(v_toFunctor_1129_);
lean_dec(v_toApplicative_1125_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1185_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___f_1143_; lean_object* v___x_1145_; 
v___f_1136_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__1));
v___f_1137_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__2));
lean_inc_ref(v_toFunctor_1129_);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1138_, 0, v_toFunctor_1129_);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1139_, 0, v_toFunctor_1129_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___f_1138_);
lean_ctor_set(v___x_1140_, 1, v___f_1139_);
v___f_1141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1141_, 0, v_toSeqRight_1132_);
v___f_1142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1142_, 0, v_toSeqLeft_1131_);
v___f_1143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1143_, 0, v_toSeq_1130_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v___f_1141_);
lean_ctor_set(v___x_1134_, 3, v___f_1142_);
lean_ctor_set(v___x_1134_, 2, v___f_1143_);
lean_ctor_set(v___x_1134_, 1, v___f_1136_);
lean_ctor_set(v___x_1134_, 0, v___x_1140_);
v___x_1145_ = v___x_1134_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___f_1136_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v___f_1143_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v___f_1142_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v___f_1141_);
v___x_1145_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v___f_1137_);
lean_ctor_set(v___x_1127_, 0, v___x_1145_);
v___x_1147_ = v___x_1127_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___f_1137_);
v___x_1147_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v_toApplicative_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1181_; 
v___x_1148_ = l_StateRefT_x27_instMonad___redArg(v___x_1147_);
v_toApplicative_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v___x_1148_, 1);
lean_dec(v_unused_1182_);
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1181_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_toApplicative_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1181_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_toFunctor_1153_; lean_object* v_toSeq_1154_; lean_object* v_toSeqLeft_1155_; lean_object* v_toSeqRight_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1179_; 
v_toFunctor_1153_ = lean_ctor_get(v_toApplicative_1149_, 0);
v_toSeq_1154_ = lean_ctor_get(v_toApplicative_1149_, 2);
v_toSeqLeft_1155_ = lean_ctor_get(v_toApplicative_1149_, 3);
v_toSeqRight_1156_ = lean_ctor_get(v_toApplicative_1149_, 4);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_toApplicative_1149_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v_toApplicative_1149_, 1);
lean_dec(v_unused_1180_);
v___x_1158_ = v_toApplicative_1149_;
v_isShared_1159_ = v_isSharedCheck_1179_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_toSeqRight_1156_);
lean_inc(v_toSeqLeft_1155_);
lean_inc(v_toSeq_1154_);
lean_inc(v_toFunctor_1153_);
lean_dec(v_toApplicative_1149_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1179_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___x_1169_; 
v___f_1160_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__3));
v___f_1161_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__4));
lean_inc_ref(v_toFunctor_1153_);
v___f_1162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1162_, 0, v_toFunctor_1153_);
v___f_1163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1163_, 0, v_toFunctor_1153_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___f_1162_);
lean_ctor_set(v___x_1164_, 1, v___f_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1165_, 0, v_toSeqRight_1156_);
v___f_1166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1166_, 0, v_toSeqLeft_1155_);
v___f_1167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1167_, 0, v_toSeq_1154_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___f_1165_);
lean_ctor_set(v___x_1158_, 3, v___f_1166_);
lean_ctor_set(v___x_1158_, 2, v___f_1167_);
lean_ctor_set(v___x_1158_, 1, v___f_1160_);
lean_ctor_set(v___x_1158_, 0, v___x_1164_);
v___x_1169_ = v___x_1158_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___f_1160_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v___f_1167_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v___f_1166_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v___f_1165_);
v___x_1169_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___f_1161_);
lean_ctor_set(v___x_1151_, 0, v___x_1169_);
v___x_1171_ = v___x_1151_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___f_1161_);
v___x_1171_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_12702__overap_1175_; lean_object* v___x_1176_; 
v___x_1172_ = 0;
v___x_1173_ = lean_box(v___x_1172_);
v___x_1174_ = l_instInhabitedOfMonad___redArg(v___x_1171_, v___x_1173_);
v___x_12702__overap_1175_ = lean_panic_fn_borrowed(v___x_1174_, v_msg_1117_);
lean_dec(v___x_1174_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
v___x_1176_ = lean_apply_5(v___x_12702__overap_1175_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, lean_box(0));
return v___x_1176_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___boxed(lean_object* v_msg_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(v_msg_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(lean_object* v_keys_1196_, lean_object* v_vals_1197_, lean_object* v_i_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_array_get_size(v_keys_1196_);
v___x_1201_ = lean_nat_dec_lt(v_i_1198_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec(v_i_1198_);
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
else
{
lean_object* v_k_x27_1203_; uint8_t v___x_1204_; 
v_k_x27_1203_ = lean_array_fget_borrowed(v_keys_1196_, v_i_1198_);
v___x_1204_ = l_Lean_instBEqLevelMVarId_beq(v_k_1199_, v_k_x27_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_add(v_i_1198_, v___x_1205_);
lean_dec(v_i_1198_);
v_i_1198_ = v___x_1206_;
goto _start;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_array_fget_borrowed(v_vals_1197_, v_i_1198_);
lean_dec(v_i_1198_);
lean_inc(v___x_1208_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_keys_1210_, lean_object* v_vals_1211_, lean_object* v_i_1212_, lean_object* v_k_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(v_keys_1210_, v_vals_1211_, v_i_1212_, v_k_1213_);
lean_dec(v_k_1213_);
lean_dec_ref(v_vals_1211_);
lean_dec_ref(v_keys_1210_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(lean_object* v_x_1215_, size_t v_x_1216_, lean_object* v_x_1217_){
_start:
{
if (lean_obj_tag(v_x_1215_) == 0)
{
lean_object* v_es_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1239_; 
v_es_1218_ = lean_ctor_get(v_x_1215_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1215_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1220_ = v_x_1215_;
v_isShared_1221_ = v_isSharedCheck_1239_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_es_1218_);
lean_dec(v_x_1215_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1239_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v_j_1226_; lean_object* v___x_1227_; 
v___x_1222_ = lean_box(2);
v___x_1223_ = ((size_t)5ULL);
v___x_1224_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1225_ = lean_usize_land(v_x_1216_, v___x_1224_);
v_j_1226_ = lean_usize_to_nat(v___x_1225_);
v___x_1227_ = lean_array_get(v___x_1222_, v_es_1218_, v_j_1226_);
lean_dec(v_j_1226_);
lean_dec_ref(v_es_1218_);
switch(lean_obj_tag(v___x_1227_))
{
case 0:
{
lean_object* v_key_1228_; lean_object* v_val_1229_; uint8_t v___x_1230_; 
v_key_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_key_1228_);
v_val_1229_ = lean_ctor_get(v___x_1227_, 1);
lean_inc(v_val_1229_);
lean_dec_ref(v___x_1227_);
v___x_1230_ = l_Lean_instBEqLevelMVarId_beq(v_x_1217_, v_key_1228_);
lean_dec(v_key_1228_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_val_1229_);
lean_del_object(v___x_1220_);
v___x_1231_ = lean_box(0);
return v___x_1231_;
}
else
{
lean_object* v___x_1233_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 0, v_val_1229_);
v___x_1233_ = v___x_1220_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_val_1229_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
case 1:
{
lean_object* v_node_1235_; size_t v___x_1236_; 
lean_del_object(v___x_1220_);
v_node_1235_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_node_1235_);
lean_dec_ref(v___x_1227_);
v___x_1236_ = lean_usize_shift_right(v_x_1216_, v___x_1223_);
v_x_1215_ = v_node_1235_;
v_x_1216_ = v___x_1236_;
goto _start;
}
default: 
{
lean_object* v___x_1238_; 
lean_del_object(v___x_1220_);
v___x_1238_ = lean_box(0);
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_ks_1240_; lean_object* v_vs_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_ks_1240_ = lean_ctor_get(v_x_1215_, 0);
lean_inc_ref(v_ks_1240_);
v_vs_1241_ = lean_ctor_get(v_x_1215_, 1);
lean_inc_ref(v_vs_1241_);
lean_dec_ref(v_x_1215_);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(v_ks_1240_, v_vs_1241_, v___x_1242_, v_x_1217_);
lean_dec_ref(v_vs_1241_);
lean_dec_ref(v_ks_1240_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
size_t v_x_13667__boxed_1247_; lean_object* v_res_1248_; 
v_x_13667__boxed_1247_ = lean_unbox_usize(v_x_1245_);
lean_dec(v_x_1245_);
v_res_1248_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(v_x_1244_, v_x_13667__boxed_1247_, v_x_1246_);
lean_dec(v_x_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint64_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = l_Lean_instHashableLevelMVarId_hash(v_x_1250_);
v___x_1252_ = lean_uint64_to_usize(v___x_1251_);
v___x_1253_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(v_x_1249_, v___x_1252_, v_x_1250_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(v_x_1254_, v_x_1255_);
lean_dec(v_x_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(lean_object* v_mvarId_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v_mctx_1267_; lean_object* v_levelAssignDepth_1268_; lean_object* v_lDepth_1269_; lean_object* v___x_1270_; 
v___x_1266_ = lean_st_ref_get(v___y_1262_);
v_mctx_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc_ref(v_mctx_1267_);
lean_dec(v___x_1266_);
v_levelAssignDepth_1268_ = lean_ctor_get(v_mctx_1267_, 1);
lean_inc(v_levelAssignDepth_1268_);
v_lDepth_1269_ = lean_ctor_get(v_mctx_1267_, 3);
lean_inc_ref(v_lDepth_1269_);
lean_dec_ref(v_mctx_1267_);
v___x_1270_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(v_lDepth_1269_, v_mvarId_1260_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_mvarId_1260_);
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_val_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
uint8_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_nat_dec_le(v_levelAssignDepth_1268_, v_val_1271_);
lean_dec(v_val_1271_);
lean_dec(v_levelAssignDepth_1268_);
v___x_1276_ = lean_box(v___x_1275_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec(v___x_1270_);
lean_dec(v_levelAssignDepth_1268_);
v___x_1281_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__0));
v___x_1282_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__1));
v___x_1283_ = lean_unsigned_to_nat(451u);
v___x_1284_ = lean_unsigned_to_nat(14u);
v___x_1285_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__2));
v___x_1286_ = 1;
v___x_1287_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1260_, v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1285_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = l_mkPanicMessageWithDecl(v___x_1281_, v___x_1282_, v___x_1283_, v___x_1284_, v___x_1288_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(v___x_1289_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___boxed(lean_object* v_mvarId_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(v_mvarId_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___y_1305_; lean_object* v___y_1306_; uint8_t v_a_1307_; lean_object* v_lvl_u2081_1313_; lean_object* v_lvl_u2082_1314_; 
switch(lean_obj_tag(v_x_1298_))
{
case 1:
{
lean_object* v_a_1321_; uint8_t v___x_1322_; 
v_a_1321_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v_x_1298_);
v___x_1322_ = l_Lean_Level_hasMVar(v_a_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_a_1321_);
v___x_1323_ = lean_box(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
v_x_1298_ = v_a_1321_;
goto _start;
}
}
case 2:
{
lean_object* v_a_1326_; lean_object* v_a_1327_; 
v_a_1326_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_a_1326_);
v_a_1327_ = lean_ctor_get(v_x_1298_, 1);
lean_inc(v_a_1327_);
lean_dec_ref(v_x_1298_);
v_lvl_u2081_1313_ = v_a_1326_;
v_lvl_u2082_1314_ = v_a_1327_;
goto v___jp_1312_;
}
case 3:
{
lean_object* v_a_1328_; lean_object* v_a_1329_; 
v_a_1328_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_a_1328_);
v_a_1329_ = lean_ctor_get(v_x_1298_, 1);
lean_inc(v_a_1329_);
lean_dec_ref(v_x_1298_);
v_lvl_u2081_1313_ = v_a_1328_;
v_lvl_u2082_1314_ = v_a_1329_;
goto v___jp_1312_;
}
case 5:
{
lean_object* v_a_1330_; lean_object* v___x_1331_; 
v_a_1330_ = lean_ctor_get(v_x_1298_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v_x_1298_);
v___x_1331_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(v_a_1330_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1331_;
}
default: 
{
uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v_x_1298_);
v___x_1332_ = 0;
v___x_1333_ = lean_box(v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
v___jp_1304_:
{
if (v_a_1307_ == 0)
{
uint8_t v___x_1308_; 
lean_dec_ref(v___y_1306_);
v___x_1308_ = l_Lean_Level_hasMVar(v___y_1305_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v___y_1305_);
v___x_1309_ = lean_box(v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
else
{
v_x_1298_ = v___y_1305_;
goto _start;
}
}
else
{
lean_dec(v___y_1305_);
return v___y_1306_;
}
}
v___jp_1312_:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_Level_hasMVar(v_lvl_u2081_1313_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_lvl_u2081_1313_);
v___x_1316_ = lean_box(v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___y_1305_ = v_lvl_u2082_1314_;
v___y_1306_ = v___x_1317_;
v_a_1307_ = v___x_1315_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_lvl_u2081_1313_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; uint8_t v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
v___x_1320_ = lean_unbox(v_a_1319_);
lean_dec(v_a_1319_);
v___y_1305_ = v_lvl_u2082_1314_;
v___y_1306_ = v___x_1318_;
v_a_1307_ = v___x_1320_;
goto v___jp_1304_;
}
else
{
lean_dec(v_lvl_u2082_1314_);
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_x_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1342_, lean_object* v_lhs_1343_, lean_object* v_rhs_1344_, lean_object* v___x_1345_, lean_object* v___x_1346_, uint8_t v___x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___y_1380_; 
if (v___x_1342_ == 0)
{
lean_object* v___x_1417_; lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v_a_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
lean_inc(v_lhs_1343_);
v___x_1417_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1343_, v___y_1349_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
lean_inc(v_rhs_1344_);
v___x_1419_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1344_, v___y_1349_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = l_Lean_Level_normalize(v_a_1418_);
lean_dec(v_a_1418_);
v___x_1422_ = l_Lean_Level_normalize(v_a_1420_);
lean_dec(v_a_1420_);
v___x_1423_ = lean_level_eq(v_lhs_1343_, v___x_1421_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1424_ = lean_is_level_def_eq(v___x_1421_, v___x_1422_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1424_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_level_eq(v_rhs_1344_, v___x_1422_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1426_ = lean_is_level_def_eq(v___x_1421_, v___x_1422_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v___x_1422_);
lean_dec(v___x_1421_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v_rhs_1344_);
lean_inc(v_lhs_1343_);
v___x_1427_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1343_, v_rhs_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1469_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1469_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1469_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = 2;
v___x_1433_ = lean_unbox(v_a_1428_);
v___x_1434_ = l_Lean_instBEqLBool_beq(v___x_1433_, v___x_1432_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; uint8_t v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v___x_1435_ = 1;
v___x_1436_ = lean_unbox(v_a_1428_);
lean_dec(v_a_1428_);
v___x_1437_ = l_Lean_instBEqLBool_beq(v___x_1436_, v___x_1435_);
v___x_1438_ = lean_box(v___x_1437_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1438_);
v___x_1440_ = v___x_1430_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1442_; 
lean_del_object(v___x_1430_);
lean_dec(v_a_1428_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v_lhs_1343_);
lean_inc(v_rhs_1344_);
v___x_1442_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1344_, v_lhs_1343_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1460_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1460_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1460_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
uint8_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_unbox(v_a_1443_);
v___x_1448_ = l_Lean_instBEqLBool_beq(v___x_1447_, v___x_1432_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; uint8_t v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v___x_1449_ = 1;
v___x_1450_ = lean_unbox(v_a_1443_);
lean_dec(v_a_1443_);
v___x_1451_ = l_Lean_instBEqLBool_beq(v___x_1450_, v___x_1449_);
v___x_1452_ = lean_box(v___x_1451_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1452_);
v___x_1454_ = v___x_1445_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
else
{
lean_object* v___x_1456_; 
lean_del_object(v___x_1445_);
lean_dec(v_a_1443_);
lean_inc(v_lhs_1343_);
v___x_1456_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_lhs_1343_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; uint8_t v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
v___x_1458_ = lean_unbox(v_a_1457_);
lean_dec(v_a_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref(v___x_1456_);
lean_inc(v_rhs_1344_);
v___x_1459_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_rhs_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1380_ = v___x_1459_;
goto v___jp_1379_;
}
else
{
v___y_1380_ = v___x_1456_;
goto v___jp_1379_;
}
}
else
{
v___y_1380_ = v___x_1456_;
goto v___jp_1379_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v_a_1461_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1442_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1442_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v_a_1470_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1427_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1427_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
v___x_1478_ = l_Lean_Level_getOffset(v_lhs_1343_);
lean_dec(v_lhs_1343_);
v___x_1479_ = l_Lean_Level_getOffset(v_rhs_1344_);
lean_dec(v_rhs_1344_);
v___x_1480_ = lean_nat_dec_eq(v___x_1478_, v___x_1479_);
lean_dec(v___x_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
v___jp_1353_:
{
lean_object* v_options_1354_; uint8_t v_hasTrace_1355_; 
v_options_1354_ = lean_ctor_get(v___y_1350_, 2);
v_hasTrace_1355_ = lean_ctor_get_uint8(v_options_1354_, sizeof(void*)*1);
if (v_hasTrace_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v___x_1356_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1356_;
}
else
{
lean_object* v_inheritedTraceOptions_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_inheritedTraceOptions_1357_ = lean_ctor_get(v___y_1350_, 13);
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2));
v___x_1359_ = l_Lean_Name_mkStr3(v___x_1345_, v___x_1346_, v___x_1358_);
v___x_1360_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5));
lean_inc(v___x_1359_);
v___x_1361_ = l_Lean_Name_append(v___x_1360_, v___x_1359_);
v___x_1362_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1357_, v_options_1354_, v___x_1361_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec(v___x_1359_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v___x_1363_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1364_ = l_Lean_MessageData_ofLevel(v_lhs_1343_);
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l_Lean_MessageData_ofLevel(v_rhs_1344_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v___x_1359_, v___x_1368_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; 
lean_dec_ref(v___x_1369_);
v___x_1370_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1370_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1369_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
v___jp_1379_:
{
if (lean_obj_tag(v___y_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1416_; 
v_a_1381_ = lean_ctor_get(v___y_1380_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___y_1380_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1383_ = v___y_1380_;
v_isShared_1384_ = v_isSharedCheck_1416_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___y_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1416_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_unbox(v_a_1381_);
lean_dec(v_a_1381_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; uint8_t v_isDefEqStuckEx_1387_; 
v___x_1386_ = l_Lean_Meta_Context_config(v___y_1348_);
v_isDefEqStuckEx_1387_ = lean_ctor_get_uint8(v___x_1386_, 4);
lean_dec_ref(v___x_1386_);
if (v_isDefEqStuckEx_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v___x_1388_ = lean_box(v_isDefEqStuckEx_1387_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1388_);
v___x_1390_ = v___x_1383_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_Level_isMVar(v_lhs_1343_);
if (v___x_1392_ == 0)
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lean_Level_isMVar(v_rhs_1344_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
v___x_1394_ = lean_box(v___x_1393_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1394_);
v___x_1396_ = v___x_1383_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
else
{
lean_del_object(v___x_1383_);
goto v___jp_1353_;
}
}
else
{
lean_del_object(v___x_1383_);
goto v___jp_1353_;
}
}
}
else
{
lean_object* v___x_1398_; 
lean_del_object(v___x_1383_);
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
v___x_1398_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1343_, v_rhs_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1407_);
v___x_1400_ = v___x_1398_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v___x_1398_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(v___x_1347_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1398_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1346_);
lean_dec_ref(v___x_1345_);
lean_dec(v_rhs_1344_);
lean_dec(v_lhs_1343_);
return v___y_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1483_, lean_object* v_lhs_1484_, lean_object* v_rhs_1485_, lean_object* v___x_1486_, lean_object* v___x_1487_, lean_object* v___x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_13891__boxed_1494_; uint8_t v___x_13894__boxed_1495_; lean_object* v_res_1496_; 
v___x_13891__boxed_1494_ = lean_unbox(v___x_1483_);
v___x_13894__boxed_1495_ = lean_unbox(v___x_1488_);
v_res_1496_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13891__boxed_1494_, v_lhs_1484_, v_rhs_1485_, v___x_1486_, v___x_1487_, v___x_13894__boxed_1495_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(lean_object* v_lhs_1497_, lean_object* v_rhs_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1505_ = l_Lean_MessageData_ofLevel(v_lhs_1497_);
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_MessageData_ofLevel(v_rhs_1498_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object* v_lhs_1511_, lean_object* v_rhs_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(v_lhs_1511_, v_rhs_1512_, v_x_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_x_1513_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(size_t v_sz_1520_, size_t v_i_1521_, lean_object* v_bs_1522_){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_usize_dec_lt(v_i_1521_, v_sz_1520_);
if (v___x_1523_ == 0)
{
return v_bs_1522_;
}
else
{
lean_object* v_v_1524_; lean_object* v_msg_1525_; lean_object* v___x_1526_; lean_object* v_bs_x27_1527_; size_t v___x_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v_v_1524_ = lean_array_uget_borrowed(v_bs_1522_, v_i_1521_);
v_msg_1525_ = lean_ctor_get(v_v_1524_, 1);
lean_inc_ref(v_msg_1525_);
v___x_1526_ = lean_unsigned_to_nat(0u);
v_bs_x27_1527_ = lean_array_uset(v_bs_1522_, v_i_1521_, v___x_1526_);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_add(v_i_1521_, v___x_1528_);
v___x_1530_ = lean_array_uset(v_bs_x27_1527_, v_i_1521_, v_msg_1525_);
v_i_1521_ = v___x_1529_;
v_bs_1522_ = v___x_1530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_bs_1534_){
_start:
{
size_t v_sz_boxed_1535_; size_t v_i_boxed_1536_; lean_object* v_res_1537_; 
v_sz_boxed_1535_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(v_sz_boxed_1535_, v_i_boxed_1536_, v_bs_1534_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(lean_object* v_oldTraces_1538_, lean_object* v_data_1539_, lean_object* v_ref_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_fileName_1547_; lean_object* v_fileMap_1548_; lean_object* v_options_1549_; lean_object* v_currRecDepth_1550_; lean_object* v_maxRecDepth_1551_; lean_object* v_ref_1552_; lean_object* v_currNamespace_1553_; lean_object* v_openDecls_1554_; lean_object* v_initHeartbeats_1555_; lean_object* v_maxHeartbeats_1556_; lean_object* v_quotContext_1557_; lean_object* v_currMacroScope_1558_; uint8_t v_diag_1559_; lean_object* v_cancelTk_x3f_1560_; uint8_t v_suppressElabErrors_1561_; lean_object* v_inheritedTraceOptions_1562_; lean_object* v___x_1563_; lean_object* v_traceState_1564_; lean_object* v_traces_1565_; lean_object* v_ref_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; lean_object* v_msg_1572_; lean_object* v___x_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1611_; 
v_fileName_1547_ = lean_ctor_get(v___y_1544_, 0);
v_fileMap_1548_ = lean_ctor_get(v___y_1544_, 1);
v_options_1549_ = lean_ctor_get(v___y_1544_, 2);
v_currRecDepth_1550_ = lean_ctor_get(v___y_1544_, 3);
v_maxRecDepth_1551_ = lean_ctor_get(v___y_1544_, 4);
v_ref_1552_ = lean_ctor_get(v___y_1544_, 5);
v_currNamespace_1553_ = lean_ctor_get(v___y_1544_, 6);
v_openDecls_1554_ = lean_ctor_get(v___y_1544_, 7);
v_initHeartbeats_1555_ = lean_ctor_get(v___y_1544_, 8);
v_maxHeartbeats_1556_ = lean_ctor_get(v___y_1544_, 9);
v_quotContext_1557_ = lean_ctor_get(v___y_1544_, 10);
v_currMacroScope_1558_ = lean_ctor_get(v___y_1544_, 11);
v_diag_1559_ = lean_ctor_get_uint8(v___y_1544_, sizeof(void*)*14);
v_cancelTk_x3f_1560_ = lean_ctor_get(v___y_1544_, 12);
v_suppressElabErrors_1561_ = lean_ctor_get_uint8(v___y_1544_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1562_ = lean_ctor_get(v___y_1544_, 13);
v___x_1563_ = lean_st_ref_get(v___y_1545_);
v_traceState_1564_ = lean_ctor_get(v___x_1563_, 4);
lean_inc_ref(v_traceState_1564_);
lean_dec(v___x_1563_);
v_traces_1565_ = lean_ctor_get(v_traceState_1564_, 0);
lean_inc_ref(v_traces_1565_);
lean_dec_ref(v_traceState_1564_);
v_ref_1566_ = l_Lean_replaceRef(v_ref_1540_, v_ref_1552_);
lean_inc_ref(v_inheritedTraceOptions_1562_);
lean_inc(v_cancelTk_x3f_1560_);
lean_inc(v_currMacroScope_1558_);
lean_inc(v_quotContext_1557_);
lean_inc(v_maxHeartbeats_1556_);
lean_inc(v_initHeartbeats_1555_);
lean_inc(v_openDecls_1554_);
lean_inc(v_currNamespace_1553_);
lean_inc(v_maxRecDepth_1551_);
lean_inc(v_currRecDepth_1550_);
lean_inc_ref(v_options_1549_);
lean_inc_ref(v_fileMap_1548_);
lean_inc_ref(v_fileName_1547_);
v___x_1567_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1567_, 0, v_fileName_1547_);
lean_ctor_set(v___x_1567_, 1, v_fileMap_1548_);
lean_ctor_set(v___x_1567_, 2, v_options_1549_);
lean_ctor_set(v___x_1567_, 3, v_currRecDepth_1550_);
lean_ctor_set(v___x_1567_, 4, v_maxRecDepth_1551_);
lean_ctor_set(v___x_1567_, 5, v_ref_1566_);
lean_ctor_set(v___x_1567_, 6, v_currNamespace_1553_);
lean_ctor_set(v___x_1567_, 7, v_openDecls_1554_);
lean_ctor_set(v___x_1567_, 8, v_initHeartbeats_1555_);
lean_ctor_set(v___x_1567_, 9, v_maxHeartbeats_1556_);
lean_ctor_set(v___x_1567_, 10, v_quotContext_1557_);
lean_ctor_set(v___x_1567_, 11, v_currMacroScope_1558_);
lean_ctor_set(v___x_1567_, 12, v_cancelTk_x3f_1560_);
lean_ctor_set(v___x_1567_, 13, v_inheritedTraceOptions_1562_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*14, v_diag_1559_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*14 + 1, v_suppressElabErrors_1561_);
v___x_1568_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1565_);
lean_dec_ref(v_traces_1565_);
v_sz_1569_ = lean_array_size(v___x_1568_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(v_sz_1569_, v___x_1570_, v___x_1568_);
v_msg_1572_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1572_, 0, v_data_1539_);
lean_ctor_set(v_msg_1572_, 1, v_msg_1541_);
lean_ctor_set(v_msg_1572_, 2, v___x_1571_);
v___x_1573_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0_spec__0(v_msg_1572_, v___y_1542_, v___y_1543_, v___x_1567_, v___y_1545_);
lean_dec_ref(v___x_1567_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1611_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1611_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v_traceState_1579_; lean_object* v_env_1580_; lean_object* v_nextMacroScope_1581_; lean_object* v_ngen_1582_; lean_object* v_auxDeclNGen_1583_; lean_object* v_cache_1584_; lean_object* v_messages_1585_; lean_object* v_infoState_1586_; lean_object* v_snapshotTasks_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1610_; 
v___x_1578_ = lean_st_ref_take(v___y_1545_);
v_traceState_1579_ = lean_ctor_get(v___x_1578_, 4);
v_env_1580_ = lean_ctor_get(v___x_1578_, 0);
v_nextMacroScope_1581_ = lean_ctor_get(v___x_1578_, 1);
v_ngen_1582_ = lean_ctor_get(v___x_1578_, 2);
v_auxDeclNGen_1583_ = lean_ctor_get(v___x_1578_, 3);
v_cache_1584_ = lean_ctor_get(v___x_1578_, 5);
v_messages_1585_ = lean_ctor_get(v___x_1578_, 6);
v_infoState_1586_ = lean_ctor_get(v___x_1578_, 7);
v_snapshotTasks_1587_ = lean_ctor_get(v___x_1578_, 8);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1589_ = v___x_1578_;
v_isShared_1590_ = v_isSharedCheck_1610_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snapshotTasks_1587_);
lean_inc(v_infoState_1586_);
lean_inc(v_messages_1585_);
lean_inc(v_cache_1584_);
lean_inc(v_traceState_1579_);
lean_inc(v_auxDeclNGen_1583_);
lean_inc(v_ngen_1582_);
lean_inc(v_nextMacroScope_1581_);
lean_inc(v_env_1580_);
lean_dec(v___x_1578_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1610_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
uint64_t v_tid_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1608_; 
v_tid_1591_ = lean_ctor_get_uint64(v_traceState_1579_, sizeof(void*)*1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_traceState_1579_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v_traceState_1579_, 0);
lean_dec(v_unused_1609_);
v___x_1593_ = v_traceState_1579_;
v_isShared_1594_ = v_isSharedCheck_1608_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v_traceState_1579_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1608_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_ref_1540_);
lean_ctor_set(v___x_1595_, 1, v_a_1574_);
v___x_1596_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1538_, v___x_1595_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1596_);
lean_ctor_set_uint64(v_reuseFailAlloc_1607_, sizeof(void*)*1, v_tid_1591_);
v___x_1598_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v___x_1598_);
v___x_1600_ = v___x_1589_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_env_1580_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_nextMacroScope_1581_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_ngen_1582_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_auxDeclNGen_1583_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v_cache_1584_);
lean_ctor_set(v_reuseFailAlloc_1606_, 6, v_messages_1585_);
lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_infoState_1586_);
lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_snapshotTasks_1587_);
v___x_1600_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = lean_st_ref_set(v___y_1545_, v___x_1600_);
v___x_1602_ = lean_box(0);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1602_);
v___x_1604_ = v___x_1576_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6___boxed(lean_object* v_oldTraces_1612_, lean_object* v_data_1613_, lean_object* v_ref_1614_, lean_object* v_msg_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(v_oldTraces_1612_, v_data_1613_, v_ref_1614_, v_msg_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1624_ = lean_ctor_get(v_x_1622_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1622_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v_x_1622_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v_x_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v_x_1622_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1622_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v_x_1622_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v_x_1622_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 0);
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg___boxed(lean_object* v_x_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_x_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(lean_object* v_opts_1643_, lean_object* v_opt_1644_){
_start:
{
lean_object* v_name_1645_; lean_object* v_defValue_1646_; lean_object* v_map_1647_; lean_object* v___x_1648_; 
v_name_1645_ = lean_ctor_get(v_opt_1644_, 0);
v_defValue_1646_ = lean_ctor_get(v_opt_1644_, 1);
v_map_1647_ = lean_ctor_get(v_opts_1643_, 0);
v___x_1648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1647_, v_name_1645_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_inc(v_defValue_1646_);
return v_defValue_1646_;
}
else
{
lean_object* v_val_1649_; 
v_val_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_val_1649_);
lean_dec_ref(v___x_1648_);
if (lean_obj_tag(v_val_1649_) == 3)
{
lean_object* v_v_1650_; 
v_v_1650_ = lean_ctor_get(v_val_1649_, 0);
lean_inc(v_v_1650_);
lean_dec_ref(v_val_1649_);
return v_v_1650_;
}
else
{
lean_dec(v_val_1649_);
lean_inc(v_defValue_1646_);
return v_defValue_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8___boxed(lean_object* v_opts_1651_, lean_object* v_opt_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(v_opts_1651_, v_opt_1652_);
lean_dec_ref(v_opt_1652_);
lean_dec_ref(v_opts_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(lean_object* v_e_1654_){
_start:
{
if (lean_obj_tag(v_e_1654_) == 0)
{
uint8_t v___x_1655_; 
v___x_1655_ = 2;
return v___x_1655_;
}
else
{
lean_object* v_a_1656_; uint8_t v___x_1657_; 
v_a_1656_ = lean_ctor_get(v_e_1654_, 0);
v___x_1657_ = lean_unbox(v_a_1656_);
if (v___x_1657_ == 0)
{
uint8_t v___x_1658_; 
v___x_1658_ = 1;
return v___x_1658_;
}
else
{
uint8_t v___x_1659_; 
v___x_1659_ = 0;
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5___boxed(lean_object* v_e_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(v_e_1660_);
lean_dec_ref(v_e_1660_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__0));
v___x_1665_ = l_Lean_stringToMessageData(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__2));
v___x_1668_ = l_Lean_stringToMessageData(v___x_1667_);
return v___x_1668_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1669_; double v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(1000u);
v___x_1670_ = lean_float_of_nat(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_cls_1671_, uint8_t v_collapsed_1672_, lean_object* v_tag_1673_, lean_object* v_opts_1674_, uint8_t v_clsEnabled_1675_, lean_object* v_oldTraces_1676_, lean_object* v_msg_1677_, lean_object* v_resStartStop_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1783_; 
v_fst_1684_ = lean_ctor_get(v_resStartStop_1678_, 0);
v_snd_1685_ = lean_ctor_get(v_resStartStop_1678_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_resStartStop_1678_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1687_ = v_resStartStop_1678_;
v_isShared_1688_ = v_isSharedCheck_1783_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_snd_1685_);
lean_inc(v_fst_1684_);
lean_dec(v_resStartStop_1678_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1783_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v_data_1692_; lean_object* v_fst_1703_; lean_object* v_snd_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1782_; 
v_fst_1703_ = lean_ctor_get(v_snd_1685_, 0);
v_snd_1704_ = lean_ctor_get(v_snd_1685_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_snd_1685_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1706_ = v_snd_1685_;
v_isShared_1707_ = v_isSharedCheck_1782_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_snd_1704_);
lean_inc(v_fst_1703_);
lean_dec(v_snd_1685_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1782_;
goto v_resetjp_1705_;
}
v___jp_1689_:
{
lean_object* v___x_1693_; 
lean_inc(v___y_1691_);
v___x_1693_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(v_oldTraces_1676_, v_data_1692_, v___y_1691_, v___y_1690_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v___x_1693_);
v___x_1694_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_fst_1684_);
return v___x_1694_;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_fst_1684_);
v_a_1695_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1693_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___y_1711_; lean_object* v_a_1712_; uint8_t v___y_1736_; double v___y_1767_; 
v___x_1708_ = l_Lean_trace_profiler;
v___x_1709_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1674_, v___x_1708_);
if (v___x_1709_ == 0)
{
v___y_1736_ = v___x_1709_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1773_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1674_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; double v___x_1776_; double v___x_1777_; double v___x_1778_; 
v___x_1774_ = l_Lean_trace_profiler_threshold;
v___x_1775_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(v_opts_1674_, v___x_1774_);
v___x_1776_ = lean_float_of_nat(v___x_1775_);
v___x_1777_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4);
v___x_1778_ = lean_float_div(v___x_1776_, v___x_1777_);
v___y_1767_ = v___x_1778_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; double v___x_1781_; 
v___x_1779_ = l_Lean_trace_profiler_threshold;
v___x_1780_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(v_opts_1674_, v___x_1779_);
v___x_1781_ = lean_float_of_nat(v___x_1780_);
v___y_1767_ = v___x_1781_;
goto v___jp_1766_;
}
}
v___jp_1710_:
{
uint8_t v_result_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v_result_1713_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(v_fst_1684_);
v___x_1714_ = l_Lean_TraceResult_toEmoji(v_result_1713_);
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
v___x_1716_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 7);
lean_ctor_set(v___x_1706_, 1, v___x_1716_);
lean_ctor_set(v___x_1706_, 0, v___x_1715_);
v___x_1718_ = v___x_1706_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v_m_1720_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 7);
lean_ctor_set(v___x_1687_, 1, v_a_1712_);
lean_ctor_set(v___x_1687_, 0, v___x_1718_);
v_m_1720_ = v___x_1687_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_a_1712_);
v_m_1720_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; double v___x_1723_; lean_object* v_data_1724_; 
v___x_1721_ = lean_box(v_result_1713_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
v___x_1723_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__0);
lean_inc_ref(v_tag_1673_);
lean_inc_ref(v___x_1722_);
lean_inc(v_cls_1671_);
v_data_1724_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1724_, 0, v_cls_1671_);
lean_ctor_set(v_data_1724_, 1, v___x_1722_);
lean_ctor_set(v_data_1724_, 2, v_tag_1673_);
lean_ctor_set_float(v_data_1724_, sizeof(void*)*3, v___x_1723_);
lean_ctor_set_float(v_data_1724_, sizeof(void*)*3 + 8, v___x_1723_);
lean_ctor_set_uint8(v_data_1724_, sizeof(void*)*3 + 16, v_collapsed_1672_);
if (v___x_1709_ == 0)
{
lean_dec_ref(v___x_1722_);
lean_dec(v_snd_1704_);
lean_dec(v_fst_1703_);
lean_dec_ref(v_tag_1673_);
lean_dec(v_cls_1671_);
v___y_1690_ = v_m_1720_;
v___y_1691_ = v___y_1711_;
v_data_1692_ = v_data_1724_;
goto v___jp_1689_;
}
else
{
lean_object* v_data_1725_; double v___x_1726_; double v___x_1727_; 
lean_dec_ref(v_data_1724_);
v_data_1725_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1725_, 0, v_cls_1671_);
lean_ctor_set(v_data_1725_, 1, v___x_1722_);
lean_ctor_set(v_data_1725_, 2, v_tag_1673_);
v___x_1726_ = lean_unbox_float(v_fst_1703_);
lean_dec(v_fst_1703_);
lean_ctor_set_float(v_data_1725_, sizeof(void*)*3, v___x_1726_);
v___x_1727_ = lean_unbox_float(v_snd_1704_);
lean_dec(v_snd_1704_);
lean_ctor_set_float(v_data_1725_, sizeof(void*)*3 + 8, v___x_1727_);
lean_ctor_set_uint8(v_data_1725_, sizeof(void*)*3 + 16, v_collapsed_1672_);
v___y_1690_ = v_m_1720_;
v___y_1691_ = v___y_1711_;
v_data_1692_ = v_data_1725_;
goto v___jp_1689_;
}
}
}
}
v___jp_1730_:
{
lean_object* v_ref_1731_; lean_object* v___x_1732_; 
v_ref_1731_ = lean_ctor_get(v___y_1681_, 5);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v_fst_1684_);
v___x_1732_ = lean_apply_6(v_msg_1677_, v_fst_1684_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, lean_box(0));
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref(v___x_1732_);
v___y_1711_ = v_ref_1731_;
v_a_1712_ = v_a_1733_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1734_; 
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3);
v___y_1711_ = v_ref_1731_;
v_a_1712_ = v___x_1734_;
goto v___jp_1710_;
}
}
v___jp_1735_:
{
if (v_clsEnabled_1675_ == 0)
{
if (v___y_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v_traceState_1738_; lean_object* v_env_1739_; lean_object* v_nextMacroScope_1740_; lean_object* v_ngen_1741_; lean_object* v_auxDeclNGen_1742_; lean_object* v_cache_1743_; lean_object* v_messages_1744_; lean_object* v_infoState_1745_; lean_object* v_snapshotTasks_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1706_);
lean_dec(v_snd_1704_);
lean_dec(v_fst_1703_);
lean_del_object(v___x_1687_);
lean_dec_ref(v_msg_1677_);
lean_dec_ref(v_tag_1673_);
lean_dec(v_cls_1671_);
v___x_1737_ = lean_st_ref_take(v___y_1682_);
v_traceState_1738_ = lean_ctor_get(v___x_1737_, 4);
v_env_1739_ = lean_ctor_get(v___x_1737_, 0);
v_nextMacroScope_1740_ = lean_ctor_get(v___x_1737_, 1);
v_ngen_1741_ = lean_ctor_get(v___x_1737_, 2);
v_auxDeclNGen_1742_ = lean_ctor_get(v___x_1737_, 3);
v_cache_1743_ = lean_ctor_get(v___x_1737_, 5);
v_messages_1744_ = lean_ctor_get(v___x_1737_, 6);
v_infoState_1745_ = lean_ctor_get(v___x_1737_, 7);
v_snapshotTasks_1746_ = lean_ctor_get(v___x_1737_, 8);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1748_ = v___x_1737_;
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snapshotTasks_1746_);
lean_inc(v_infoState_1745_);
lean_inc(v_messages_1744_);
lean_inc(v_cache_1743_);
lean_inc(v_traceState_1738_);
lean_inc(v_auxDeclNGen_1742_);
lean_inc(v_ngen_1741_);
lean_inc(v_nextMacroScope_1740_);
lean_inc(v_env_1739_);
lean_dec(v___x_1737_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
uint64_t v_tid_1750_; lean_object* v_traces_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1764_; 
v_tid_1750_ = lean_ctor_get_uint64(v_traceState_1738_, sizeof(void*)*1);
v_traces_1751_ = lean_ctor_get(v_traceState_1738_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_traceState_1738_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1753_ = v_traceState_1738_;
v_isShared_1754_ = v_isSharedCheck_1764_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_traces_1751_);
lean_dec(v_traceState_1738_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1764_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1676_, v_traces_1751_);
lean_dec_ref(v_traces_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1755_);
lean_ctor_set_uint64(v_reuseFailAlloc_1763_, sizeof(void*)*1, v_tid_1750_);
v___x_1757_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v___x_1757_);
v___x_1759_ = v___x_1748_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_env_1739_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_nextMacroScope_1740_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_ngen_1741_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_auxDeclNGen_1742_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v_cache_1743_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_messages_1744_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_infoState_1745_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_snapshotTasks_1746_);
v___x_1759_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_st_ref_set(v___y_1682_, v___x_1759_);
v___x_1761_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_fst_1684_);
return v___x_1761_;
}
}
}
}
}
else
{
goto v___jp_1730_;
}
}
else
{
goto v___jp_1730_;
}
}
v___jp_1766_:
{
double v___x_1768_; double v___x_1769_; double v___x_1770_; uint8_t v___x_1771_; 
v___x_1768_ = lean_unbox_float(v_snd_1704_);
v___x_1769_ = lean_unbox_float(v_fst_1703_);
v___x_1770_ = lean_float_sub(v___x_1768_, v___x_1769_);
v___x_1771_ = lean_float_decLt(v___y_1767_, v___x_1770_);
v___y_1736_ = v___x_1771_;
goto v___jp_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_cls_1784_, lean_object* v_collapsed_1785_, lean_object* v_tag_1786_, lean_object* v_opts_1787_, lean_object* v_clsEnabled_1788_, lean_object* v_oldTraces_1789_, lean_object* v_msg_1790_, lean_object* v_resStartStop_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v_collapsed_boxed_1797_; uint8_t v_clsEnabled_boxed_1798_; lean_object* v_res_1799_; 
v_collapsed_boxed_1797_ = lean_unbox(v_collapsed_1785_);
v_clsEnabled_boxed_1798_ = lean_unbox(v_clsEnabled_1788_);
v_res_1799_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_cls_1784_, v_collapsed_boxed_1797_, v_tag_1786_, v_opts_1787_, v_clsEnabled_boxed_1798_, v_oldTraces_1789_, v_msg_1790_, v_resStartStop_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_opts_1787_);
return v_res_1799_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1800_; double v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(1000000000u);
v___x_1801_ = lean_float_of_nat(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5));
v___x_1807_ = l_Lean_Name_append(v___x_1806_, v___x_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; uint8_t v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v_a_1828_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; uint8_t v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v_a_1853_; lean_object* v___y_1863_; lean_object* v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; uint8_t v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v_lhs_1915_; lean_object* v_rhs_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; 
if (lean_obj_tag(v_x_1808_) == 1)
{
if (lean_obj_tag(v_x_1809_) == 1)
{
lean_object* v_a_1942_; lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1942_ = lean_ctor_get(v_x_1808_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v_x_1808_);
v_a_1943_ = lean_ctor_get(v_x_1809_, 0);
lean_inc(v_a_1943_);
lean_dec_ref(v_x_1809_);
v___x_1944_ = lean_is_level_def_eq(v_a_1942_, v_a_1943_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1944_;
}
else
{
v_lhs_1915_ = v_x_1808_;
v_rhs_1916_ = v_x_1809_;
v___y_1917_ = v_a_1810_;
v___y_1918_ = v_a_1811_;
v___y_1919_ = v_a_1812_;
v___y_1920_ = v_a_1813_;
goto v___jp_1914_;
}
}
else
{
v_lhs_1915_ = v_x_1808_;
v_rhs_1916_ = v_x_1809_;
v___y_1917_ = v_a_1810_;
v___y_1918_ = v_a_1811_;
v___y_1919_ = v_a_1812_;
v___y_1920_ = v_a_1813_;
goto v___jp_1914_;
}
v___jp_1815_:
{
lean_object* v___x_1829_; double v___x_1830_; double v___x_1831_; double v___x_1832_; double v___x_1833_; double v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1829_ = lean_io_mono_nanos_now();
v___x_1830_ = lean_float_of_nat(v___y_1825_);
v___x_1831_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1832_ = lean_float_div(v___x_1830_, v___x_1831_);
v___x_1833_ = lean_float_of_nat(v___x_1829_);
v___x_1834_ = lean_float_div(v___x_1833_, v___x_1831_);
v___x_1835_ = lean_box_float(v___x_1832_);
v___x_1836_ = lean_box_float(v___x_1834_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_a_1828_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_inc_ref(v___y_1819_);
lean_inc(v___y_1822_);
v___x_1839_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1822_, v___y_1820_, v___y_1819_, v___y_1823_, v___y_1821_, v___y_1826_, v___y_1818_, v___x_1838_, v___y_1824_, v___y_1827_, v___y_1817_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v___x_1839_;
}
v___jp_1840_:
{
lean_object* v___x_1854_; double v___x_1855_; double v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1854_ = lean_io_get_num_heartbeats();
v___x_1855_ = lean_float_of_nat(v___y_1851_);
v___x_1856_ = lean_float_of_nat(v___x_1854_);
v___x_1857_ = lean_box_float(v___x_1855_);
v___x_1858_ = lean_box_float(v___x_1856_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v_a_1853_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1847_);
v___x_1861_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1847_, v___y_1845_, v___y_1844_, v___y_1848_, v___y_1846_, v___y_1850_, v___y_1843_, v___x_1860_, v___y_1849_, v___y_1852_, v___y_1842_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v___x_1861_;
}
v___jp_1862_:
{
lean_object* v___x_1874_; lean_object* v_a_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1874_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(v___y_1863_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1877_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1871_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_io_mono_nanos_now();
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
v___x_1879_ = lean_apply_5(v___y_1868_, v___y_1872_, v___y_1873_, v___y_1864_, v___y_1863_, lean_box(0));
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 1);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
v___y_1816_ = v___y_1863_;
v___y_1817_ = v___y_1864_;
v___y_1818_ = v___y_1867_;
v___y_1819_ = v___y_1866_;
v___y_1820_ = v___y_1865_;
v___y_1821_ = v___y_1870_;
v___y_1822_ = v___y_1869_;
v___y_1823_ = v___y_1871_;
v___y_1824_ = v___y_1872_;
v___y_1825_ = v___x_1878_;
v___y_1826_ = v_a_1875_;
v___y_1827_ = v___y_1873_;
v_a_1828_ = v___x_1885_;
goto v___jp_1815_;
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_a_1888_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1879_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1879_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
v___y_1816_ = v___y_1863_;
v___y_1817_ = v___y_1864_;
v___y_1818_ = v___y_1867_;
v___y_1819_ = v___y_1866_;
v___y_1820_ = v___y_1865_;
v___y_1821_ = v___y_1870_;
v___y_1822_ = v___y_1869_;
v___y_1823_ = v___y_1871_;
v___y_1824_ = v___y_1872_;
v___y_1825_ = v___x_1878_;
v___y_1826_ = v_a_1875_;
v___y_1827_ = v___y_1873_;
v_a_1828_ = v___x_1893_;
goto v___jp_1815_;
}
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
v___x_1897_ = lean_apply_5(v___y_1868_, v___y_1872_, v___y_1873_, v___y_1864_, v___y_1863_, lean_box(0));
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 1);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
v___y_1841_ = v___y_1863_;
v___y_1842_ = v___y_1864_;
v___y_1843_ = v___y_1867_;
v___y_1844_ = v___y_1866_;
v___y_1845_ = v___y_1865_;
v___y_1846_ = v___y_1870_;
v___y_1847_ = v___y_1869_;
v___y_1848_ = v___y_1871_;
v___y_1849_ = v___y_1872_;
v___y_1850_ = v_a_1875_;
v___y_1851_ = v___x_1896_;
v___y_1852_ = v___y_1873_;
v_a_1853_ = v___x_1903_;
goto v___jp_1840_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1897_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1897_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 0);
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v___y_1841_ = v___y_1863_;
v___y_1842_ = v___y_1864_;
v___y_1843_ = v___y_1867_;
v___y_1844_ = v___y_1866_;
v___y_1845_ = v___y_1865_;
v___y_1846_ = v___y_1870_;
v___y_1847_ = v___y_1869_;
v___y_1848_ = v___y_1871_;
v___y_1849_ = v___y_1872_;
v___y_1850_ = v_a_1875_;
v___y_1851_ = v___x_1896_;
v___y_1852_ = v___y_1873_;
v_a_1853_ = v___x_1911_;
goto v___jp_1840_;
}
}
}
}
}
v___jp_1914_:
{
lean_object* v_options_1921_; lean_object* v_inheritedTraceOptions_1922_; uint8_t v_hasTrace_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___y_1932_; 
v_options_1921_ = lean_ctor_get(v___y_1919_, 2);
v_inheritedTraceOptions_1922_ = lean_ctor_get(v___y_1919_, 13);
v_hasTrace_1923_ = lean_ctor_get_uint8(v_options_1921_, sizeof(void*)*1);
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_1926_ = l_Lean_Level_getLevelOffset(v_lhs_1915_);
v___x_1927_ = l_Lean_Level_getLevelOffset(v_rhs_1916_);
v___x_1928_ = lean_level_eq(v___x_1926_, v___x_1927_);
lean_dec(v___x_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = 1;
v___x_1930_ = lean_box(v___x_1928_);
v___x_1931_ = lean_box(v___x_1929_);
lean_inc(v_rhs_1916_);
lean_inc(v_lhs_1915_);
v___y_1932_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1932_, 0, v___x_1930_);
lean_closure_set(v___y_1932_, 1, v_lhs_1915_);
lean_closure_set(v___y_1932_, 2, v_rhs_1916_);
lean_closure_set(v___y_1932_, 3, v___x_1924_);
lean_closure_set(v___y_1932_, 4, v___x_1925_);
lean_closure_set(v___y_1932_, 5, v___x_1931_);
if (v_hasTrace_1923_ == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref(v___y_1932_);
v___x_1933_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1928_, v_lhs_1915_, v_rhs_1916_, v___x_1924_, v___x_1925_, v___x_1929_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v___x_1933_;
}
else
{
lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
lean_inc(v_rhs_1916_);
lean_inc(v_lhs_1915_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1934_, 0, v_lhs_1915_);
lean_closure_set(v___f_1934_, 1, v_rhs_1916_);
v___x_1935_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_1936_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___closed__1));
v___x_1937_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1938_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1922_, v_options_1921_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = l_Lean_trace_profiler;
v___x_1940_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_options_1921_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref(v___f_1934_);
lean_dec_ref(v___y_1932_);
v___x_1941_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1928_, v_lhs_1915_, v_rhs_1916_, v___x_1924_, v___x_1925_, v___x_1929_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v___x_1941_;
}
else
{
lean_inc_ref(v_options_1921_);
lean_dec(v_rhs_1916_);
lean_dec(v_lhs_1915_);
v___y_1863_ = v___y_1920_;
v___y_1864_ = v___y_1919_;
v___y_1865_ = v___x_1929_;
v___y_1866_ = v___x_1936_;
v___y_1867_ = v___f_1934_;
v___y_1868_ = v___y_1932_;
v___y_1869_ = v___x_1935_;
v___y_1870_ = v___x_1938_;
v___y_1871_ = v_options_1921_;
v___y_1872_ = v___y_1917_;
v___y_1873_ = v___y_1918_;
goto v___jp_1862_;
}
}
else
{
lean_inc_ref(v_options_1921_);
lean_dec(v_rhs_1916_);
lean_dec(v_lhs_1915_);
v___y_1863_ = v___y_1920_;
v___y_1864_ = v___y_1919_;
v___y_1865_ = v___x_1929_;
v___y_1866_ = v___x_1936_;
v___y_1867_ = v___f_1934_;
v___y_1868_ = v___y_1932_;
v___y_1869_ = v___x_1935_;
v___y_1870_ = v___x_1938_;
v___y_1871_ = v_options_1921_;
v___y_1872_ = v___y_1917_;
v___y_1873_ = v___y_1918_;
goto v___jp_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = lean_is_level_def_eq(v_x_1945_, v_x_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7(lean_object* v_00_u03b1_1953_, lean_object* v_x_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_x_1954_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7(v_00_u03b1_1961_, v_x_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(v_x_1970_, v_x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4(v_00_u03b2_1973_, v_x_1974_, v_x_1975_);
lean_dec(v_x_1975_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1977_, lean_object* v_x_1978_, size_t v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(v_x_1978_, v_x_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
size_t v_x_14891__boxed_1986_; lean_object* v_res_1987_; 
v_x_14891__boxed_1986_ = lean_unbox_usize(v_x_1984_);
lean_dec(v_x_1984_);
v_res_1987_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9(v_00_u03b2_1982_, v_x_1983_, v_x_14891__boxed_1986_, v_x_1985_);
lean_dec(v_x_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_1988_, lean_object* v_keys_1989_, lean_object* v_vals_1990_, lean_object* v_heq_1991_, lean_object* v_i_1992_, lean_object* v_k_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(v_keys_1989_, v_vals_1990_, v_i_1992_, v_k_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b2_1995_, lean_object* v_keys_1996_, lean_object* v_vals_1997_, lean_object* v_heq_1998_, lean_object* v_i_1999_, lean_object* v_k_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12(v_00_u03b2_1995_, v_keys_1996_, v_vals_1997_, v_heq_1998_, v_i_1999_, v_k_2000_);
lean_dec(v_k_2000_);
lean_dec_ref(v_vals_1997_);
lean_dec_ref(v_keys_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2058_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_2059_ = 0;
v___x_2060_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2061_ = l_Lean_registerTraceClass(v___x_2058_, v___x_2059_, v___x_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
lean_dec_ref(v___x_2061_);
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_2063_ = 1;
v___x_2064_ = l_Lean_registerTraceClass(v___x_2062_, v___x_2063_, v___x_2060_);
return v___x_2064_;
}
else
{
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2066_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
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
