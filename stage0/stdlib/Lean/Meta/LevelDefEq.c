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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
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
lean_object* v___f_47_; lean_object* v___x_218__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_218__overap_48_ = lean_panic_fn(v___f_47_, v_msg_41_);
v___x_49_ = lean_apply_5(v___x_218__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(lean_object* v_msg_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v_msg_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
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
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec_ref(v_a_267_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v___x_277_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_265_, v_v_266_, v_a_276_);
v___x_278_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_265_, v___x_277_, v_a_268_);
lean_dec(v_a_268_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v_a_268_);
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
size_t v_x_1046__boxed_329_; size_t v_x_1047__boxed_330_; lean_object* v_res_331_; 
v_x_1046__boxed_329_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_x_1047__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_323_, v_x_324_, v_x_1046__boxed_329_, v_x_1047__boxed_330_, v_x_327_, v_x_328_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(lean_object* v_cls_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_options_542_; uint8_t v_hasTrace_543_; 
v_options_542_ = lean_ctor_get(v___y_540_, 2);
v_hasTrace_543_ = lean_ctor_get_uint8(v_options_542_, sizeof(void*)*1);
if (v_hasTrace_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_cls_539_);
v___x_544_ = lean_box(v_hasTrace_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v_inheritedTraceOptions_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_inheritedTraceOptions_546_ = lean_ctor_get(v___y_540_, 13);
v___x_547_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___closed__1));
v___x_548_ = l_Lean_Name_append(v___x_547_, v_cls_539_);
v___x_549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_546_, v_options_542_, v___x_548_);
lean_dec(v___x_548_);
v___x_550_ = lean_box(v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg___boxed(lean_object* v_cls_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(v_cls_552_, v___y_553_);
lean_dec_ref(v___y_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(lean_object* v_cls_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(v_cls_556_, v___y_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___boxed(lean_object* v_cls_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0(v_cls_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1(lean_object* v_msgData_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; lean_object* v_env_577_; lean_object* v___x_578_; lean_object* v_mctx_579_; lean_object* v_lctx_580_; lean_object* v_options_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_576_ = lean_st_ref_get(v___y_574_);
v_env_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_ref(v_env_577_);
lean_dec(v___x_576_);
v___x_578_ = lean_st_ref_get(v___y_572_);
v_mctx_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_mctx_579_);
lean_dec(v___x_578_);
v_lctx_580_ = lean_ctor_get(v___y_571_, 2);
v_options_581_ = lean_ctor_get(v___y_573_, 2);
lean_inc_ref(v_options_581_);
lean_inc_ref(v_lctx_580_);
v___x_582_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_582_, 0, v_env_577_);
lean_ctor_set(v___x_582_, 1, v_mctx_579_);
lean_ctor_set(v___x_582_, 2, v_lctx_580_);
lean_ctor_set(v___x_582_, 3, v_options_581_);
v___x_583_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_msgData_570_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1___boxed(lean_object* v_msgData_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1(v_msgData_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_591_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_592_; double v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_float_of_nat(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1(lean_object* v_cls_597_, lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_ref_604_; lean_object* v___x_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_650_; 
v_ref_604_ = lean_ctor_get(v___y_601_, 5);
v___x_605_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_650_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_650_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_650_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v_traceState_611_; lean_object* v_env_612_; lean_object* v_nextMacroScope_613_; lean_object* v_ngen_614_; lean_object* v_auxDeclNGen_615_; lean_object* v_cache_616_; lean_object* v_messages_617_; lean_object* v_infoState_618_; lean_object* v_snapshotTasks_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_649_; 
v___x_610_ = lean_st_ref_take(v___y_602_);
v_traceState_611_ = lean_ctor_get(v___x_610_, 4);
v_env_612_ = lean_ctor_get(v___x_610_, 0);
v_nextMacroScope_613_ = lean_ctor_get(v___x_610_, 1);
v_ngen_614_ = lean_ctor_get(v___x_610_, 2);
v_auxDeclNGen_615_ = lean_ctor_get(v___x_610_, 3);
v_cache_616_ = lean_ctor_get(v___x_610_, 5);
v_messages_617_ = lean_ctor_get(v___x_610_, 6);
v_infoState_618_ = lean_ctor_get(v___x_610_, 7);
v_snapshotTasks_619_ = lean_ctor_get(v___x_610_, 8);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_649_ == 0)
{
v___x_621_ = v___x_610_;
v_isShared_622_ = v_isSharedCheck_649_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snapshotTasks_619_);
lean_inc(v_infoState_618_);
lean_inc(v_messages_617_);
lean_inc(v_cache_616_);
lean_inc(v_traceState_611_);
lean_inc(v_auxDeclNGen_615_);
lean_inc(v_ngen_614_);
lean_inc(v_nextMacroScope_613_);
lean_inc(v_env_612_);
lean_dec(v___x_610_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_649_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint64_t v_tid_623_; lean_object* v_traces_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_648_; 
v_tid_623_ = lean_ctor_get_uint64(v_traceState_611_, sizeof(void*)*1);
v_traces_624_ = lean_ctor_get(v_traceState_611_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_traceState_611_);
if (v_isSharedCheck_648_ == 0)
{
v___x_626_ = v_traceState_611_;
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_traces_624_);
lean_dec(v_traceState_611_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; double v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_628_ = lean_box(0);
v___x_629_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0);
v___x_630_ = 0;
v___x_631_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__1));
v___x_632_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_632_, 0, v_cls_597_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3, v___x_629_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3 + 8, v___x_629_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 16, v___x_630_);
v___x_633_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__2));
v___x_634_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v_a_606_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_inc(v_ref_604_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_ref_604_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_PersistentArray_push___redArg(v_traces_624_, v___x_635_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_636_);
v___x_638_ = v___x_626_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_636_);
lean_ctor_set_uint64(v_reuseFailAlloc_647_, sizeof(void*)*1, v_tid_623_);
v___x_638_ = v_reuseFailAlloc_647_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___x_638_);
v___x_640_ = v___x_621_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_env_612_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_nextMacroScope_613_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_ngen_614_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_auxDeclNGen_615_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 5, v_cache_616_);
lean_ctor_set(v_reuseFailAlloc_646_, 6, v_messages_617_);
lean_ctor_set(v_reuseFailAlloc_646_, 7, v_infoState_618_);
lean_ctor_set(v_reuseFailAlloc_646_, 8, v_snapshotTasks_619_);
v___x_640_ = v_reuseFailAlloc_646_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_641_ = lean_st_ref_set(v___y_602_, v___x_640_);
v___x_642_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_642_);
v___x_644_ = v___x_608_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___boxed(lean_object* v_cls_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1(v_cls_651_, v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_658_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_669_, lean_object* v_rhs_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_ref_676_; lean_object* v___y_678_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_a_700_; uint8_t v___x_701_; 
v_ref_676_ = lean_ctor_get(v_a_673_, 5);
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_699_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(v___x_698_, v_a_673_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
v___x_701_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
if (v___x_701_ == 0)
{
v___y_678_ = v_a_672_;
goto v___jp_677_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc(v_lhs_669_);
v___x_702_ = l_Lean_MessageData_ofLevel(v_lhs_669_);
v___x_703_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
lean_inc(v_rhs_670_);
v___x_705_ = l_Lean_MessageData_ofLevel(v_rhs_670_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1(v___x_698_, v___x_706_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_dec_ref(v___x_707_);
v___y_678_ = v_a_672_;
goto v___jp_677_;
}
else
{
lean_dec(v_rhs_670_);
lean_dec(v_lhs_669_);
return v___x_707_;
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v_mctx_680_; lean_object* v_cache_681_; lean_object* v_zetaDeltaFVarIds_682_; lean_object* v_postponed_683_; lean_object* v_diag_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_697_; 
v___x_679_ = lean_st_ref_take(v___y_678_);
v_mctx_680_ = lean_ctor_get(v___x_679_, 0);
v_cache_681_ = lean_ctor_get(v___x_679_, 1);
v_zetaDeltaFVarIds_682_ = lean_ctor_get(v___x_679_, 2);
v_postponed_683_ = lean_ctor_get(v___x_679_, 3);
v_diag_684_ = lean_ctor_get(v___x_679_, 4);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_697_ == 0)
{
v___x_686_ = v___x_679_;
v_isShared_687_ = v_isSharedCheck_697_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_diag_684_);
lean_inc(v_postponed_683_);
lean_inc(v_zetaDeltaFVarIds_682_);
lean_inc(v_cache_681_);
lean_inc(v_mctx_680_);
lean_dec(v___x_679_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_697_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_defEqCtx_x3f_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v_defEqCtx_x3f_688_ = lean_ctor_get(v_a_671_, 4);
lean_inc(v_defEqCtx_x3f_688_);
lean_inc(v_ref_676_);
v___x_689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_689_, 0, v_ref_676_);
lean_ctor_set(v___x_689_, 1, v_lhs_669_);
lean_ctor_set(v___x_689_, 2, v_rhs_670_);
lean_ctor_set(v___x_689_, 3, v_defEqCtx_x3f_688_);
v___x_690_ = l_Lean_PersistentArray_push___redArg(v_postponed_683_, v___x_689_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v___x_690_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_mctx_680_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_cache_681_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_zetaDeltaFVarIds_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_diag_684_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_st_ref_set(v___y_678_, v___x_692_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_708_, lean_object* v_rhs_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_708_, v_rhs_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_716_, lean_object* v_mvarId_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
if (lean_obj_tag(v_v_716_) == 5)
{
lean_object* v_a_723_; lean_object* v___x_724_; 
v_a_723_ = lean_ctor_get(v_v_716_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v_v_716_);
v___x_724_ = l_Lean_LMVarId_getLevel(v_a_723_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
v___x_726_ = l_Lean_LMVarId_getLevel(v_mvarId_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_736_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_731_ = lean_nat_dec_lt(v_a_727_, v_a_725_);
lean_dec(v_a_725_);
lean_dec(v_a_727_);
v___x_732_ = lean_box(v___x_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_a_725_);
v_a_737_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_726_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_726_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_mvarId_717_);
v_a_745_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_724_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_724_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_mvarId_717_);
lean_dec(v_v_716_);
v___x_753_ = 0;
v___x_754_ = lean_box(v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_756_, lean_object* v_mvarId_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_756_, v_mvarId_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_764_, lean_object* v_v_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___y_772_; lean_object* v___y_801_; lean_object* v___y_802_; 
switch(lean_obj_tag(v_u_764_))
{
case 5:
{
lean_object* v_a_844_; lean_object* v___x_845_; 
v_a_844_ = lean_ctor_get(v_u_764_, 0);
lean_inc(v_a_844_);
v___x_845_ = l_Lean_LMVarId_isReadOnly(v_a_844_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_926_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_926_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_926_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_926_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v___x_850_; 
v___x_850_ = lean_unbox(v_a_846_);
lean_dec(v_a_846_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_del_object(v___x_848_);
lean_inc(v_a_844_);
lean_inc(v_v_765_);
v___x_851_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_765_, v_a_844_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_912_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_912_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_912_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_912_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___y_863_; uint8_t v___x_884_; 
v___x_884_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_Level_occurs(v_u_764_, v_v_765_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_854_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec_ref(v_a_766_);
v___x_886_ = l_Lean_Level_mvarId_x21(v_u_764_);
lean_dec_ref(v_u_764_);
v___x_887_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_886_, v_v_765_, v_a_767_);
lean_dec(v_a_767_);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_887_, 0);
lean_dec(v_unused_897_);
v___x_889_ = v___x_887_;
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
else
{
lean_dec(v___x_887_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = 1;
v___x_892_ = lean_box(v___x_891_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_Level_isMax(v_v_765_);
if (v___x_898_ == 0)
{
v___y_863_ = v___x_898_;
goto v___jp_862_;
}
else
{
uint8_t v___x_899_; 
v___x_899_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_764_, v_v_765_);
if (v___x_899_ == 0)
{
v___y_863_ = v___x_898_;
goto v___jp_862_;
}
else
{
lean_dec_ref(v_u_764_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
goto v___jp_856_;
}
}
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_854_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec_ref(v_a_766_);
v___x_900_ = l_Lean_Level_mvarId_x21(v_v_765_);
lean_dec(v_v_765_);
v___x_901_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_900_, v_u_764_, v_a_767_);
lean_dec(v_a_767_);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_901_, 0);
lean_dec(v_unused_911_);
v___x_903_ = v___x_901_;
v_isShared_904_ = v_isSharedCheck_910_;
goto v_resetjp_902_;
}
else
{
lean_dec(v___x_901_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_910_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_905_ = 1;
v___x_906_ = lean_box(v___x_905_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_906_);
v___x_908_ = v___x_903_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
v___jp_856_:
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = 2;
v___x_858_ = lean_box(v___x_857_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_858_);
v___x_860_ = v___x_854_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
v___jp_862_:
{
if (v___y_863_ == 0)
{
lean_dec_ref(v_u_764_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
goto v___jp_856_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_del_object(v___x_854_);
v___x_864_ = l_Lean_Level_mvarId_x21(v_u_764_);
lean_dec_ref(v_u_764_);
v___x_865_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_864_, v_v_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_874_; 
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_865_, 0);
lean_dec(v_unused_875_);
v___x_867_ = v___x_865_;
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
else
{
lean_dec(v___x_865_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = 1;
v___x_870_ = lean_box(v___x_869_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_865_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_865_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_u_764_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
v_a_913_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_851_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_851_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
lean_dec_ref(v_u_764_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
v___x_921_ = 2;
v___x_922_ = lean_box(v___x_921_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_922_);
v___x_924_ = v___x_848_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_u_764_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
v_a_927_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_845_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_845_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_765_))
{
case 5:
{
lean_dec_ref(v_v_765_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
goto v___jp_792_;
}
case 2:
{
lean_object* v_a_935_; lean_object* v_a_936_; lean_object* v___x_937_; 
v_a_935_ = lean_ctor_get(v_v_765_, 0);
lean_inc(v_a_935_);
v_a_936_ = lean_ctor_get(v_v_765_, 1);
lean_inc(v_a_936_);
lean_dec_ref(v_v_765_);
lean_inc(v_a_769_);
lean_inc_ref(v_a_768_);
lean_inc(v_a_767_);
lean_inc_ref(v_a_766_);
v___x_937_ = lean_is_level_def_eq(v_u_764_, v_a_935_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; uint8_t v___x_939_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
v___x_939_ = lean_unbox(v_a_938_);
lean_dec(v_a_938_);
if (v___x_939_ == 0)
{
lean_dec(v_a_936_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
v___y_772_ = v___x_937_;
goto v___jp_771_;
}
else
{
lean_object* v___x_940_; 
lean_dec_ref(v___x_937_);
v___x_940_ = lean_is_level_def_eq(v_u_764_, v_a_936_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
v___y_772_ = v___x_940_;
goto v___jp_771_;
}
}
else
{
lean_dec(v_a_936_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
v___y_772_ = v___x_937_;
goto v___jp_771_;
}
}
case 3:
{
lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_941_ = lean_ctor_get(v_v_765_, 1);
lean_inc(v_a_941_);
lean_dec_ref(v_v_765_);
v___x_942_ = lean_is_level_def_eq(v_u_764_, v_a_941_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_953_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_953_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_947_ = lean_unbox(v_a_943_);
lean_dec(v_a_943_);
v___x_948_ = l_Bool_toLBool(v___x_947_);
v___x_949_ = lean_box(v___x_948_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_951_ = v___x_945_;
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
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_942_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_942_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
case 1:
{
uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v_v_765_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
v___x_962_ = 0;
v___x_963_ = lean_box(v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
default: 
{
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
v___y_801_ = v_a_766_;
v___y_802_ = v_a_767_;
goto v___jp_800_;
}
}
}
case 1:
{
lean_object* v_a_965_; uint8_t v___y_967_; 
v_a_965_ = lean_ctor_get(v_u_764_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v_u_764_);
if (lean_obj_tag(v_v_765_) == 5)
{
lean_dec_ref(v_v_765_);
lean_dec(v_a_965_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
goto v___jp_792_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Level_isParam(v_v_765_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_Level_isMVar(v_a_965_);
if (v___x_1012_ == 0)
{
v___y_967_ = v___x_1012_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_Level_occurs(v_a_965_, v_v_765_);
v___y_967_ = v___x_1013_;
goto v___jp_966_;
}
}
else
{
uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_a_965_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
v___x_1014_ = 0;
v___x_1015_ = lean_box(v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
v___jp_966_:
{
if (v___y_967_ == 0)
{
lean_object* v___x_968_; 
lean_inc(v_a_769_);
lean_inc_ref(v_a_768_);
lean_inc(v_a_767_);
lean_inc_ref(v_a_766_);
v___x_968_ = l_Lean_Meta_decLevel_x3f(v_v_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_999_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_999_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
if (lean_obj_tag(v_a_969_) == 0)
{
uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
lean_dec(v_a_965_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
v___x_973_ = 2;
v___x_974_ = lean_box(v___x_973_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; 
lean_del_object(v___x_971_);
v_val_978_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_val_978_);
lean_dec_ref(v_a_969_);
v___x_979_ = lean_is_level_def_eq(v_a_965_, v_val_978_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_990_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_990_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_984_ = lean_unbox(v_a_980_);
lean_dec(v_a_980_);
v___x_985_ = l_Bool_toLBool(v___x_984_);
v___x_986_ = lean_box(v___x_985_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_986_);
v___x_988_ = v___x_982_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_979_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_979_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_a_965_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
v_a_1000_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_968_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_968_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec(v_a_965_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_v_765_);
v___x_1008_ = 2;
v___x_1009_ = lean_box(v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
default: 
{
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
if (lean_obj_tag(v_v_765_) == 5)
{
lean_dec_ref(v_v_765_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_u_764_);
goto v___jp_792_;
}
else
{
v___y_801_ = v_a_766_;
v___y_802_ = v_a_767_;
goto v___jp_800_;
}
}
}
v___jp_771_:
{
if (lean_obj_tag(v___y_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_783_; 
v_a_773_ = lean_ctor_get(v___y_772_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___y_772_);
if (v_isSharedCheck_783_ == 0)
{
v___x_775_ = v___y_772_;
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___y_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
uint8_t v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_777_ = lean_unbox(v_a_773_);
lean_dec(v_a_773_);
v___x_778_ = l_Bool_toLBool(v___x_777_);
v___x_779_ = lean_box(v___x_778_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_779_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_784_ = lean_ctor_get(v___y_772_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___y_772_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___y_772_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___y_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
v___jp_792_:
{
uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = 2;
v___x_794_ = lean_box(v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
v___jp_796_:
{
uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = 2;
v___x_798_ = lean_box(v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
v___jp_800_:
{
uint8_t v_univApprox_803_; 
v_univApprox_803_ = lean_ctor_get_uint8(v___y_801_, sizeof(void*)*7 + 1);
lean_dec_ref(v___y_801_);
if (v_univApprox_803_ == 0)
{
lean_dec(v___y_802_);
lean_dec(v_v_765_);
lean_dec(v_u_764_);
goto v___jp_796_;
}
else
{
lean_object* v___x_804_; 
lean_inc(v_v_765_);
lean_inc(v_u_764_);
v___x_804_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___redArg(v_u_764_, v_v_765_, v___y_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_835_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_835_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_835_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_835_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v___x_809_; 
v___x_809_ = lean_unbox(v_a_805_);
lean_dec(v_a_805_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_del_object(v___x_807_);
v___x_810_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___redArg(v_u_764_, v_v_765_, v___y_802_);
lean_dec(v___y_802_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_821_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_821_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; 
v___x_815_ = lean_unbox(v_a_811_);
lean_dec(v_a_811_);
if (v___x_815_ == 0)
{
lean_del_object(v___x_813_);
goto v___jp_796_;
}
else
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_816_ = 1;
v___x_817_ = lean_box(v___x_816_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_810_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_810_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v___y_802_);
lean_dec(v_v_765_);
lean_dec(v_u_764_);
v___x_830_ = 1;
v___x_831_ = lean_box(v___x_830_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_831_);
v___x_833_ = v___x_807_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec(v___y_802_);
lean_dec(v_v_765_);
lean_dec(v_u_764_);
v_a_836_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_804_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_804_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1017_, lean_object* v_v_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1017_, v_v_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v_mctx_1029_; lean_object* v___x_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1033_; lean_object* v_cache_1034_; lean_object* v_zetaDeltaFVarIds_1035_; lean_object* v_postponed_1036_; lean_object* v_diag_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1046_; 
v___x_1028_ = lean_st_ref_get(v___y_1026_);
v_mctx_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_mctx_1029_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_instantiate_level_mvars(v_mctx_1029_, v_l_1025_);
v_fst_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_fst_1031_);
v_snd_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_snd_1032_);
lean_dec_ref(v___x_1030_);
v___x_1033_ = lean_st_ref_take(v___y_1026_);
v_cache_1034_ = lean_ctor_get(v___x_1033_, 1);
v_zetaDeltaFVarIds_1035_ = lean_ctor_get(v___x_1033_, 2);
v_postponed_1036_ = lean_ctor_get(v___x_1033_, 3);
v_diag_1037_ = lean_ctor_get(v___x_1033_, 4);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___x_1033_, 0);
lean_dec(v_unused_1047_);
v___x_1039_ = v___x_1033_;
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_diag_1037_);
lean_inc(v_postponed_1036_);
lean_inc(v_zetaDeltaFVarIds_1035_);
lean_inc(v_cache_1034_);
lean_dec(v___x_1033_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_fst_1031_);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_fst_1031_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_cache_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_zetaDeltaFVarIds_1035_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_postponed_1036_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_diag_1037_);
v___x_1042_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_st_ref_set(v___y_1026_, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v_snd_1032_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1048_, v___y_1049_);
lean_dec(v___y_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1052_, v___y_1054_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1065_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_unsigned_to_nat(32u);
v___x_1067_ = lean_mk_empty_array_with_capacity(v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1069_ = ((size_t)5ULL);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_unsigned_to_nat(32u);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_1071_);
v___x_1073_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__0);
v___x_1074_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
lean_ctor_set(v___x_1074_, 2, v___x_1070_);
lean_ctor_set(v___x_1074_, 3, v___x_1070_);
lean_ctor_set_usize(v___x_1074_, 4, v___x_1069_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_traceState_1078_; lean_object* v_traces_1079_; lean_object* v___x_1080_; lean_object* v_traceState_1081_; lean_object* v_env_1082_; lean_object* v_nextMacroScope_1083_; lean_object* v_ngen_1084_; lean_object* v_auxDeclNGen_1085_; lean_object* v_cache_1086_; lean_object* v_messages_1087_; lean_object* v_infoState_1088_; lean_object* v_snapshotTasks_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1108_; 
v___x_1077_ = lean_st_ref_get(v___y_1075_);
v_traceState_1078_ = lean_ctor_get(v___x_1077_, 4);
lean_inc_ref(v_traceState_1078_);
lean_dec(v___x_1077_);
v_traces_1079_ = lean_ctor_get(v_traceState_1078_, 0);
lean_inc_ref(v_traces_1079_);
lean_dec_ref(v_traceState_1078_);
v___x_1080_ = lean_st_ref_take(v___y_1075_);
v_traceState_1081_ = lean_ctor_get(v___x_1080_, 4);
v_env_1082_ = lean_ctor_get(v___x_1080_, 0);
v_nextMacroScope_1083_ = lean_ctor_get(v___x_1080_, 1);
v_ngen_1084_ = lean_ctor_get(v___x_1080_, 2);
v_auxDeclNGen_1085_ = lean_ctor_get(v___x_1080_, 3);
v_cache_1086_ = lean_ctor_get(v___x_1080_, 5);
v_messages_1087_ = lean_ctor_get(v___x_1080_, 6);
v_infoState_1088_ = lean_ctor_get(v___x_1080_, 7);
v_snapshotTasks_1089_ = lean_ctor_get(v___x_1080_, 8);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1091_ = v___x_1080_;
v_isShared_1092_ = v_isSharedCheck_1108_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snapshotTasks_1089_);
lean_inc(v_infoState_1088_);
lean_inc(v_messages_1087_);
lean_inc(v_cache_1086_);
lean_inc(v_traceState_1081_);
lean_inc(v_auxDeclNGen_1085_);
lean_inc(v_ngen_1084_);
lean_inc(v_nextMacroScope_1083_);
lean_inc(v_env_1082_);
lean_dec(v___x_1080_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1108_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
uint64_t v_tid_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1106_; 
v_tid_1093_ = lean_ctor_get_uint64(v_traceState_1081_, sizeof(void*)*1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_traceState_1081_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v_traceState_1081_, 0);
lean_dec(v_unused_1107_);
v___x_1095_ = v_traceState_1081_;
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v_traceState_1081_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___closed__1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1097_);
lean_ctor_set_uint64(v_reuseFailAlloc_1105_, sizeof(void*)*1, v_tid_1093_);
v___x_1099_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1099_);
v___x_1101_ = v___x_1091_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_env_1082_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_nextMacroScope_1083_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_ngen_1084_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_auxDeclNGen_1085_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1104_, 5, v_cache_1086_);
lean_ctor_set(v_reuseFailAlloc_1104_, 6, v_messages_1087_);
lean_ctor_set(v_reuseFailAlloc_1104_, 7, v_infoState_1088_);
lean_ctor_set(v_reuseFailAlloc_1104_, 8, v_snapshotTasks_1089_);
v___x_1101_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_st_ref_set(v___y_1075_, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_traces_1079_);
return v___x_1103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg___boxed(lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(v___y_1109_);
lean_dec(v___y_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1124_, lean_object* v_opt_1125_){
_start:
{
lean_object* v_name_1126_; lean_object* v_defValue_1127_; lean_object* v_map_1128_; lean_object* v___x_1129_; 
v_name_1126_ = lean_ctor_get(v_opt_1125_, 0);
v_defValue_1127_ = lean_ctor_get(v_opt_1125_, 1);
v_map_1128_ = lean_ctor_get(v_opts_1124_, 0);
v___x_1129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1128_, v_name_1126_);
if (lean_obj_tag(v___x_1129_) == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_unbox(v_defValue_1127_);
return v___x_1130_;
}
else
{
lean_object* v_val_1131_; 
v_val_1131_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1131_);
lean_dec_ref(v___x_1129_);
if (lean_obj_tag(v_val_1131_) == 1)
{
uint8_t v_v_1132_; 
v_v_1132_ = lean_ctor_get_uint8(v_val_1131_, 0);
lean_dec_ref(v_val_1131_);
return v_v_1132_;
}
else
{
uint8_t v___x_1133_; 
lean_dec(v_val_1131_);
v___x_1133_ = lean_unbox(v_defValue_1127_);
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1134_, lean_object* v_opt_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1134_, v_opt_1135_);
lean_dec_ref(v_opt_1135_);
lean_dec_ref(v_opts_1134_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(lean_object* v_msg_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_toApplicative_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1213_; 
v___x_1149_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__0);
v___x_1150_ = l_ReaderT_instMonad___redArg(v___x_1149_);
v_toApplicative_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1150_, 1);
lean_dec(v_unused_1214_);
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1213_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_toApplicative_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1213_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_toFunctor_1155_; lean_object* v_toSeq_1156_; lean_object* v_toSeqLeft_1157_; lean_object* v_toSeqRight_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1211_; 
v_toFunctor_1155_ = lean_ctor_get(v_toApplicative_1151_, 0);
v_toSeq_1156_ = lean_ctor_get(v_toApplicative_1151_, 2);
v_toSeqLeft_1157_ = lean_ctor_get(v_toApplicative_1151_, 3);
v_toSeqRight_1158_ = lean_ctor_get(v_toApplicative_1151_, 4);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_toApplicative_1151_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_toApplicative_1151_, 1);
lean_dec(v_unused_1212_);
v___x_1160_ = v_toApplicative_1151_;
v_isShared_1161_ = v_isSharedCheck_1211_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_toSeqRight_1158_);
lean_inc(v_toSeqLeft_1157_);
lean_inc(v_toSeq_1156_);
lean_inc(v_toFunctor_1155_);
lean_dec(v_toApplicative_1151_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1211_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___x_1171_; 
v___f_1162_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__1));
v___f_1163_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__2));
lean_inc_ref(v_toFunctor_1155_);
v___f_1164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1164_, 0, v_toFunctor_1155_);
v___f_1165_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1165_, 0, v_toFunctor_1155_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___f_1164_);
lean_ctor_set(v___x_1166_, 1, v___f_1165_);
v___f_1167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1167_, 0, v_toSeqRight_1158_);
v___f_1168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1168_, 0, v_toSeqLeft_1157_);
v___f_1169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1169_, 0, v_toSeq_1156_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v___f_1167_);
lean_ctor_set(v___x_1160_, 3, v___f_1168_);
lean_ctor_set(v___x_1160_, 2, v___f_1169_);
lean_ctor_set(v___x_1160_, 1, v___f_1162_);
lean_ctor_set(v___x_1160_, 0, v___x_1166_);
v___x_1171_ = v___x_1160_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___f_1162_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v___f_1169_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v___f_1168_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v___f_1167_);
v___x_1171_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___f_1163_);
lean_ctor_set(v___x_1153_, 0, v___x_1171_);
v___x_1173_ = v___x_1153_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___f_1163_);
v___x_1173_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v_toApplicative_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1207_; 
v___x_1174_ = l_ReaderT_instMonad___redArg(v___x_1173_);
v_toApplicative_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1174_, 1);
lean_dec(v_unused_1208_);
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1207_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_toApplicative_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1207_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_toFunctor_1179_; lean_object* v_toSeq_1180_; lean_object* v_toSeqLeft_1181_; lean_object* v_toSeqRight_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1205_; 
v_toFunctor_1179_ = lean_ctor_get(v_toApplicative_1175_, 0);
v_toSeq_1180_ = lean_ctor_get(v_toApplicative_1175_, 2);
v_toSeqLeft_1181_ = lean_ctor_get(v_toApplicative_1175_, 3);
v_toSeqRight_1182_ = lean_ctor_get(v_toApplicative_1175_, 4);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_toApplicative_1175_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_toApplicative_1175_, 1);
lean_dec(v_unused_1206_);
v___x_1184_ = v_toApplicative_1175_;
v_isShared_1185_ = v_isSharedCheck_1205_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_toSeqRight_1182_);
lean_inc(v_toSeqLeft_1181_);
lean_inc(v_toSeq_1180_);
lean_inc(v_toFunctor_1179_);
lean_dec(v_toApplicative_1175_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1205_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___f_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1195_; 
v___f_1186_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__3));
v___f_1187_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___closed__4));
lean_inc_ref(v_toFunctor_1179_);
v___f_1188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1188_, 0, v_toFunctor_1179_);
v___f_1189_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1189_, 0, v_toFunctor_1179_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___f_1188_);
lean_ctor_set(v___x_1190_, 1, v___f_1189_);
v___f_1191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1191_, 0, v_toSeqRight_1182_);
v___f_1192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1192_, 0, v_toSeqLeft_1181_);
v___f_1193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1193_, 0, v_toSeq_1180_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 4, v___f_1191_);
lean_ctor_set(v___x_1184_, 3, v___f_1192_);
lean_ctor_set(v___x_1184_, 2, v___f_1193_);
lean_ctor_set(v___x_1184_, 1, v___f_1186_);
lean_ctor_set(v___x_1184_, 0, v___x_1190_);
v___x_1195_ = v___x_1184_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___f_1186_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v___f_1193_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___f_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___f_1191_);
v___x_1195_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___f_1187_);
lean_ctor_set(v___x_1177_, 0, v___x_1195_);
v___x_1197_ = v___x_1177_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___f_1187_);
v___x_1197_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_11819__overap_1201_; lean_object* v___x_1202_; 
v___x_1198_ = 0;
v___x_1199_ = lean_box(v___x_1198_);
v___x_1200_ = l_instInhabitedOfMonad___redArg(v___x_1197_, v___x_1199_);
v___x_11819__overap_1201_ = lean_panic_fn(v___x_1200_, v_msg_1143_);
v___x_1202_ = lean_apply_5(v___x_11819__overap_1201_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, lean_box(0));
return v___x_1202_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5___boxed(lean_object* v_msg_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(v_msg_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(lean_object* v_keys_1222_, lean_object* v_vals_1223_, lean_object* v_i_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_array_get_size(v_keys_1222_);
v___x_1227_ = lean_nat_dec_lt(v_i_1224_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
lean_dec(v_i_1224_);
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
else
{
lean_object* v_k_x27_1229_; uint8_t v___x_1230_; 
v_k_x27_1229_ = lean_array_fget_borrowed(v_keys_1222_, v_i_1224_);
v___x_1230_ = l_Lean_instBEqLevelMVarId_beq(v_k_1225_, v_k_x27_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_i_1224_, v___x_1231_);
lean_dec(v_i_1224_);
v_i_1224_ = v___x_1232_;
goto _start;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_array_fget_borrowed(v_vals_1223_, v_i_1224_);
lean_dec(v_i_1224_);
lean_inc(v___x_1234_);
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_keys_1236_, lean_object* v_vals_1237_, lean_object* v_i_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(v_keys_1236_, v_vals_1237_, v_i_1238_, v_k_1239_);
lean_dec(v_k_1239_);
lean_dec_ref(v_vals_1237_);
lean_dec_ref(v_keys_1236_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(lean_object* v_x_1241_, size_t v_x_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
lean_object* v_es_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1265_; 
v_es_1244_ = lean_ctor_get(v_x_1241_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1241_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1246_ = v_x_1241_;
v_isShared_1247_ = v_isSharedCheck_1265_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_es_1244_);
lean_dec(v_x_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1265_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v_j_1252_; lean_object* v___x_1253_; 
v___x_1248_ = lean_box(2);
v___x_1249_ = ((size_t)5ULL);
v___x_1250_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1251_ = lean_usize_land(v_x_1242_, v___x_1250_);
v_j_1252_ = lean_usize_to_nat(v___x_1251_);
v___x_1253_ = lean_array_get(v___x_1248_, v_es_1244_, v_j_1252_);
lean_dec(v_j_1252_);
lean_dec_ref(v_es_1244_);
switch(lean_obj_tag(v___x_1253_))
{
case 0:
{
lean_object* v_key_1254_; lean_object* v_val_1255_; uint8_t v___x_1256_; 
v_key_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_key_1254_);
v_val_1255_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_val_1255_);
lean_dec_ref(v___x_1253_);
v___x_1256_ = l_Lean_instBEqLevelMVarId_beq(v_x_1243_, v_key_1254_);
lean_dec(v_key_1254_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_dec(v_val_1255_);
lean_del_object(v___x_1246_);
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
else
{
lean_object* v___x_1259_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 0, v_val_1255_);
v___x_1259_ = v___x_1246_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_val_1255_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
case 1:
{
lean_object* v_node_1261_; size_t v___x_1262_; 
lean_del_object(v___x_1246_);
v_node_1261_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_node_1261_);
lean_dec_ref(v___x_1253_);
v___x_1262_ = lean_usize_shift_right(v_x_1242_, v___x_1249_);
v_x_1241_ = v_node_1261_;
v_x_1242_ = v___x_1262_;
goto _start;
}
default: 
{
lean_object* v___x_1264_; 
lean_del_object(v___x_1246_);
v___x_1264_ = lean_box(0);
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_ks_1266_; lean_object* v_vs_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_ks_1266_ = lean_ctor_get(v_x_1241_, 0);
lean_inc_ref(v_ks_1266_);
v_vs_1267_ = lean_ctor_get(v_x_1241_, 1);
lean_inc_ref(v_vs_1267_);
lean_dec_ref(v_x_1241_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(v_ks_1266_, v_vs_1267_, v___x_1268_, v_x_1243_);
lean_dec_ref(v_vs_1267_);
lean_dec_ref(v_ks_1266_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
size_t v_x_12730__boxed_1273_; lean_object* v_res_1274_; 
v_x_12730__boxed_1273_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_res_1274_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(v_x_1270_, v_x_12730__boxed_1273_, v_x_1272_);
lean_dec(v_x_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
uint64_t v___x_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = l_Lean_instHashableLevelMVarId_hash(v_x_1276_);
v___x_1278_ = lean_uint64_to_usize(v___x_1277_);
v___x_1279_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(v_x_1275_, v___x_1278_, v_x_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(v_x_1280_, v_x_1281_);
lean_dec(v_x_1281_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(lean_object* v_mvarId_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v_mctx_1293_; lean_object* v_levelAssignDepth_1294_; lean_object* v_lDepth_1295_; lean_object* v___x_1296_; 
v___x_1292_ = lean_st_ref_get(v___y_1288_);
v_mctx_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_mctx_1293_);
lean_dec(v___x_1292_);
v_levelAssignDepth_1294_ = lean_ctor_get(v_mctx_1293_, 1);
lean_inc(v_levelAssignDepth_1294_);
v_lDepth_1295_ = lean_ctor_get(v_mctx_1293_, 3);
lean_inc_ref(v_lDepth_1295_);
lean_dec_ref(v_mctx_1293_);
v___x_1296_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(v_lDepth_1295_, v_mvarId_1286_);
if (lean_obj_tag(v___x_1296_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v_mvarId_1286_);
v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1306_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_val_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1306_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1301_ = lean_nat_dec_le(v_levelAssignDepth_1294_, v_val_1297_);
lean_dec(v_val_1297_);
lean_dec(v_levelAssignDepth_1294_);
v___x_1302_ = lean_box(v___x_1301_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v___x_1296_);
lean_dec(v_levelAssignDepth_1294_);
v___x_1307_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__0));
v___x_1308_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__1));
v___x_1309_ = lean_unsigned_to_nat(451u);
v___x_1310_ = lean_unsigned_to_nat(14u);
v___x_1311_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___closed__2));
v___x_1312_ = 1;
v___x_1313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1286_, v___x_1312_);
v___x_1314_ = lean_string_append(v___x_1311_, v___x_1313_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = l_mkPanicMessageWithDecl(v___x_1307_, v___x_1308_, v___x_1309_, v___x_1310_, v___x_1314_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__5(v___x_1315_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1___boxed(lean_object* v_mvarId_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(v_mvarId_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v_x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___y_1331_; lean_object* v___y_1332_; uint8_t v_a_1333_; lean_object* v_lvl_u2081_1339_; lean_object* v_lvl_u2082_1340_; 
switch(lean_obj_tag(v_x_1324_))
{
case 1:
{
lean_object* v_a_1347_; uint8_t v___x_1348_; 
v_a_1347_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v_x_1324_);
v___x_1348_ = l_Lean_Level_hasMVar(v_a_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_a_1347_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
v___x_1349_ = lean_box(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
else
{
v_x_1324_ = v_a_1347_;
goto _start;
}
}
case 2:
{
lean_object* v_a_1352_; lean_object* v_a_1353_; 
v_a_1352_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_a_1352_);
v_a_1353_ = lean_ctor_get(v_x_1324_, 1);
lean_inc(v_a_1353_);
lean_dec_ref(v_x_1324_);
v_lvl_u2081_1339_ = v_a_1352_;
v_lvl_u2082_1340_ = v_a_1353_;
goto v___jp_1338_;
}
case 3:
{
lean_object* v_a_1354_; lean_object* v_a_1355_; 
v_a_1354_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_a_1354_);
v_a_1355_ = lean_ctor_get(v_x_1324_, 1);
lean_inc(v_a_1355_);
lean_dec_ref(v_x_1324_);
v_lvl_u2081_1339_ = v_a_1354_;
v_lvl_u2082_1340_ = v_a_1355_;
goto v___jp_1338_;
}
case 5:
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_a_1356_);
lean_dec_ref(v_x_1324_);
v___x_1357_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1(v_a_1356_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
return v___x_1357_;
}
default: 
{
uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v_x_1324_);
v___x_1358_ = 0;
v___x_1359_ = lean_box(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
}
v___jp_1330_:
{
if (v_a_1333_ == 0)
{
uint8_t v___x_1334_; 
lean_dec_ref(v___y_1332_);
v___x_1334_ = l_Lean_Level_hasMVar(v___y_1331_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
v___x_1335_ = lean_box(v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
else
{
v_x_1324_ = v___y_1331_;
goto _start;
}
}
else
{
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v___y_1332_;
}
}
v___jp_1338_:
{
uint8_t v___x_1341_; 
v___x_1341_ = l_Lean_Level_hasMVar(v_lvl_u2081_1339_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_lvl_u2081_1339_);
v___x_1342_ = lean_box(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___y_1331_ = v_lvl_u2082_1340_;
v___y_1332_ = v___x_1343_;
v_a_1333_ = v___x_1341_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1344_; 
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
v___x_1344_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_lvl_u2081_1339_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; uint8_t v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
v___x_1346_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
v___y_1331_ = v_lvl_u2082_1340_;
v___y_1332_ = v___x_1344_;
v_a_1333_ = v___x_1346_;
goto v___jp_1330_;
}
else
{
lean_dec(v_lvl_u2082_1340_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1368_, lean_object* v_lhs_1369_, lean_object* v_rhs_1370_, lean_object* v___x_1371_, lean_object* v___x_1372_, uint8_t v___x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___y_1402_; 
if (v___x_1368_ == 0)
{
lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_inc(v_lhs_1369_);
v___x_1448_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1369_, v___y_1375_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref(v___x_1448_);
lean_inc(v_rhs_1370_);
v___x_1450_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1370_, v___y_1375_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = l_Lean_Level_normalize(v_a_1449_);
lean_dec(v_a_1449_);
v___x_1453_ = l_Lean_Level_normalize(v_a_1451_);
lean_dec(v_a_1451_);
v___x_1454_ = lean_level_eq(v_lhs_1369_, v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1455_ = lean_is_level_def_eq(v___x_1452_, v___x_1453_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_level_eq(v_rhs_1370_, v___x_1453_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1457_ = lean_is_level_def_eq(v___x_1452_, v___x_1453_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; 
lean_dec(v___x_1453_);
lean_dec(v___x_1452_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v_rhs_1370_);
lean_inc(v_lhs_1369_);
v___x_1458_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1369_, v_rhs_1370_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1500_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1500_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1500_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
uint8_t v___x_1463_; uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = 2;
v___x_1464_ = lean_unbox(v_a_1459_);
v___x_1465_ = l_Lean_instBEqLBool_beq(v___x_1464_, v___x_1463_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; uint8_t v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1466_ = 1;
v___x_1467_ = lean_unbox(v_a_1459_);
lean_dec(v_a_1459_);
v___x_1468_ = l_Lean_instBEqLBool_beq(v___x_1467_, v___x_1466_);
v___x_1469_ = lean_box(v___x_1468_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1469_);
v___x_1471_ = v___x_1461_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1473_; 
lean_del_object(v___x_1461_);
lean_dec(v_a_1459_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v_lhs_1369_);
lean_inc(v_rhs_1370_);
v___x_1473_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1370_, v_lhs_1369_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1491_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1491_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1491_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
uint8_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_unbox(v_a_1474_);
v___x_1479_ = l_Lean_instBEqLBool_beq(v___x_1478_, v___x_1463_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; uint8_t v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1480_ = 1;
v___x_1481_ = lean_unbox(v_a_1474_);
lean_dec(v_a_1474_);
v___x_1482_ = l_Lean_instBEqLBool_beq(v___x_1481_, v___x_1480_);
v___x_1483_ = lean_box(v___x_1482_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1483_);
v___x_1485_ = v___x_1476_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
lean_object* v___x_1487_; 
lean_del_object(v___x_1476_);
lean_dec(v_a_1474_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v_lhs_1369_);
v___x_1487_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_lhs_1369_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; uint8_t v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
v___x_1489_ = lean_unbox(v_a_1488_);
lean_dec(v_a_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec_ref(v___x_1487_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v_rhs_1370_);
v___x_1490_ = l_Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v_rhs_1370_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
v___y_1402_ = v___x_1490_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___x_1487_;
goto v___jp_1401_;
}
}
else
{
v___y_1402_ = v___x_1487_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v_a_1492_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1473_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1473_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v_a_1501_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1458_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1458_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
v___x_1509_ = l_Lean_Level_getOffset(v_lhs_1369_);
lean_dec(v_lhs_1369_);
v___x_1510_ = l_Lean_Level_getOffset(v_rhs_1370_);
lean_dec(v_rhs_1370_);
v___x_1511_ = lean_nat_dec_eq(v___x_1509_, v___x_1510_);
lean_dec(v___x_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
v___jp_1379_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_a_1383_; uint8_t v___x_1384_; 
v___x_1380_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2));
v___x_1381_ = l_Lean_Name_mkStr3(v___x_1371_, v___x_1372_, v___x_1380_);
lean_inc(v___x_1381_);
v___x_1382_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(v___x_1381_, v___y_1376_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = lean_unbox(v_a_1383_);
lean_dec(v_a_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec(v___x_1381_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1385_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1386_ = l_Lean_MessageData_ofLevel(v_lhs_1369_);
v___x_1387_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = l_Lean_MessageData_ofLevel(v_rhs_1370_);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1(v___x_1381_, v___x_1390_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; 
lean_dec_ref(v___x_1391_);
v___x_1392_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1392_;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1391_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
v___jp_1401_:
{
if (lean_obj_tag(v___y_1402_) == 0)
{
lean_object* v_a_1403_; uint8_t v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v___y_1402_);
v___x_1404_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Meta_getConfig___redArg(v___y_1374_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1421_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1421_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1421_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
uint8_t v_isDefEqStuckEx_1410_; 
v_isDefEqStuckEx_1410_ = lean_ctor_get_uint8(v_a_1406_, 4);
lean_dec(v_a_1406_);
if (v_isDefEqStuckEx_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1411_ = lean_box(v_isDefEqStuckEx_1410_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = l_Lean_Level_isMVar(v_lhs_1369_);
if (v___x_1415_ == 0)
{
uint8_t v___x_1416_; 
v___x_1416_ = l_Lean_Level_isMVar(v_rhs_1370_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v___x_1417_ = lean_box(v___x_1416_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1417_);
v___x_1419_ = v___x_1408_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_del_object(v___x_1408_);
goto v___jp_1379_;
}
}
else
{
lean_del_object(v___x_1408_);
goto v___jp_1379_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
v_a_1422_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1405_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1405_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v___x_1430_; 
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
v___x_1430_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1369_, v_rhs_1370_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v___x_1430_, 0);
lean_dec(v_unused_1439_);
v___x_1432_ = v___x_1430_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_dec(v___x_1430_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_box(v___x_1373_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1430_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1430_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
lean_dec(v_rhs_1370_);
lean_dec(v_lhs_1369_);
return v___y_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1514_, lean_object* v_lhs_1515_, lean_object* v_rhs_1516_, lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v___x_12951__boxed_1525_; uint8_t v___x_12954__boxed_1526_; lean_object* v_res_1527_; 
v___x_12951__boxed_1525_ = lean_unbox(v___x_1514_);
v___x_12954__boxed_1526_ = lean_unbox(v___x_1519_);
v_res_1527_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_12951__boxed_1525_, v_lhs_1515_, v_rhs_1516_, v___x_1517_, v___x_1518_, v___x_12954__boxed_1526_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(lean_object* v_lhs_1528_, lean_object* v_rhs_1529_, lean_object* v_x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1536_ = l_Lean_MessageData_ofLevel(v_lhs_1528_);
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_MessageData_ofLevel(v_rhs_1529_);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object* v_lhs_1542_, lean_object* v_rhs_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(v_lhs_1542_, v_rhs_1543_, v_x_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v_x_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_bs_1553_){
_start:
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1554_ == 0)
{
return v_bs_1553_;
}
else
{
lean_object* v_v_1555_; lean_object* v_msg_1556_; lean_object* v___x_1557_; lean_object* v_bs_x27_1558_; size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v_v_1555_ = lean_array_uget_borrowed(v_bs_1553_, v_i_1552_);
v_msg_1556_ = lean_ctor_get(v_v_1555_, 1);
lean_inc_ref(v_msg_1556_);
v___x_1557_ = lean_unsigned_to_nat(0u);
v_bs_x27_1558_ = lean_array_uset(v_bs_1553_, v_i_1552_, v___x_1557_);
v___x_1559_ = ((size_t)1ULL);
v___x_1560_ = lean_usize_add(v_i_1552_, v___x_1559_);
v___x_1561_ = lean_array_uset(v_bs_x27_1558_, v_i_1552_, v_msg_1556_);
v_i_1552_ = v___x_1560_;
v_bs_1553_ = v___x_1561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1563_, lean_object* v_i_1564_, lean_object* v_bs_1565_){
_start:
{
size_t v_sz_boxed_1566_; size_t v_i_boxed_1567_; lean_object* v_res_1568_; 
v_sz_boxed_1566_ = lean_unbox_usize(v_sz_1563_);
lean_dec(v_sz_1563_);
v_i_boxed_1567_ = lean_unbox_usize(v_i_1564_);
lean_dec(v_i_1564_);
v_res_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(v_sz_boxed_1566_, v_i_boxed_1567_, v_bs_1565_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(lean_object* v_oldTraces_1569_, lean_object* v_data_1570_, lean_object* v_ref_1571_, lean_object* v_msg_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_fileName_1578_; lean_object* v_fileMap_1579_; lean_object* v_options_1580_; lean_object* v_currRecDepth_1581_; lean_object* v_maxRecDepth_1582_; lean_object* v_ref_1583_; lean_object* v_currNamespace_1584_; lean_object* v_openDecls_1585_; lean_object* v_initHeartbeats_1586_; lean_object* v_maxHeartbeats_1587_; lean_object* v_quotContext_1588_; lean_object* v_currMacroScope_1589_; uint8_t v_diag_1590_; lean_object* v_cancelTk_x3f_1591_; uint8_t v_suppressElabErrors_1592_; lean_object* v_inheritedTraceOptions_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1648_; 
v_fileName_1578_ = lean_ctor_get(v___y_1575_, 0);
v_fileMap_1579_ = lean_ctor_get(v___y_1575_, 1);
v_options_1580_ = lean_ctor_get(v___y_1575_, 2);
v_currRecDepth_1581_ = lean_ctor_get(v___y_1575_, 3);
v_maxRecDepth_1582_ = lean_ctor_get(v___y_1575_, 4);
v_ref_1583_ = lean_ctor_get(v___y_1575_, 5);
v_currNamespace_1584_ = lean_ctor_get(v___y_1575_, 6);
v_openDecls_1585_ = lean_ctor_get(v___y_1575_, 7);
v_initHeartbeats_1586_ = lean_ctor_get(v___y_1575_, 8);
v_maxHeartbeats_1587_ = lean_ctor_get(v___y_1575_, 9);
v_quotContext_1588_ = lean_ctor_get(v___y_1575_, 10);
v_currMacroScope_1589_ = lean_ctor_get(v___y_1575_, 11);
v_diag_1590_ = lean_ctor_get_uint8(v___y_1575_, sizeof(void*)*14);
v_cancelTk_x3f_1591_ = lean_ctor_get(v___y_1575_, 12);
v_suppressElabErrors_1592_ = lean_ctor_get_uint8(v___y_1575_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1593_ = lean_ctor_get(v___y_1575_, 13);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___y_1575_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1595_ = v___y_1575_;
v_isShared_1596_ = v_isSharedCheck_1648_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_inheritedTraceOptions_1593_);
lean_inc(v_cancelTk_x3f_1591_);
lean_inc(v_currMacroScope_1589_);
lean_inc(v_quotContext_1588_);
lean_inc(v_maxHeartbeats_1587_);
lean_inc(v_initHeartbeats_1586_);
lean_inc(v_openDecls_1585_);
lean_inc(v_currNamespace_1584_);
lean_inc(v_ref_1583_);
lean_inc(v_maxRecDepth_1582_);
lean_inc(v_currRecDepth_1581_);
lean_inc(v_options_1580_);
lean_inc(v_fileMap_1579_);
lean_inc(v_fileName_1578_);
lean_dec(v___y_1575_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1648_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v_traceState_1598_; lean_object* v_traces_1599_; lean_object* v_ref_1600_; lean_object* v___x_1602_; 
v___x_1597_ = lean_st_ref_get(v___y_1576_);
v_traceState_1598_ = lean_ctor_get(v___x_1597_, 4);
lean_inc_ref(v_traceState_1598_);
lean_dec(v___x_1597_);
v_traces_1599_ = lean_ctor_get(v_traceState_1598_, 0);
lean_inc_ref(v_traces_1599_);
lean_dec_ref(v_traceState_1598_);
v_ref_1600_ = l_Lean_replaceRef(v_ref_1571_, v_ref_1583_);
lean_dec(v_ref_1583_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 5, v_ref_1600_);
v___x_1602_ = v___x_1595_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_fileName_1578_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_fileMap_1579_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_options_1580_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_currRecDepth_1581_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_maxRecDepth_1582_);
lean_ctor_set(v_reuseFailAlloc_1647_, 5, v_ref_1600_);
lean_ctor_set(v_reuseFailAlloc_1647_, 6, v_currNamespace_1584_);
lean_ctor_set(v_reuseFailAlloc_1647_, 7, v_openDecls_1585_);
lean_ctor_set(v_reuseFailAlloc_1647_, 8, v_initHeartbeats_1586_);
lean_ctor_set(v_reuseFailAlloc_1647_, 9, v_maxHeartbeats_1587_);
lean_ctor_set(v_reuseFailAlloc_1647_, 10, v_quotContext_1588_);
lean_ctor_set(v_reuseFailAlloc_1647_, 11, v_currMacroScope_1589_);
lean_ctor_set(v_reuseFailAlloc_1647_, 12, v_cancelTk_x3f_1591_);
lean_ctor_set(v_reuseFailAlloc_1647_, 13, v_inheritedTraceOptions_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*14, v_diag_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*14 + 1, v_suppressElabErrors_1592_);
v___x_1602_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; size_t v_sz_1604_; size_t v___x_1605_; lean_object* v___x_1606_; lean_object* v_msg_1607_; lean_object* v___x_1608_; lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1646_; 
v___x_1603_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1599_);
lean_dec_ref(v_traces_1599_);
v_sz_1604_ = lean_array_size(v___x_1603_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6_spec__9(v_sz_1604_, v___x_1605_, v___x_1603_);
v_msg_1607_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1607_, 0, v_data_1570_);
lean_ctor_set(v_msg_1607_, 1, v_msg_1572_);
lean_ctor_set(v_msg_1607_, 2, v___x_1606_);
v___x_1608_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1_spec__1(v_msg_1607_, v___y_1573_, v___y_1574_, v___x_1602_, v___y_1576_);
lean_dec_ref(v___x_1602_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1646_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1646_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v_traceState_1614_; lean_object* v_env_1615_; lean_object* v_nextMacroScope_1616_; lean_object* v_ngen_1617_; lean_object* v_auxDeclNGen_1618_; lean_object* v_cache_1619_; lean_object* v_messages_1620_; lean_object* v_infoState_1621_; lean_object* v_snapshotTasks_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1645_; 
v___x_1613_ = lean_st_ref_take(v___y_1576_);
v_traceState_1614_ = lean_ctor_get(v___x_1613_, 4);
v_env_1615_ = lean_ctor_get(v___x_1613_, 0);
v_nextMacroScope_1616_ = lean_ctor_get(v___x_1613_, 1);
v_ngen_1617_ = lean_ctor_get(v___x_1613_, 2);
v_auxDeclNGen_1618_ = lean_ctor_get(v___x_1613_, 3);
v_cache_1619_ = lean_ctor_get(v___x_1613_, 5);
v_messages_1620_ = lean_ctor_get(v___x_1613_, 6);
v_infoState_1621_ = lean_ctor_get(v___x_1613_, 7);
v_snapshotTasks_1622_ = lean_ctor_get(v___x_1613_, 8);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1624_ = v___x_1613_;
v_isShared_1625_ = v_isSharedCheck_1645_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snapshotTasks_1622_);
lean_inc(v_infoState_1621_);
lean_inc(v_messages_1620_);
lean_inc(v_cache_1619_);
lean_inc(v_traceState_1614_);
lean_inc(v_auxDeclNGen_1618_);
lean_inc(v_ngen_1617_);
lean_inc(v_nextMacroScope_1616_);
lean_inc(v_env_1615_);
lean_dec(v___x_1613_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1645_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
uint64_t v_tid_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1643_; 
v_tid_1626_ = lean_ctor_get_uint64(v_traceState_1614_, sizeof(void*)*1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_traceState_1614_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v_traceState_1614_, 0);
lean_dec(v_unused_1644_);
v___x_1628_ = v_traceState_1614_;
v_isShared_1629_ = v_isSharedCheck_1643_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v_traceState_1614_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1643_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_ref_1571_);
lean_ctor_set(v___x_1630_, 1, v_a_1609_);
v___x_1631_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1569_, v___x_1630_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1631_);
v___x_1633_ = v___x_1628_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1631_);
lean_ctor_set_uint64(v_reuseFailAlloc_1642_, sizeof(void*)*1, v_tid_1626_);
v___x_1633_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v___x_1633_);
v___x_1635_ = v___x_1624_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_env_1615_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_nextMacroScope_1616_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_ngen_1617_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_auxDeclNGen_1618_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1641_, 5, v_cache_1619_);
lean_ctor_set(v_reuseFailAlloc_1641_, 6, v_messages_1620_);
lean_ctor_set(v_reuseFailAlloc_1641_, 7, v_infoState_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 8, v_snapshotTasks_1622_);
v___x_1635_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1636_ = lean_st_ref_set(v___y_1576_, v___x_1635_);
v___x_1637_ = lean_box(0);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1637_);
v___x_1639_ = v___x_1611_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6___boxed(lean_object* v_oldTraces_1649_, lean_object* v_data_1650_, lean_object* v_ref_1651_, lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(v_oldTraces_1649_, v_data_1650_, v_ref_1651_, v_msg_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(lean_object* v_x_1659_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v_x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v_x_1659_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v_x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 1);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v_x_1659_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1659_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v_x_1659_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v_x_1659_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 0);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg___boxed(lean_object* v_x_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_x_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(lean_object* v_opts_1680_, lean_object* v_opt_1681_){
_start:
{
lean_object* v_name_1682_; lean_object* v_defValue_1683_; lean_object* v_map_1684_; lean_object* v___x_1685_; 
v_name_1682_ = lean_ctor_get(v_opt_1681_, 0);
v_defValue_1683_ = lean_ctor_get(v_opt_1681_, 1);
v_map_1684_ = lean_ctor_get(v_opts_1680_, 0);
v___x_1685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1684_, v_name_1682_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_inc(v_defValue_1683_);
return v_defValue_1683_;
}
else
{
lean_object* v_val_1686_; 
v_val_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_val_1686_);
lean_dec_ref(v___x_1685_);
if (lean_obj_tag(v_val_1686_) == 3)
{
lean_object* v_v_1687_; 
v_v_1687_ = lean_ctor_get(v_val_1686_, 0);
lean_inc(v_v_1687_);
lean_dec_ref(v_val_1686_);
return v_v_1687_;
}
else
{
lean_dec(v_val_1686_);
lean_inc(v_defValue_1683_);
return v_defValue_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8___boxed(lean_object* v_opts_1688_, lean_object* v_opt_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(v_opts_1688_, v_opt_1689_);
lean_dec_ref(v_opt_1689_);
lean_dec_ref(v_opts_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(lean_object* v_e_1691_){
_start:
{
if (lean_obj_tag(v_e_1691_) == 0)
{
uint8_t v___x_1692_; 
v___x_1692_ = 2;
return v___x_1692_;
}
else
{
lean_object* v_a_1693_; uint8_t v___x_1694_; 
v_a_1693_ = lean_ctor_get(v_e_1691_, 0);
v___x_1694_ = lean_unbox(v_a_1693_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = 1;
return v___x_1695_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = 0;
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5___boxed(lean_object* v_e_1697_){
_start:
{
uint8_t v_res_1698_; lean_object* v_r_1699_; 
v_res_1698_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(v_e_1697_);
lean_dec_ref(v_e_1697_);
v_r_1699_ = lean_box(v_res_1698_);
return v_r_1699_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__0));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__2));
v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
return v___x_1705_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1706_; double v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(1000u);
v___x_1707_ = lean_float_of_nat(v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_cls_1708_, uint8_t v_collapsed_1709_, lean_object* v_tag_1710_, lean_object* v_opts_1711_, uint8_t v_clsEnabled_1712_, lean_object* v_oldTraces_1713_, lean_object* v_msg_1714_, lean_object* v_resStartStop_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_fst_1721_; lean_object* v_snd_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1820_; 
v_fst_1721_ = lean_ctor_get(v_resStartStop_1715_, 0);
v_snd_1722_ = lean_ctor_get(v_resStartStop_1715_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_resStartStop_1715_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1724_ = v_resStartStop_1715_;
v_isShared_1725_ = v_isSharedCheck_1820_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_snd_1722_);
lean_inc(v_fst_1721_);
lean_dec(v_resStartStop_1715_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1820_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v_data_1729_; lean_object* v_fst_1740_; lean_object* v_snd_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1819_; 
v_fst_1740_ = lean_ctor_get(v_snd_1722_, 0);
v_snd_1741_ = lean_ctor_get(v_snd_1722_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_snd_1722_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1743_ = v_snd_1722_;
v_isShared_1744_ = v_isSharedCheck_1819_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snd_1741_);
lean_inc(v_fst_1740_);
lean_dec(v_snd_1722_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1819_;
goto v_resetjp_1742_;
}
v___jp_1726_:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__6(v_oldTraces_1713_, v_data_1729_, v___y_1727_, v___y_1728_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; 
lean_dec_ref(v___x_1730_);
v___x_1731_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_fst_1721_);
return v___x_1731_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_fst_1721_);
v_a_1732_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1730_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1730_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___y_1748_; lean_object* v_a_1749_; uint8_t v___y_1773_; double v___y_1804_; 
v___x_1745_ = l_Lean_trace_profiler;
v___x_1746_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1711_, v___x_1745_);
if (v___x_1746_ == 0)
{
v___y_1773_ = v___x_1746_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1810_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1711_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; double v___x_1813_; double v___x_1814_; double v___x_1815_; 
v___x_1811_ = l_Lean_trace_profiler_threshold;
v___x_1812_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(v_opts_1711_, v___x_1811_);
v___x_1813_ = lean_float_of_nat(v___x_1812_);
v___x_1814_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__4);
v___x_1815_ = lean_float_div(v___x_1813_, v___x_1814_);
v___y_1804_ = v___x_1815_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; double v___x_1818_; 
v___x_1816_ = l_Lean_trace_profiler_threshold;
v___x_1817_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__8(v_opts_1711_, v___x_1816_);
v___x_1818_ = lean_float_of_nat(v___x_1817_);
v___y_1804_ = v___x_1818_;
goto v___jp_1803_;
}
}
v___jp_1747_:
{
uint8_t v_result_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v_result_1750_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__5(v_fst_1721_);
v___x_1751_ = l_Lean_TraceResult_toEmoji(v_result_1750_);
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
v___x_1753_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__1);
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 7);
lean_ctor_set(v___x_1743_, 1, v___x_1753_);
lean_ctor_set(v___x_1743_, 0, v___x_1752_);
v___x_1755_ = v___x_1743_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v_m_1757_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 7);
lean_ctor_set(v___x_1724_, 1, v_a_1749_);
lean_ctor_set(v___x_1724_, 0, v___x_1755_);
v_m_1757_ = v___x_1724_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_a_1749_);
v_m_1757_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; double v___x_1760_; lean_object* v_data_1761_; 
v___x_1758_ = lean_box(v_result_1750_);
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
v___x_1760_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__0);
lean_inc_ref(v_tag_1710_);
lean_inc_ref(v___x_1759_);
lean_inc(v_cls_1708_);
v_data_1761_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1761_, 0, v_cls_1708_);
lean_ctor_set(v_data_1761_, 1, v___x_1759_);
lean_ctor_set(v_data_1761_, 2, v_tag_1710_);
lean_ctor_set_float(v_data_1761_, sizeof(void*)*3, v___x_1760_);
lean_ctor_set_float(v_data_1761_, sizeof(void*)*3 + 8, v___x_1760_);
lean_ctor_set_uint8(v_data_1761_, sizeof(void*)*3 + 16, v_collapsed_1709_);
if (v___x_1746_ == 0)
{
lean_dec_ref(v___x_1759_);
lean_dec(v_snd_1741_);
lean_dec(v_fst_1740_);
lean_dec_ref(v_tag_1710_);
lean_dec(v_cls_1708_);
v___y_1727_ = v___y_1748_;
v___y_1728_ = v_m_1757_;
v_data_1729_ = v_data_1761_;
goto v___jp_1726_;
}
else
{
lean_object* v_data_1762_; double v___x_1763_; double v___x_1764_; 
lean_dec_ref(v_data_1761_);
v_data_1762_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1762_, 0, v_cls_1708_);
lean_ctor_set(v_data_1762_, 1, v___x_1759_);
lean_ctor_set(v_data_1762_, 2, v_tag_1710_);
v___x_1763_ = lean_unbox_float(v_fst_1740_);
lean_dec(v_fst_1740_);
lean_ctor_set_float(v_data_1762_, sizeof(void*)*3, v___x_1763_);
v___x_1764_ = lean_unbox_float(v_snd_1741_);
lean_dec(v_snd_1741_);
lean_ctor_set_float(v_data_1762_, sizeof(void*)*3 + 8, v___x_1764_);
lean_ctor_set_uint8(v_data_1762_, sizeof(void*)*3 + 16, v_collapsed_1709_);
v___y_1727_ = v___y_1748_;
v___y_1728_ = v_m_1757_;
v_data_1729_ = v_data_1762_;
goto v___jp_1726_;
}
}
}
}
v___jp_1767_:
{
lean_object* v_ref_1768_; lean_object* v___x_1769_; 
v_ref_1768_ = lean_ctor_get(v___y_1718_, 5);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc(v_fst_1721_);
v___x_1769_ = lean_apply_6(v_msg_1714_, v_fst_1721_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, lean_box(0));
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1769_);
lean_inc(v_ref_1768_);
v___y_1748_ = v_ref_1768_;
v_a_1749_ = v_a_1770_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1771_; 
lean_dec_ref(v___x_1769_);
v___x_1771_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___closed__3);
lean_inc(v_ref_1768_);
v___y_1748_ = v_ref_1768_;
v_a_1749_ = v___x_1771_;
goto v___jp_1747_;
}
}
v___jp_1772_:
{
if (v_clsEnabled_1712_ == 0)
{
if (v___y_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v_traceState_1775_; lean_object* v_env_1776_; lean_object* v_nextMacroScope_1777_; lean_object* v_ngen_1778_; lean_object* v_auxDeclNGen_1779_; lean_object* v_cache_1780_; lean_object* v_messages_1781_; lean_object* v_infoState_1782_; lean_object* v_snapshotTasks_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1802_; 
lean_del_object(v___x_1743_);
lean_dec(v_snd_1741_);
lean_dec(v_fst_1740_);
lean_del_object(v___x_1724_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_msg_1714_);
lean_dec_ref(v_tag_1710_);
lean_dec(v_cls_1708_);
v___x_1774_ = lean_st_ref_take(v___y_1719_);
v_traceState_1775_ = lean_ctor_get(v___x_1774_, 4);
v_env_1776_ = lean_ctor_get(v___x_1774_, 0);
v_nextMacroScope_1777_ = lean_ctor_get(v___x_1774_, 1);
v_ngen_1778_ = lean_ctor_get(v___x_1774_, 2);
v_auxDeclNGen_1779_ = lean_ctor_get(v___x_1774_, 3);
v_cache_1780_ = lean_ctor_get(v___x_1774_, 5);
v_messages_1781_ = lean_ctor_get(v___x_1774_, 6);
v_infoState_1782_ = lean_ctor_get(v___x_1774_, 7);
v_snapshotTasks_1783_ = lean_ctor_get(v___x_1774_, 8);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1785_ = v___x_1774_;
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snapshotTasks_1783_);
lean_inc(v_infoState_1782_);
lean_inc(v_messages_1781_);
lean_inc(v_cache_1780_);
lean_inc(v_traceState_1775_);
lean_inc(v_auxDeclNGen_1779_);
lean_inc(v_ngen_1778_);
lean_inc(v_nextMacroScope_1777_);
lean_inc(v_env_1776_);
lean_dec(v___x_1774_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint64_t v_tid_1787_; lean_object* v_traces_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1801_; 
v_tid_1787_ = lean_ctor_get_uint64(v_traceState_1775_, sizeof(void*)*1);
v_traces_1788_ = lean_ctor_get(v_traceState_1775_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_traceState_1775_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1790_ = v_traceState_1775_;
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_traces_1788_);
lean_dec(v_traceState_1775_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1713_, v_traces_1788_);
lean_dec_ref(v_traces_1788_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1792_);
lean_ctor_set_uint64(v_reuseFailAlloc_1800_, sizeof(void*)*1, v_tid_1787_);
v___x_1794_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 4, v___x_1794_);
v___x_1796_ = v___x_1785_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_env_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_nextMacroScope_1777_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_ngen_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_auxDeclNGen_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_cache_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_messages_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_infoState_1782_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_snapshotTasks_1783_);
v___x_1796_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_st_ref_set(v___y_1719_, v___x_1796_);
lean_dec(v___y_1719_);
v___x_1798_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_fst_1721_);
return v___x_1798_;
}
}
}
}
}
else
{
goto v___jp_1767_;
}
}
else
{
goto v___jp_1767_;
}
}
v___jp_1803_:
{
double v___x_1805_; double v___x_1806_; double v___x_1807_; uint8_t v___x_1808_; 
v___x_1805_ = lean_unbox_float(v_snd_1741_);
v___x_1806_ = lean_unbox_float(v_fst_1740_);
v___x_1807_ = lean_float_sub(v___x_1805_, v___x_1806_);
v___x_1808_ = lean_float_decLt(v___y_1804_, v___x_1807_);
v___y_1773_ = v___x_1808_;
goto v___jp_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_cls_1821_, lean_object* v_collapsed_1822_, lean_object* v_tag_1823_, lean_object* v_opts_1824_, lean_object* v_clsEnabled_1825_, lean_object* v_oldTraces_1826_, lean_object* v_msg_1827_, lean_object* v_resStartStop_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v_collapsed_boxed_1834_; uint8_t v_clsEnabled_boxed_1835_; lean_object* v_res_1836_; 
v_collapsed_boxed_1834_ = lean_unbox(v_collapsed_1822_);
v_clsEnabled_boxed_1835_ = lean_unbox(v_clsEnabled_1825_);
v_res_1836_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_cls_1821_, v_collapsed_boxed_1834_, v_tag_1823_, v_opts_1824_, v_clsEnabled_boxed_1835_, v_oldTraces_1826_, v_msg_1827_, v_resStartStop_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_opts_1824_);
return v_res_1836_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1837_; double v___x_1838_; 
v___x_1837_ = lean_unsigned_to_nat(1000000000u);
v___x_1838_ = lean_float_of_nat(v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1842_, lean_object* v_x_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; uint8_t v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v_a_1862_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v_a_1887_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; uint8_t v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v_lhs_1949_; lean_object* v_rhs_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; 
if (lean_obj_tag(v_x_1842_) == 1)
{
if (lean_obj_tag(v_x_1843_) == 1)
{
lean_object* v_a_1978_; lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1978_ = lean_ctor_get(v_x_1842_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v_x_1842_);
v_a_1979_ = lean_ctor_get(v_x_1843_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v_x_1843_);
v___x_1980_ = lean_is_level_def_eq(v_a_1978_, v_a_1979_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
return v___x_1980_;
}
else
{
v_lhs_1949_ = v_x_1842_;
v_rhs_1950_ = v_x_1843_;
v___y_1951_ = v_a_1844_;
v___y_1952_ = v_a_1845_;
v___y_1953_ = v_a_1846_;
v___y_1954_ = v_a_1847_;
goto v___jp_1948_;
}
}
else
{
v_lhs_1949_ = v_x_1842_;
v_rhs_1950_ = v_x_1843_;
v___y_1951_ = v_a_1844_;
v___y_1952_ = v_a_1845_;
v___y_1953_ = v_a_1846_;
v___y_1954_ = v_a_1847_;
goto v___jp_1948_;
}
v___jp_1849_:
{
lean_object* v___x_1863_; double v___x_1864_; double v___x_1865_; double v___x_1866_; double v___x_1867_; double v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1863_ = lean_io_mono_nanos_now();
v___x_1864_ = lean_float_of_nat(v___y_1857_);
v___x_1865_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1866_ = lean_float_div(v___x_1864_, v___x_1865_);
v___x_1867_ = lean_float_of_nat(v___x_1863_);
v___x_1868_ = lean_float_div(v___x_1867_, v___x_1865_);
v___x_1869_ = lean_box_float(v___x_1866_);
v___x_1870_ = lean_box_float(v___x_1868_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1862_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1851_, v___y_1855_, v___y_1860_, v___y_1854_, v___y_1858_, v___y_1850_, v___y_1853_, v___x_1872_, v___y_1861_, v___y_1856_, v___y_1852_, v___y_1859_);
lean_dec_ref(v___y_1854_);
return v___x_1873_;
}
v___jp_1874_:
{
lean_object* v___x_1888_; double v___x_1889_; double v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1888_ = lean_io_get_num_heartbeats();
v___x_1889_ = lean_float_of_nat(v___y_1880_);
v___x_1890_ = lean_float_of_nat(v___x_1888_);
v___x_1891_ = lean_box_float(v___x_1889_);
v___x_1892_ = lean_box_float(v___x_1890_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1887_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1876_, v___y_1881_, v___y_1885_, v___y_1879_, v___y_1883_, v___y_1875_, v___y_1878_, v___x_1894_, v___y_1886_, v___y_1882_, v___y_1877_, v___y_1884_);
lean_dec_ref(v___y_1879_);
return v___x_1895_;
}
v___jp_1896_:
{
lean_object* v___x_1908_; lean_object* v_a_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1908_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___redArg(v___y_1905_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1911_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1899_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_io_mono_nanos_now();
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1907_);
v___x_1913_ = lean_apply_5(v___y_1903_, v___y_1907_, v___y_1902_, v___y_1900_, v___y_1905_, lean_box(0));
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
v___y_1850_ = v_a_1909_;
v___y_1851_ = v___y_1897_;
v___y_1852_ = v___y_1900_;
v___y_1853_ = v___y_1898_;
v___y_1854_ = v___y_1899_;
v___y_1855_ = v___y_1901_;
v___y_1856_ = v___y_1902_;
v___y_1857_ = v___x_1912_;
v___y_1858_ = v___y_1904_;
v___y_1859_ = v___y_1905_;
v___y_1860_ = v___y_1906_;
v___y_1861_ = v___y_1907_;
v_a_1862_ = v___x_1919_;
goto v___jp_1849_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 0);
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v___y_1850_ = v_a_1909_;
v___y_1851_ = v___y_1897_;
v___y_1852_ = v___y_1900_;
v___y_1853_ = v___y_1898_;
v___y_1854_ = v___y_1899_;
v___y_1855_ = v___y_1901_;
v___y_1856_ = v___y_1902_;
v___y_1857_ = v___x_1912_;
v___y_1858_ = v___y_1904_;
v___y_1859_ = v___y_1905_;
v___y_1860_ = v___y_1906_;
v___y_1861_ = v___y_1907_;
v_a_1862_ = v___x_1927_;
goto v___jp_1849_;
}
}
}
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1907_);
v___x_1931_ = lean_apply_5(v___y_1903_, v___y_1907_, v___y_1902_, v___y_1900_, v___y_1905_, lean_box(0));
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v___y_1875_ = v_a_1909_;
v___y_1876_ = v___y_1897_;
v___y_1877_ = v___y_1900_;
v___y_1878_ = v___y_1898_;
v___y_1879_ = v___y_1899_;
v___y_1880_ = v___x_1930_;
v___y_1881_ = v___y_1901_;
v___y_1882_ = v___y_1902_;
v___y_1883_ = v___y_1904_;
v___y_1884_ = v___y_1905_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
v_a_1887_ = v___x_1937_;
goto v___jp_1874_;
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1931_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1931_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 0);
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
v___y_1875_ = v_a_1909_;
v___y_1876_ = v___y_1897_;
v___y_1877_ = v___y_1900_;
v___y_1878_ = v___y_1898_;
v___y_1879_ = v___y_1899_;
v___y_1880_ = v___x_1930_;
v___y_1881_ = v___y_1901_;
v___y_1882_ = v___y_1902_;
v___y_1883_ = v___y_1904_;
v___y_1884_ = v___y_1905_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
v_a_1887_ = v___x_1945_;
goto v___jp_1874_;
}
}
}
}
}
v___jp_1948_:
{
lean_object* v_options_1955_; uint8_t v_hasTrace_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___y_1965_; 
v_options_1955_ = lean_ctor_get(v___y_1953_, 2);
v_hasTrace_1956_ = lean_ctor_get_uint8(v_options_1955_, sizeof(void*)*1);
v___x_1957_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1958_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_1959_ = l_Lean_Level_getLevelOffset(v_lhs_1949_);
v___x_1960_ = l_Lean_Level_getLevelOffset(v_rhs_1950_);
v___x_1961_ = lean_level_eq(v___x_1959_, v___x_1960_);
lean_dec(v___x_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = 1;
v___x_1963_ = lean_box(v___x_1961_);
v___x_1964_ = lean_box(v___x_1962_);
lean_inc(v_rhs_1950_);
lean_inc(v_lhs_1949_);
v___y_1965_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1965_, 0, v___x_1963_);
lean_closure_set(v___y_1965_, 1, v_lhs_1949_);
lean_closure_set(v___y_1965_, 2, v_rhs_1950_);
lean_closure_set(v___y_1965_, 3, v___x_1957_);
lean_closure_set(v___y_1965_, 4, v___x_1958_);
lean_closure_set(v___y_1965_, 5, v___x_1964_);
if (v_hasTrace_1956_ == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v___y_1965_);
v___x_1966_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1961_, v_lhs_1949_, v_rhs_1950_, v___x_1957_, v___x_1958_, v___x_1962_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v_a_1969_; lean_object* v___f_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1967_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_1968_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__0___redArg(v___x_1967_, v___y_1953_);
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
lean_inc(v_rhs_1950_);
lean_inc(v_lhs_1949_);
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1970_, 0, v_lhs_1949_);
lean_closure_set(v___f_1970_, 1, v_rhs_1950_);
v___x_1971_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_spec__1___closed__1));
v___x_1972_ = lean_unbox(v_a_1969_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = l_Lean_trace_profiler;
v___x_1974_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_options_1955_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec_ref(v___f_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v___y_1965_);
v___x_1975_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1961_, v_lhs_1949_, v_rhs_1950_, v___x_1957_, v___x_1958_, v___x_1962_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1975_;
}
else
{
uint8_t v___x_1976_; 
lean_inc_ref(v_options_1955_);
lean_dec(v_rhs_1950_);
lean_dec(v_lhs_1949_);
v___x_1976_ = lean_unbox(v_a_1969_);
lean_dec(v_a_1969_);
v___y_1897_ = v___x_1967_;
v___y_1898_ = v___f_1970_;
v___y_1899_ = v_options_1955_;
v___y_1900_ = v___y_1953_;
v___y_1901_ = v___x_1962_;
v___y_1902_ = v___y_1952_;
v___y_1903_ = v___y_1965_;
v___y_1904_ = v___x_1976_;
v___y_1905_ = v___y_1954_;
v___y_1906_ = v___x_1971_;
v___y_1907_ = v___y_1951_;
goto v___jp_1896_;
}
}
else
{
uint8_t v___x_1977_; 
lean_inc_ref(v_options_1955_);
lean_dec(v_rhs_1950_);
lean_dec(v_lhs_1949_);
v___x_1977_ = lean_unbox(v_a_1969_);
lean_dec(v_a_1969_);
v___y_1897_ = v___x_1967_;
v___y_1898_ = v___f_1970_;
v___y_1899_ = v_options_1955_;
v___y_1900_ = v___y_1953_;
v___y_1901_ = v___x_1962_;
v___y_1902_ = v___y_1952_;
v___y_1903_ = v___y_1965_;
v___y_1904_ = v___x_1977_;
v___y_1905_ = v___y_1954_;
v___y_1906_ = v___x_1971_;
v___y_1907_ = v___y_1951_;
goto v___jp_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = lean_is_level_def_eq(v_x_1981_, v_x_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7(lean_object* v_00_u03b1_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___redArg(v_x_1990_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1997_, lean_object* v_x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_spec__7(v_00_u03b1_1997_, v_x_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___redArg(v_x_2006_, v_x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4(v_00_u03b2_2009_, v_x_2010_, v_x_2011_);
lean_dec(v_x_2011_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_2013_, lean_object* v_x_2014_, size_t v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___redArg(v_x_2014_, v_x_2015_, v_x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
size_t v_x_13986__boxed_2022_; lean_object* v_res_2023_; 
v_x_13986__boxed_2022_ = lean_unbox_usize(v_x_2020_);
lean_dec(v_x_2020_);
v_res_2023_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9(v_00_u03b2_2018_, v_x_2019_, v_x_13986__boxed_2022_, v_x_2021_);
lean_dec(v_x_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2024_, lean_object* v_keys_2025_, lean_object* v_vals_2026_, lean_object* v_heq_2027_, lean_object* v_i_2028_, lean_object* v_k_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___redArg(v_keys_2025_, v_vals_2026_, v_i_2028_, v_k_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2031_, lean_object* v_keys_2032_, lean_object* v_vals_2033_, lean_object* v_heq_2034_, lean_object* v_i_2035_, lean_object* v_k_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_spec__1_spec__4_spec__9_spec__12(v_00_u03b2_2031_, v_keys_2032_, v_vals_2033_, v_heq_2034_, v_i_2035_, v_k_2036_);
lean_dec(v_k_2036_);
lean_dec_ref(v_vals_2033_);
lean_dec_ref(v_keys_2032_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__1));
v___x_2095_ = 0;
v___x_2096_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2097_ = l_Lean_registerTraceClass(v___x_2094_, v___x_2095_, v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; 
lean_dec_ref(v___x_2097_);
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_2099_ = 1;
v___x_2100_ = l_Lean_registerTraceClass(v___x_2098_, v___x_2099_, v___x_2096_);
return v___x_2100_;
}
else
{
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2102_;
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
