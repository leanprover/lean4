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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_hasAssignableLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffset(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.LevelDefEq"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "_private.Lean.Meta.LevelDefEq.0.Lean.Meta.solveSelfMax"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "assertion violation: v.isMax\n  "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isLevelDefEq"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 1, 100, 166, 77, 133, 145, 204)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7_value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "solveSelfMax: "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tryApproxSelfMax "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tryApproxMaxMax "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stuck"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 131, 35, 104, 114, 254, 231, 20)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3 = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_isLevelDefEqAuxImpl___closed__0;
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__1;
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__2;
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__3;
static const lean_string_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__4 = (const lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__4_value;
static const lean_string_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "instantiateMVars"};
static const lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__5 = (const lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__5_value;
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(249, 167, 243, 240, 112, 42, 66, 234)}};
static const lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__6 = (const lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__6_value;
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__7 = (const lean_object*)&l_Lean_Meta_isLevelDefEqAuxImpl___closed__7_value;
static lean_once_cell_t l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___closed__8;
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LevelDefEq"};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 184, 81, 18, 195, 210, 152, 110)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(30, 209, 144, 83, 13, 92, 153, 140)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 46, 128, 72, 56, 107, 184, 50)}};
static const lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value),LEAN_SCALAR_PTR_LITERAL(183, 118, 41, 27, 129, 22, 6, 162)}};
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
static const lean_ctor_object l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4_value),LEAN_SCALAR_PTR_LITERAL(238, 252, 13, 249, 138, 174, 25, 171)}};
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
lean_object* v___f_47_; lean_object* v___x_1320__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_1320__overap_48_ = lean_panic_fn_borrowed(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_1320__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_, lean_object* v_x_60_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_n_87_, lean_object* v_k_88_, lean_object* v_v_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_n_87_, v___x_90_, v_k_88_, v_v_89_);
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
v_newNode_157_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v___x_156_, v_x_102_, v_x_103_);
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
v___x_164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_x_101_, v_ks_160_, v_vs_161_, v___x_162_, v___x_163_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(size_t v_depth_172_, lean_object* v_keys_173_, lean_object* v_vals_174_, lean_object* v_i_175_, lean_object* v_entries_176_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_192_, lean_object* v_keys_193_, lean_object* v_vals_194_, lean_object* v_i_195_, lean_object* v_entries_196_){
_start:
{
size_t v_depth_boxed_197_; lean_object* v_res_198_; 
v_depth_boxed_197_ = lean_unbox_usize(v_depth_192_);
lean_dec(v_depth_192_);
v_res_198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_boxed_197_, v_keys_193_, v_vals_194_, v_i_195_, v_entries_196_);
lean_dec_ref(v_vals_194_);
lean_dec_ref(v_keys_193_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
size_t v_x_3043__boxed_204_; size_t v_x_3044__boxed_205_; lean_object* v_res_206_; 
v_x_3043__boxed_204_ = lean_unbox_usize(v_x_200_);
lean_dec(v_x_200_);
v_x_3044__boxed_205_ = lean_unbox_usize(v_x_201_);
lean_dec(v_x_201_);
v_res_206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_199_, v_x_3043__boxed_204_, v_x_3044__boxed_205_, v_x_202_, v_x_203_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object* v_msgData_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; lean_object* v_env_264_; lean_object* v___x_265_; lean_object* v_mctx_266_; lean_object* v_lctx_267_; lean_object* v_options_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_263_ = lean_st_ref_get(v___y_261_);
v_env_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_ref(v_env_264_);
lean_dec(v___x_263_);
v___x_265_ = lean_st_ref_get(v___y_259_);
v_mctx_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc_ref(v_mctx_266_);
lean_dec(v___x_265_);
v_lctx_267_ = lean_ctor_get(v___y_258_, 2);
v_options_268_ = lean_ctor_get(v___y_260_, 2);
lean_inc_ref(v_options_268_);
lean_inc_ref(v_lctx_267_);
v___x_269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_269_, 0, v_env_264_);
lean_ctor_set(v___x_269_, 1, v_mctx_266_);
lean_ctor_set(v___x_269_, 2, v_lctx_267_);
lean_ctor_set(v___x_269_, 3, v_options_268_);
v___x_270_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_msgData_257_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_278_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_279_; double v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_float_of_nat(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_ref_291_; lean_object* v___x_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_337_; 
v_ref_291_ = lean_ctor_get(v___y_288_, 5);
v___x_292_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_337_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_337_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_337_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v_traceState_298_; lean_object* v_env_299_; lean_object* v_nextMacroScope_300_; lean_object* v_ngen_301_; lean_object* v_auxDeclNGen_302_; lean_object* v_cache_303_; lean_object* v_messages_304_; lean_object* v_infoState_305_; lean_object* v_snapshotTasks_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_336_; 
v___x_297_ = lean_st_ref_take(v___y_289_);
v_traceState_298_ = lean_ctor_get(v___x_297_, 4);
v_env_299_ = lean_ctor_get(v___x_297_, 0);
v_nextMacroScope_300_ = lean_ctor_get(v___x_297_, 1);
v_ngen_301_ = lean_ctor_get(v___x_297_, 2);
v_auxDeclNGen_302_ = lean_ctor_get(v___x_297_, 3);
v_cache_303_ = lean_ctor_get(v___x_297_, 5);
v_messages_304_ = lean_ctor_get(v___x_297_, 6);
v_infoState_305_ = lean_ctor_get(v___x_297_, 7);
v_snapshotTasks_306_ = lean_ctor_get(v___x_297_, 8);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_336_ == 0)
{
v___x_308_ = v___x_297_;
v_isShared_309_ = v_isSharedCheck_336_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snapshotTasks_306_);
lean_inc(v_infoState_305_);
lean_inc(v_messages_304_);
lean_inc(v_cache_303_);
lean_inc(v_traceState_298_);
lean_inc(v_auxDeclNGen_302_);
lean_inc(v_ngen_301_);
lean_inc(v_nextMacroScope_300_);
lean_inc(v_env_299_);
lean_dec(v___x_297_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_336_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
uint64_t v_tid_310_; lean_object* v_traces_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_335_; 
v_tid_310_ = lean_ctor_get_uint64(v_traceState_298_, sizeof(void*)*1);
v_traces_311_ = lean_ctor_get(v_traceState_298_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_traceState_298_);
if (v_isSharedCheck_335_ == 0)
{
v___x_313_ = v_traceState_298_;
v_isShared_314_ = v_isSharedCheck_335_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_traces_311_);
lean_dec(v_traceState_298_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_335_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; double v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_317_ = 0;
v___x_318_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_319_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_319_, 0, v_cls_284_);
lean_ctor_set(v___x_319_, 1, v___x_315_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set_float(v___x_319_, sizeof(void*)*3, v___x_316_);
lean_ctor_set_float(v___x_319_, sizeof(void*)*3 + 8, v___x_316_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*3 + 16, v___x_317_);
v___x_320_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_321_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v_a_293_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_inc(v_ref_291_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_ref_291_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = l_Lean_PersistentArray_push___redArg(v_traces_311_, v___x_322_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_323_);
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_323_);
lean_ctor_set_uint64(v_reuseFailAlloc_334_, sizeof(void*)*1, v_tid_310_);
v___x_325_ = v_reuseFailAlloc_334_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 4, v___x_325_);
v___x_327_ = v___x_308_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_env_299_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_nextMacroScope_300_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_ngen_301_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_auxDeclNGen_302_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v_cache_303_);
lean_ctor_set(v_reuseFailAlloc_333_, 6, v_messages_304_);
lean_ctor_set(v_reuseFailAlloc_333_, 7, v_infoState_305_);
lean_ctor_set(v_reuseFailAlloc_333_, 8, v_snapshotTasks_306_);
v___x_327_ = v_reuseFailAlloc_333_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_328_ = lean_st_ref_set(v___y_289_, v___x_327_);
v___x_329_ = lean_box(0);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_329_);
v___x_331_ = v___x_295_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_338_, v_msg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_345_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_350_ = lean_unsigned_to_nat(2u);
v___x_351_ = lean_unsigned_to_nat(39u);
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_353_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_354_ = l_mkPanicMessageWithDecl(v___x_353_, v___x_352_, v___x_351_, v___x_350_, v___x_349_);
return v___x_354_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_367_ = l_Lean_Name_append(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_374_, lean_object* v_v_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = l_Lean_Level_isMax(v_v_375_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v_v_375_);
lean_dec(v_mvarId_374_);
v___x_382_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_383_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_382_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_mkFreshLevelMVar(v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_options_385_; lean_object* v_a_386_; lean_object* v_inheritedTraceOptions_387_; uint8_t v_hasTrace_388_; lean_object* v___x_389_; 
v_options_385_ = lean_ctor_get(v_a_378_, 2);
v_a_386_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_384_);
v_inheritedTraceOptions_387_ = lean_ctor_get(v_a_378_, 13);
v_hasTrace_388_ = lean_ctor_get_uint8(v_options_385_, sizeof(void*)*1);
v___x_389_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_374_, v_v_375_, v_a_386_);
if (v_hasTrace_388_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_374_, v___x_389_, v_a_377_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_387_, v_options_385_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_374_, v___x_389_, v_a_377_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_374_);
v___x_396_ = l_Lean_mkLevelMVar(v_mvarId_374_);
v___x_397_ = l_Lean_MessageData_ofLevel(v___x_396_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_395_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
lean_inc(v___x_389_);
v___x_401_ = l_Lean_MessageData_ofLevel(v___x_389_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_391_, v___x_402_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
lean_dec_ref(v___x_403_);
v___x_404_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_374_, v___x_389_, v_a_377_);
return v___x_404_;
}
else
{
lean_dec(v___x_389_);
lean_dec(v_mvarId_374_);
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_v_375_);
lean_dec(v_mvarId_374_);
v_a_405_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_384_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_384_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_413_, lean_object* v_v_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_413_, v_v_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_421_, lean_object* v_val_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_421_, v_val_422_, v___y_424_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_429_, lean_object* v_val_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_429_, v_val_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_438_, v_x_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, size_t v_x_444_, size_t v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_443_, v_x_444_, v_x_445_, v_x_446_, v_x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
size_t v_x_3561__boxed_455_; size_t v_x_3562__boxed_456_; lean_object* v_res_457_; 
v_x_3561__boxed_455_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_x_3562__boxed_456_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_res_457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_449_, v_x_450_, v_x_3561__boxed_455_, v_x_3562__boxed_456_, v_x_453_, v_x_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_458_, lean_object* v_n_459_, lean_object* v_k_460_, lean_object* v_v_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_459_, v_k_460_, v_v_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_463_, size_t v_depth_464_, lean_object* v_keys_465_, lean_object* v_vals_466_, lean_object* v_heq_467_, lean_object* v_i_468_, lean_object* v_entries_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_464_, v_keys_465_, v_vals_466_, v_i_468_, v_entries_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_471_, lean_object* v_depth_472_, lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_heq_475_, lean_object* v_i_476_, lean_object* v_entries_477_){
_start:
{
size_t v_depth_boxed_478_; lean_object* v_res_479_; 
v_depth_boxed_478_ = lean_unbox_usize(v_depth_472_);
lean_dec(v_depth_472_);
v_res_479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_471_, v_depth_boxed_478_, v_keys_473_, v_vals_474_, v_heq_475_, v_i_476_, v_entries_477_);
lean_dec_ref(v_vals_474_);
lean_dec_ref(v_keys_473_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_481_, v_x_482_, v_x_483_, v_x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_489_, lean_object* v_v_x27_490_, lean_object* v_mvarId_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
uint8_t v___x_497_; lean_object* v___y_499_; 
v___x_497_ = lean_level_eq(v_u_489_, v_v_x27_490_);
if (v___x_497_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_mvarId_491_);
lean_dec(v_u_489_);
v___x_510_ = lean_box(v___x_497_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_options_512_; uint8_t v_hasTrace_513_; 
v_options_512_ = lean_ctor_get(v_a_494_, 2);
v_hasTrace_513_ = lean_ctor_get_uint8(v_options_512_, sizeof(void*)*1);
if (v_hasTrace_513_ == 0)
{
v___y_499_ = v_a_493_;
goto v___jp_498_;
}
else
{
lean_object* v_inheritedTraceOptions_514_; lean_object* v_cls_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_inheritedTraceOptions_514_ = lean_ctor_get(v_a_494_, 13);
v_cls_515_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_516_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_514_, v_options_512_, v___x_516_);
if (v___x_517_ == 0)
{
v___y_499_ = v_a_493_;
goto v___jp_498_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_518_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_491_);
v___x_519_ = l_Lean_mkLevelMVar(v_mvarId_491_);
v___x_520_ = l_Lean_MessageData_ofLevel(v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_inc(v_u_489_);
v___x_524_ = l_Lean_MessageData_ofLevel(v_u_489_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_515_, v___x_525_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_dec_ref(v___x_526_);
v___y_499_ = v_a_493_;
goto v___jp_498_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_mvarId_491_);
lean_dec(v_u_489_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v___x_500_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_491_, v_u_489_, v___y_499_);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_500_, 0);
lean_dec(v_unused_509_);
v___x_502_ = v___x_500_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_dec(v___x_500_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_box(v___x_497_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_535_, lean_object* v_v_x27_536_, lean_object* v_mvarId_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_535_, v_v_x27_536_, v_mvarId_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_v_x27_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_544_, lean_object* v_v_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
if (lean_obj_tag(v_v_545_) == 2)
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v_v_545_, 1);
lean_inc(v_a_555_);
if (lean_obj_tag(v_a_555_) == 5)
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_556_ = lean_ctor_get(v_v_545_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v_v_545_);
v_a_557_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_a_557_);
lean_dec_ref(v_a_555_);
v___x_558_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_544_, v_a_556_, v_a_557_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_556_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v_v_545_, 0);
lean_inc(v_a_559_);
lean_dec_ref(v_v_545_);
if (lean_obj_tag(v_a_559_) == 5)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v_a_559_);
v___x_561_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_544_, v_a_555_, v_a_560_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_555_);
return v___x_561_;
}
else
{
lean_dec(v_a_559_);
lean_dec(v_a_555_);
lean_dec(v_u_544_);
goto v___jp_551_;
}
}
}
else
{
lean_dec(v_v_545_);
lean_dec(v_u_544_);
goto v___jp_551_;
}
v___jp_551_:
{
uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = 0;
v___x_553_ = lean_box(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_562_, lean_object* v_v_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_562_, v_v_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_573_, lean_object* v_u_u2082_574_, lean_object* v_v_x27_575_, lean_object* v_mvarId_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
uint8_t v___x_582_; uint8_t v___x_583_; lean_object* v___y_585_; lean_object* v___y_597_; 
v___x_582_ = lean_level_eq(v_u_u2081_573_, v_v_x27_575_);
v___x_583_ = 1;
if (v___x_582_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = lean_level_eq(v_u_u2082_574_, v_v_x27_575_);
lean_dec(v_u_u2082_574_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_mvarId_576_);
lean_dec(v_u_u2081_573_);
v___x_609_ = lean_box(v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v_options_611_; uint8_t v_hasTrace_612_; 
v_options_611_ = lean_ctor_get(v_a_579_, 2);
v_hasTrace_612_ = lean_ctor_get_uint8(v_options_611_, sizeof(void*)*1);
if (v_hasTrace_612_ == 0)
{
v___y_597_ = v_a_578_;
goto v___jp_596_;
}
else
{
lean_object* v_inheritedTraceOptions_613_; lean_object* v_cls_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_inheritedTraceOptions_613_ = lean_ctor_get(v_a_579_, 13);
v_cls_614_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_615_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_613_, v_options_611_, v___x_615_);
if (v___x_616_ == 0)
{
v___y_597_ = v_a_578_;
goto v___jp_596_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_617_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_576_);
v___x_618_ = l_Lean_mkLevelMVar(v_mvarId_576_);
v___x_619_ = l_Lean_MessageData_ofLevel(v___x_618_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_617_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_inc(v_u_u2081_573_);
v___x_623_ = l_Lean_MessageData_ofLevel(v_u_u2081_573_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_614_, v___x_624_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec_ref(v___x_625_);
v___y_597_ = v_a_578_;
goto v___jp_596_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_mvarId_576_);
lean_dec(v_u_u2081_573_);
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_634_; uint8_t v_hasTrace_635_; 
lean_dec(v_u_u2081_573_);
v_options_634_ = lean_ctor_get(v_a_579_, 2);
v_hasTrace_635_ = lean_ctor_get_uint8(v_options_634_, sizeof(void*)*1);
if (v_hasTrace_635_ == 0)
{
v___y_585_ = v_a_578_;
goto v___jp_584_;
}
else
{
lean_object* v_inheritedTraceOptions_636_; lean_object* v_cls_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_inheritedTraceOptions_636_ = lean_ctor_get(v_a_579_, 13);
v_cls_637_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_638_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_636_, v_options_634_, v___x_638_);
if (v___x_639_ == 0)
{
v___y_585_ = v_a_578_;
goto v___jp_584_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_640_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_576_);
v___x_641_ = l_Lean_mkLevelMVar(v_mvarId_576_);
v___x_642_ = l_Lean_MessageData_ofLevel(v___x_641_);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_640_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_inc(v_u_u2082_574_);
v___x_646_ = l_Lean_MessageData_ofLevel(v_u_u2082_574_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_637_, v___x_647_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_dec_ref(v___x_648_);
v___y_585_ = v_a_578_;
goto v___jp_584_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_mvarId_576_);
lean_dec(v_u_u2082_574_);
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
v___jp_584_:
{
lean_object* v___x_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v___x_586_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_576_, v_u_u2082_574_, v___y_585_);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_595_);
v___x_588_ = v___x_586_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_dec(v___x_586_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_box(v___x_583_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_606_; 
v___x_598_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_576_, v_u_u2081_573_, v___y_597_);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_598_, 0);
lean_dec(v_unused_607_);
v___x_600_ = v___x_598_;
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
else
{
lean_dec(v___x_598_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_box(v___x_583_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_657_, lean_object* v_u_u2082_658_, lean_object* v_v_x27_659_, lean_object* v_mvarId_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_657_, v_u_u2082_658_, v_v_x27_659_, v_mvarId_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_v_x27_659_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_667_, lean_object* v_v_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
if (lean_obj_tag(v_u_667_) == 2)
{
if (lean_obj_tag(v_v_668_) == 2)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v_v_668_, 1);
lean_inc(v_a_678_);
if (lean_obj_tag(v_a_678_) == 5)
{
lean_object* v_a_679_; lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_679_ = lean_ctor_get(v_u_667_, 0);
lean_inc(v_a_679_);
v_a_680_ = lean_ctor_get(v_u_667_, 1);
lean_inc(v_a_680_);
lean_dec_ref(v_u_667_);
v_a_681_ = lean_ctor_get(v_v_668_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v_v_668_);
v_a_682_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v_a_678_);
v___x_683_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_681_);
return v___x_683_;
}
else
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v_v_668_, 0);
lean_inc(v_a_684_);
lean_dec_ref(v_v_668_);
if (lean_obj_tag(v_a_684_) == 5)
{
lean_object* v_a_685_; lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_685_ = lean_ctor_get(v_u_667_, 0);
lean_inc(v_a_685_);
v_a_686_ = lean_ctor_get(v_u_667_, 1);
lean_inc(v_a_686_);
lean_dec_ref(v_u_667_);
v_a_687_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v_a_684_);
v___x_688_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_685_, v_a_686_, v_a_678_, v_a_687_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_678_);
return v___x_688_;
}
else
{
lean_dec(v_a_684_);
lean_dec(v_a_678_);
lean_dec_ref(v_u_667_);
goto v___jp_674_;
}
}
}
else
{
lean_dec_ref(v_u_667_);
lean_dec(v_v_668_);
goto v___jp_674_;
}
}
else
{
lean_dec(v_v_668_);
lean_dec(v_u_667_);
goto v___jp_674_;
}
v___jp_674_:
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = 0;
v___x_676_ = lean_box(v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_689_, lean_object* v_v_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_689_, v_v_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
return v_res_696_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_704_ = l_Lean_Name_append(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_708_, lean_object* v_rhs_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_options_715_; lean_object* v_ref_716_; lean_object* v_inheritedTraceOptions_717_; lean_object* v___y_719_; uint8_t v_hasTrace_739_; 
v_options_715_ = lean_ctor_get(v_a_712_, 2);
v_ref_716_ = lean_ctor_get(v_a_712_, 5);
v_inheritedTraceOptions_717_ = lean_ctor_get(v_a_712_, 13);
v_hasTrace_739_ = lean_ctor_get_uint8(v_options_715_, sizeof(void*)*1);
if (v_hasTrace_739_ == 0)
{
v___y_719_ = v_a_711_;
goto v___jp_718_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_717_, v_options_715_, v___x_741_);
if (v___x_742_ == 0)
{
v___y_719_ = v_a_711_;
goto v___jp_718_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_inc(v_lhs_708_);
v___x_743_ = l_Lean_MessageData_ofLevel(v_lhs_708_);
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v_rhs_709_);
v___x_746_ = l_Lean_MessageData_ofLevel(v_rhs_709_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_740_, v___x_747_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref(v___x_748_);
v___y_719_ = v_a_711_;
goto v___jp_718_;
}
else
{
lean_dec(v_rhs_709_);
lean_dec(v_lhs_708_);
return v___x_748_;
}
}
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v_mctx_721_; lean_object* v_cache_722_; lean_object* v_zetaDeltaFVarIds_723_; lean_object* v_postponed_724_; lean_object* v_diag_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_738_; 
v___x_720_ = lean_st_ref_take(v___y_719_);
v_mctx_721_ = lean_ctor_get(v___x_720_, 0);
v_cache_722_ = lean_ctor_get(v___x_720_, 1);
v_zetaDeltaFVarIds_723_ = lean_ctor_get(v___x_720_, 2);
v_postponed_724_ = lean_ctor_get(v___x_720_, 3);
v_diag_725_ = lean_ctor_get(v___x_720_, 4);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_738_ == 0)
{
v___x_727_ = v___x_720_;
v_isShared_728_ = v_isSharedCheck_738_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_diag_725_);
lean_inc(v_postponed_724_);
lean_inc(v_zetaDeltaFVarIds_723_);
lean_inc(v_cache_722_);
lean_inc(v_mctx_721_);
lean_dec(v___x_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_738_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_defEqCtx_x3f_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_defEqCtx_x3f_729_ = lean_ctor_get(v_a_710_, 4);
lean_inc(v_defEqCtx_x3f_729_);
lean_inc(v_ref_716_);
v___x_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_730_, 0, v_ref_716_);
lean_ctor_set(v___x_730_, 1, v_lhs_708_);
lean_ctor_set(v___x_730_, 2, v_rhs_709_);
lean_ctor_set(v___x_730_, 3, v_defEqCtx_x3f_729_);
v___x_731_ = l_Lean_PersistentArray_push___redArg(v_postponed_724_, v___x_730_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 3, v___x_731_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_mctx_721_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_cache_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_zetaDeltaFVarIds_723_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_diag_725_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_st_ref_set(v___y_719_, v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_749_, lean_object* v_rhs_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_749_, v_rhs_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_757_, lean_object* v_mvarId_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
if (lean_obj_tag(v_v_757_) == 5)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v_v_757_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v_v_757_);
v___x_765_ = l_Lean_LMVarId_getLevel(v_a_764_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v___x_765_);
v___x_767_ = l_Lean_LMVarId_getLevel(v_mvarId_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_777_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_777_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_nat_dec_lt(v_a_768_, v_a_766_);
lean_dec(v_a_766_);
lean_dec(v_a_768_);
v___x_773_ = lean_box(v___x_772_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_a_766_);
v_a_778_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_767_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_767_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_mvarId_758_);
v_a_786_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_765_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_765_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_mvarId_758_);
lean_dec(v_v_757_);
v___x_794_ = 0;
v___x_795_ = lean_box(v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_797_, lean_object* v_mvarId_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_797_, v_mvarId_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_805_, lean_object* v_v_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___y_813_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_888_; lean_object* v___y_902_; 
switch(lean_obj_tag(v_u_805_))
{
case 5:
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v_u_805_, 0);
lean_inc(v_a_915_);
v___x_916_ = l_Lean_LMVarId_isReadOnly(v_a_915_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_1013_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_1013_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_1013_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
uint8_t v___x_921_; 
v___x_921_ = lean_unbox(v_a_917_);
lean_dec(v_a_917_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_del_object(v___x_919_);
lean_inc(v_a_915_);
lean_inc(v_v_806_);
v___x_922_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_806_, v_a_915_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_999_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_999_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_999_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_999_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
uint8_t v___y_934_; uint8_t v___x_955_; 
v___x_955_ = lean_unbox(v_a_923_);
lean_dec(v_a_923_);
if (v___x_955_ == 0)
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_Level_occurs(v_u_805_, v_v_806_);
if (v___x_956_ == 0)
{
lean_object* v_options_957_; uint8_t v_hasTrace_958_; 
lean_del_object(v___x_925_);
v_options_957_ = lean_ctor_get(v_a_809_, 2);
v_hasTrace_958_ = lean_ctor_get_uint8(v_options_957_, sizeof(void*)*1);
if (v_hasTrace_958_ == 0)
{
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
v___y_888_ = v_a_808_;
goto v___jp_887_;
}
else
{
lean_object* v_inheritedTraceOptions_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_inheritedTraceOptions_959_ = lean_ctor_get(v_a_809_, 13);
v___x_960_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_959_, v_options_957_, v___x_961_);
if (v___x_962_ == 0)
{
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
v___y_888_ = v_a_808_;
goto v___jp_887_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_inc_ref(v_u_805_);
v___x_963_ = l_Lean_MessageData_ofLevel(v_u_805_);
v___x_964_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
lean_inc(v_v_806_);
v___x_966_ = l_Lean_MessageData_ofLevel(v_v_806_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_960_, v___x_967_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_dec_ref(v___x_968_);
v___y_888_ = v_a_808_;
goto v___jp_887_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_u_805_);
lean_dec(v_a_808_);
lean_dec(v_v_806_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
else
{
uint8_t v___x_977_; 
v___x_977_ = l_Lean_Level_isMax(v_v_806_);
if (v___x_977_ == 0)
{
v___y_934_ = v___x_977_;
goto v___jp_933_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_805_, v_v_806_);
if (v___x_978_ == 0)
{
v___y_934_ = v___x_977_;
goto v___jp_933_;
}
else
{
lean_dec_ref(v_u_805_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
goto v___jp_927_;
}
}
}
}
else
{
lean_object* v_options_979_; uint8_t v_hasTrace_980_; 
lean_del_object(v___x_925_);
v_options_979_ = lean_ctor_get(v_a_809_, 2);
v_hasTrace_980_ = lean_ctor_get_uint8(v_options_979_, sizeof(void*)*1);
if (v_hasTrace_980_ == 0)
{
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
v___y_902_ = v_a_808_;
goto v___jp_901_;
}
else
{
lean_object* v_inheritedTraceOptions_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_inheritedTraceOptions_981_ = lean_ctor_get(v_a_809_, 13);
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_983_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_981_, v_options_979_, v___x_983_);
if (v___x_984_ == 0)
{
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
v___y_902_ = v_a_808_;
goto v___jp_901_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc(v_v_806_);
v___x_985_ = l_Lean_MessageData_ofLevel(v_v_806_);
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc_ref(v_u_805_);
v___x_988_ = l_Lean_MessageData_ofLevel(v_u_805_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_982_, v___x_989_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_dec_ref(v___x_990_);
v___y_902_ = v_a_808_;
goto v___jp_901_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_u_805_);
lean_dec(v_a_808_);
lean_dec(v_v_806_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
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
v___jp_927_:
{
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = 2;
v___x_929_ = lean_box(v___x_928_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_929_);
v___x_931_ = v___x_925_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
v___jp_933_:
{
if (v___y_934_ == 0)
{
lean_dec_ref(v_u_805_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
goto v___jp_927_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_925_);
v___x_935_ = l_Lean_Level_mvarId_x21(v_u_805_);
lean_dec_ref(v_u_805_);
v___x_936_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_935_, v_v_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_945_; 
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_936_, 0);
lean_dec(v_unused_946_);
v___x_938_ = v___x_936_;
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
else
{
lean_dec(v___x_936_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = 1;
v___x_941_ = lean_box(v___x_940_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_936_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_936_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_u_805_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
v_a_1000_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_922_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_922_);
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
uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
lean_dec_ref(v_u_805_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
v___x_1008_ = 2;
v___x_1009_ = lean_box(v___x_1008_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_1009_);
v___x_1011_ = v___x_919_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_u_805_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
v_a_1014_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_916_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_916_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_806_))
{
case 5:
{
lean_dec_ref(v_v_806_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
goto v___jp_833_;
}
case 2:
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v_v_806_, 0);
lean_inc(v_a_1022_);
v_a_1023_ = lean_ctor_get(v_v_806_, 1);
lean_inc(v_a_1023_);
lean_dec_ref(v_v_806_);
lean_inc(v_a_810_);
lean_inc_ref(v_a_809_);
lean_inc(v_a_808_);
lean_inc_ref(v_a_807_);
v___x_1024_ = lean_is_level_def_eq(v_u_805_, v_a_1022_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; uint8_t v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
v___x_1026_ = lean_unbox(v_a_1025_);
lean_dec(v_a_1025_);
if (v___x_1026_ == 0)
{
lean_dec(v_a_1023_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
v___y_813_ = v___x_1024_;
goto v___jp_812_;
}
else
{
lean_object* v___x_1027_; 
lean_dec_ref(v___x_1024_);
v___x_1027_ = lean_is_level_def_eq(v_u_805_, v_a_1023_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
v___y_813_ = v___x_1027_;
goto v___jp_812_;
}
}
else
{
lean_dec(v_a_1023_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
v___y_813_ = v___x_1024_;
goto v___jp_812_;
}
}
case 3:
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_a_1028_ = lean_ctor_get(v_v_806_, 1);
lean_inc(v_a_1028_);
lean_dec_ref(v_v_806_);
v___x_1029_ = lean_is_level_def_eq(v_u_805_, v_a_1028_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1040_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
uint8_t v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1034_ = lean_unbox(v_a_1030_);
lean_dec(v_a_1030_);
v___x_1035_ = l_Bool_toLBool(v___x_1034_);
v___x_1036_ = lean_box(v___x_1035_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1036_);
v___x_1038_ = v___x_1032_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1029_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1029_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
case 1:
{
uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_v_806_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
v___x_1049_ = 0;
v___x_1050_ = lean_box(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
default: 
{
v___y_842_ = v_a_807_;
v___y_843_ = v_a_808_;
v___y_844_ = v_a_809_;
v___y_845_ = v_a_810_;
goto v___jp_841_;
}
}
}
case 1:
{
lean_object* v_a_1052_; uint8_t v___y_1054_; 
v_a_1052_ = lean_ctor_get(v_u_805_, 0);
lean_inc(v_a_1052_);
lean_dec_ref(v_u_805_);
if (lean_obj_tag(v_v_806_) == 5)
{
lean_dec_ref(v_v_806_);
lean_dec(v_a_1052_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
goto v___jp_833_;
}
else
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Level_isParam(v_v_806_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Lean_Level_isMVar(v_a_1052_);
if (v___x_1099_ == 0)
{
v___y_1054_ = v___x_1099_;
goto v___jp_1053_;
}
else
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Lean_Level_occurs(v_a_1052_, v_v_806_);
v___y_1054_ = v___x_1100_;
goto v___jp_1053_;
}
}
else
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_a_1052_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
v___x_1101_ = 0;
v___x_1102_ = lean_box(v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
v___jp_1053_:
{
if (v___y_1054_ == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Meta_decLevel_x3f(v_v_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1086_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1086_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1086_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
if (lean_obj_tag(v_a_1056_) == 0)
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_a_1052_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
v___x_1060_ = 2;
v___x_1061_ = lean_box(v___x_1060_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1061_);
v___x_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_1058_);
v_val_1065_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_val_1065_);
lean_dec_ref(v_a_1056_);
v___x_1066_ = lean_is_level_def_eq(v_a_1052_, v_val_1065_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1077_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1077_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1077_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
uint8_t v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1071_ = lean_unbox(v_a_1067_);
lean_dec(v_a_1067_);
v___x_1072_ = l_Bool_toLBool(v___x_1071_);
v___x_1073_ = lean_box(v___x_1072_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1073_);
v___x_1075_ = v___x_1069_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1066_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1066_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_1052_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
v_a_1087_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1055_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1055_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_a_1052_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
v___x_1095_ = 2;
v___x_1096_ = lean_box(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_806_) == 5)
{
lean_dec_ref(v_v_806_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_u_805_);
goto v___jp_833_;
}
else
{
v___y_842_ = v_a_807_;
v___y_843_ = v_a_808_;
v___y_844_ = v_a_809_;
v___y_845_ = v_a_810_;
goto v___jp_841_;
}
}
}
v___jp_812_:
{
if (lean_obj_tag(v___y_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_824_; 
v_a_814_ = lean_ctor_get(v___y_813_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___y_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_816_ = v___y_813_;
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___y_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_818_ = lean_unbox(v_a_814_);
lean_dec(v_a_814_);
v___x_819_ = l_Bool_toLBool(v___x_818_);
v___x_820_ = lean_box(v___x_819_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
v_a_825_ = lean_ctor_get(v___y_813_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___y_813_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___y_813_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___y_813_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
v___jp_833_:
{
uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = 2;
v___x_835_ = lean_box(v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
v___jp_837_:
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 2;
v___x_839_ = lean_box(v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
v___jp_841_:
{
uint8_t v_univApprox_846_; 
v_univApprox_846_ = lean_ctor_get_uint8(v___y_842_, sizeof(void*)*7 + 1);
if (v_univApprox_846_ == 0)
{
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_v_806_);
lean_dec(v_u_805_);
goto v___jp_837_;
}
else
{
lean_object* v___x_847_; 
lean_inc(v_v_806_);
lean_inc(v_u_805_);
v___x_847_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_805_, v_v_806_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_878_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_878_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_878_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_878_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_del_object(v___x_850_);
v___x_853_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_805_, v_v_806_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; 
v___x_858_ = lean_unbox(v_a_854_);
lean_dec(v_a_854_);
if (v___x_858_ == 0)
{
lean_del_object(v___x_856_);
goto v___jp_837_;
}
else
{
uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_859_ = 1;
v___x_860_ = lean_box(v___x_859_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_853_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_853_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_v_806_);
lean_dec(v_u_805_);
v___x_873_ = 1;
v___x_874_ = lean_box(v___x_873_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_874_);
v___x_876_ = v___x_850_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_v_806_);
lean_dec(v_u_805_);
v_a_879_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_847_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_847_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
v___jp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_899_; 
v___x_889_ = l_Lean_Level_mvarId_x21(v_u_805_);
lean_dec(v_u_805_);
v___x_890_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_889_, v_v_806_, v___y_888_);
lean_dec(v___y_888_);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_890_, 0);
lean_dec(v_unused_900_);
v___x_892_ = v___x_890_;
v_isShared_893_ = v_isSharedCheck_899_;
goto v_resetjp_891_;
}
else
{
lean_dec(v___x_890_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_899_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_894_ = 1;
v___x_895_ = lean_box(v___x_894_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_895_);
v___x_897_ = v___x_892_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
v___jp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_913_; 
v___x_903_ = l_Lean_Level_mvarId_x21(v_v_806_);
lean_dec(v_v_806_);
v___x_904_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_903_, v_u_805_, v___y_902_);
lean_dec(v___y_902_);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_914_);
v___x_906_ = v___x_904_;
v_isShared_907_ = v_isSharedCheck_913_;
goto v_resetjp_905_;
}
else
{
lean_dec(v___x_904_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_913_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_908_ = 1;
v___x_909_ = lean_box(v___x_908_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1104_, lean_object* v_v_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1104_, v_v_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_mctx_1116_; lean_object* v___x_1117_; lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1120_; lean_object* v_cache_1121_; lean_object* v_zetaDeltaFVarIds_1122_; lean_object* v_postponed_1123_; lean_object* v_diag_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v___x_1115_ = lean_st_ref_get(v___y_1113_);
v_mctx_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_mctx_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = lean_instantiate_level_mvars(v_mctx_1116_, v_l_1112_);
v_fst_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_fst_1118_);
v_snd_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_snd_1119_);
lean_dec_ref(v___x_1117_);
v___x_1120_ = lean_st_ref_take(v___y_1113_);
v_cache_1121_ = lean_ctor_get(v___x_1120_, 1);
v_zetaDeltaFVarIds_1122_ = lean_ctor_get(v___x_1120_, 2);
v_postponed_1123_ = lean_ctor_get(v___x_1120_, 3);
v_diag_1124_ = lean_ctor_get(v___x_1120_, 4);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1120_, 0);
lean_dec(v_unused_1134_);
v___x_1126_ = v___x_1120_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_diag_1124_);
lean_inc(v_postponed_1123_);
lean_inc(v_zetaDeltaFVarIds_1122_);
lean_inc(v_cache_1121_);
lean_dec(v___x_1120_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_fst_1118_);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_fst_1118_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_cache_1121_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_zetaDeltaFVarIds_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_postponed_1123_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_diag_1124_);
v___x_1129_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_st_ref_set(v___y_1113_, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_snd_1119_);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1135_, v___y_1136_);
lean_dec(v___y_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1139_, v___y_1141_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1152_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_unsigned_to_nat(32u);
v___x_1154_ = lean_mk_empty_array_with_capacity(v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1156_ = ((size_t)5ULL);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_unsigned_to_nat(32u);
v___x_1159_ = lean_mk_empty_array_with_capacity(v___x_1158_);
v___x_1160_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1161_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v___x_1157_);
lean_ctor_set(v___x_1161_, 3, v___x_1157_);
lean_ctor_set_usize(v___x_1161_, 4, v___x_1156_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v_traceState_1165_; lean_object* v_traces_1166_; lean_object* v___x_1167_; lean_object* v_traceState_1168_; lean_object* v_env_1169_; lean_object* v_nextMacroScope_1170_; lean_object* v_ngen_1171_; lean_object* v_auxDeclNGen_1172_; lean_object* v_cache_1173_; lean_object* v_messages_1174_; lean_object* v_infoState_1175_; lean_object* v_snapshotTasks_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1195_; 
v___x_1164_ = lean_st_ref_get(v___y_1162_);
v_traceState_1165_ = lean_ctor_get(v___x_1164_, 4);
lean_inc_ref(v_traceState_1165_);
lean_dec(v___x_1164_);
v_traces_1166_ = lean_ctor_get(v_traceState_1165_, 0);
lean_inc_ref(v_traces_1166_);
lean_dec_ref(v_traceState_1165_);
v___x_1167_ = lean_st_ref_take(v___y_1162_);
v_traceState_1168_ = lean_ctor_get(v___x_1167_, 4);
v_env_1169_ = lean_ctor_get(v___x_1167_, 0);
v_nextMacroScope_1170_ = lean_ctor_get(v___x_1167_, 1);
v_ngen_1171_ = lean_ctor_get(v___x_1167_, 2);
v_auxDeclNGen_1172_ = lean_ctor_get(v___x_1167_, 3);
v_cache_1173_ = lean_ctor_get(v___x_1167_, 5);
v_messages_1174_ = lean_ctor_get(v___x_1167_, 6);
v_infoState_1175_ = lean_ctor_get(v___x_1167_, 7);
v_snapshotTasks_1176_ = lean_ctor_get(v___x_1167_, 8);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1178_ = v___x_1167_;
v_isShared_1179_ = v_isSharedCheck_1195_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_snapshotTasks_1176_);
lean_inc(v_infoState_1175_);
lean_inc(v_messages_1174_);
lean_inc(v_cache_1173_);
lean_inc(v_traceState_1168_);
lean_inc(v_auxDeclNGen_1172_);
lean_inc(v_ngen_1171_);
lean_inc(v_nextMacroScope_1170_);
lean_inc(v_env_1169_);
lean_dec(v___x_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1195_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint64_t v_tid_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1193_; 
v_tid_1180_ = lean_ctor_get_uint64(v_traceState_1168_, sizeof(void*)*1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_traceState_1168_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_traceState_1168_, 0);
lean_dec(v_unused_1194_);
v___x_1182_ = v_traceState_1168_;
v_isShared_1183_ = v_isSharedCheck_1193_;
goto v_resetjp_1181_;
}
else
{
lean_dec(v_traceState_1168_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1193_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1184_);
lean_ctor_set_uint64(v_reuseFailAlloc_1192_, sizeof(void*)*1, v_tid_1180_);
v___x_1186_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v___x_1186_);
v___x_1188_ = v___x_1178_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_env_1169_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_nextMacroScope_1170_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_ngen_1171_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_auxDeclNGen_1172_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 5, v_cache_1173_);
lean_ctor_set(v_reuseFailAlloc_1191_, 6, v_messages_1174_);
lean_ctor_set(v_reuseFailAlloc_1191_, 7, v_infoState_1175_);
lean_ctor_set(v_reuseFailAlloc_1191_, 8, v_snapshotTasks_1176_);
v___x_1188_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_st_ref_set(v___y_1162_, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_traces_1166_);
return v___x_1190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1196_);
lean_dec(v___y_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1211_, lean_object* v_k_1212_, uint8_t v_v_1213_){
_start:
{
lean_object* v_map_1214_; uint8_t v_hasTrace_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1229_; 
v_map_1214_ = lean_ctor_get(v_o_1211_, 0);
v_hasTrace_1215_ = lean_ctor_get_uint8(v_o_1211_, sizeof(void*)*1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_o_1211_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1217_ = v_o_1211_;
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_map_1214_);
lean_dec(v_o_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1219_, 0, v_v_1213_);
lean_inc(v_k_1212_);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1212_, v___x_1219_, v_map_1214_);
if (v_hasTrace_1215_ == 0)
{
lean_object* v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1224_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1222_ = l_Lean_Name_isPrefixOf(v___x_1221_, v_k_1212_);
lean_dec(v_k_1212_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1224_ = v___x_1217_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1220_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*1, v___x_1222_);
return v___x_1224_;
}
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_k_1212_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1227_ = v___x_1217_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1, v_hasTrace_1215_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1230_, lean_object* v_k_1231_, lean_object* v_v_1232_){
_start:
{
uint8_t v_v_boxed_1233_; lean_object* v_res_1234_; 
v_v_boxed_1233_ = lean_unbox(v_v_1232_);
v_res_1234_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1230_, v_k_1231_, v_v_boxed_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1235_, lean_object* v_opt_1236_){
_start:
{
lean_object* v_name_1237_; lean_object* v_defValue_1238_; lean_object* v_map_1239_; lean_object* v___x_1240_; 
v_name_1237_ = lean_ctor_get(v_opt_1236_, 0);
v_defValue_1238_ = lean_ctor_get(v_opt_1236_, 1);
v_map_1239_ = lean_ctor_get(v_opts_1235_, 0);
v___x_1240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1239_, v_name_1237_);
if (lean_obj_tag(v___x_1240_) == 0)
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_unbox(v_defValue_1238_);
return v___x_1241_;
}
else
{
lean_object* v_val_1242_; 
v_val_1242_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_val_1242_);
lean_dec_ref(v___x_1240_);
if (lean_obj_tag(v_val_1242_) == 1)
{
uint8_t v_v_1243_; 
v_v_1243_ = lean_ctor_get_uint8(v_val_1242_, 0);
lean_dec_ref(v_val_1242_);
return v_v_1243_;
}
else
{
uint8_t v___x_1244_; 
lean_dec(v_val_1242_);
v___x_1244_ = lean_unbox(v_defValue_1238_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1245_, lean_object* v_opt_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1245_, v_opt_1246_);
lean_dec_ref(v_opt_1246_);
lean_dec_ref(v_opts_1245_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1249_, lean_object* v_opt_1250_){
_start:
{
lean_object* v_name_1251_; lean_object* v_defValue_1252_; lean_object* v_map_1253_; lean_object* v___x_1254_; 
v_name_1251_ = lean_ctor_get(v_opt_1250_, 0);
v_defValue_1252_ = lean_ctor_get(v_opt_1250_, 1);
v_map_1253_ = lean_ctor_get(v_opts_1249_, 0);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1253_, v_name_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_inc(v_defValue_1252_);
return v_defValue_1252_;
}
else
{
lean_object* v_val_1255_; 
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref(v___x_1254_);
if (lean_obj_tag(v_val_1255_) == 3)
{
lean_object* v_v_1256_; 
v_v_1256_ = lean_ctor_get(v_val_1255_, 0);
lean_inc(v_v_1256_);
lean_dec_ref(v_val_1255_);
return v_v_1256_;
}
else
{
lean_dec(v_val_1255_);
lean_inc(v_defValue_1252_);
return v_defValue_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1257_, lean_object* v_opt_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1257_, v_opt_1258_);
lean_dec_ref(v_opt_1258_);
lean_dec_ref(v_opts_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1260_, lean_object* v_lhs_1261_, lean_object* v_rhs_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, uint8_t v___x_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___y_1298_; 
if (v___x_1260_ == 0)
{
lean_object* v___x_1335_; lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
lean_inc(v_lhs_1261_);
v___x_1335_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1261_, v___y_1267_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref(v___x_1335_);
lean_inc(v_rhs_1262_);
v___x_1337_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1262_, v___y_1267_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Lean_Level_normalize(v_a_1336_);
lean_dec(v_a_1336_);
v___x_1340_ = l_Lean_Level_normalize(v_a_1338_);
lean_dec(v_a_1338_);
v___x_1341_ = lean_level_eq(v_lhs_1261_, v___x_1339_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
v___x_1342_ = lean_is_level_def_eq(v___x_1339_, v___x_1340_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1342_;
}
else
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_level_eq(v_rhs_1262_, v___x_1340_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
v___x_1344_ = lean_is_level_def_eq(v___x_1339_, v___x_1340_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; 
lean_dec(v___x_1340_);
lean_dec(v___x_1339_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v_rhs_1262_);
lean_inc(v_lhs_1261_);
v___x_1345_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1261_, v_rhs_1262_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1387_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1387_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1387_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint8_t v___x_1350_; uint8_t v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = 2;
v___x_1351_ = lean_unbox(v_a_1346_);
v___x_1352_ = l_Lean_instBEqLBool_beq(v___x_1351_, v___x_1350_);
if (v___x_1352_ == 0)
{
uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v___x_1353_ = 1;
v___x_1354_ = lean_unbox(v_a_1346_);
lean_dec(v_a_1346_);
v___x_1355_ = l_Lean_instBEqLBool_beq(v___x_1354_, v___x_1353_);
v___x_1356_ = lean_box(v___x_1355_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1356_);
v___x_1358_ = v___x_1348_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_object* v___x_1360_; 
lean_del_object(v___x_1348_);
lean_dec(v_a_1346_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v_lhs_1261_);
lean_inc(v_rhs_1262_);
v___x_1360_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1262_, v_lhs_1261_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1378_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1378_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1378_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint8_t v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_unbox(v_a_1361_);
v___x_1366_ = l_Lean_instBEqLBool_beq(v___x_1365_, v___x_1350_);
if (v___x_1366_ == 0)
{
uint8_t v___x_1367_; uint8_t v___x_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v___x_1367_ = 1;
v___x_1368_ = lean_unbox(v_a_1361_);
lean_dec(v_a_1361_);
v___x_1369_ = l_Lean_instBEqLBool_beq(v___x_1368_, v___x_1367_);
v___x_1370_ = lean_box(v___x_1369_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1370_);
v___x_1372_ = v___x_1363_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v___x_1374_; 
lean_del_object(v___x_1363_);
lean_dec(v_a_1361_);
lean_inc(v_lhs_1261_);
v___x_1374_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1261_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; uint8_t v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
v___x_1376_ = lean_unbox(v_a_1375_);
lean_dec(v_a_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref(v___x_1374_);
lean_inc(v_rhs_1262_);
v___x_1377_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1262_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
v___y_1298_ = v___x_1377_;
goto v___jp_1297_;
}
else
{
v___y_1298_ = v___x_1374_;
goto v___jp_1297_;
}
}
else
{
v___y_1298_ = v___x_1374_;
goto v___jp_1297_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v_a_1379_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1360_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1360_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v_a_1388_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1345_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1345_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
v___x_1396_ = l_Lean_Level_getOffset(v_lhs_1261_);
lean_dec(v_lhs_1261_);
v___x_1397_ = l_Lean_Level_getOffset(v_rhs_1262_);
lean_dec(v_rhs_1262_);
v___x_1398_ = lean_nat_dec_eq(v___x_1396_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
v___jp_1271_:
{
lean_object* v_options_1272_; uint8_t v_hasTrace_1273_; 
v_options_1272_ = lean_ctor_get(v___y_1268_, 2);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_options_1272_, sizeof(void*)*1);
if (v_hasTrace_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v___x_1274_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1274_;
}
else
{
lean_object* v_inheritedTraceOptions_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_inheritedTraceOptions_1275_ = lean_ctor_get(v___y_1268_, 13);
v___x_1276_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1277_ = l_Lean_Name_mkStr3(v___x_1263_, v___x_1264_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1277_);
v___x_1279_ = l_Lean_Name_append(v___x_1278_, v___x_1277_);
v___x_1280_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1275_, v_options_1272_, v___x_1279_);
lean_dec(v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec(v___x_1277_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v___x_1281_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1282_ = l_Lean_MessageData_ofLevel(v_lhs_1261_);
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_MessageData_ofLevel(v_rhs_1262_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1277_, v___x_1286_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1288_; 
lean_dec_ref(v___x_1287_);
v___x_1288_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1287_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
v___jp_1297_:
{
if (lean_obj_tag(v___y_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1334_; 
v_a_1299_ = lean_ctor_get(v___y_1298_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___y_1298_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1301_ = v___y_1298_;
v_isShared_1302_ = v_isSharedCheck_1334_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___y_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1334_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; uint8_t v_isDefEqStuckEx_1305_; 
v___x_1304_ = l_Lean_Meta_Context_config(v___y_1266_);
v_isDefEqStuckEx_1305_ = lean_ctor_get_uint8(v___x_1304_, 4);
lean_dec_ref(v___x_1304_);
if (v_isDefEqStuckEx_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v___x_1306_ = lean_box(v_isDefEqStuckEx_1305_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1306_);
v___x_1308_ = v___x_1301_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Level_isMVar(v_lhs_1261_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_Level_isMVar(v_rhs_1262_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
v___x_1312_ = lean_box(v___x_1311_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1312_);
v___x_1314_ = v___x_1301_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
else
{
lean_del_object(v___x_1301_);
goto v___jp_1271_;
}
}
else
{
lean_del_object(v___x_1301_);
goto v___jp_1271_;
}
}
}
else
{
lean_object* v___x_1316_; 
lean_del_object(v___x_1301_);
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
v___x_1316_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1261_, v_rhs_1262_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1316_, 0);
lean_dec(v_unused_1325_);
v___x_1318_ = v___x_1316_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v___x_1316_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(v___x_1265_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1316_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v_rhs_1262_);
lean_dec(v_lhs_1261_);
return v___y_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1401_, lean_object* v_lhs_1402_, lean_object* v_rhs_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___x_15019__boxed_1412_; uint8_t v___x_15022__boxed_1413_; lean_object* v_res_1414_; 
v___x_15019__boxed_1412_ = lean_unbox(v___x_1401_);
v___x_15022__boxed_1413_ = lean_unbox(v___x_1406_);
v_res_1414_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_15019__boxed_1412_, v_lhs_1402_, v_rhs_1403_, v___x_1404_, v___x_1405_, v___x_15022__boxed_1413_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_a_1417_ = lean_ctor_get(v_x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v_x_1415_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v_x_1415_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 1);
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v_x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v_x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v_x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 0);
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg___boxed(lean_object* v_x_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_x_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(size_t v_sz_1436_, size_t v_i_1437_, lean_object* v_bs_1438_){
_start:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_usize_dec_lt(v_i_1437_, v_sz_1436_);
if (v___x_1439_ == 0)
{
return v_bs_1438_;
}
else
{
lean_object* v_v_1440_; lean_object* v_msg_1441_; lean_object* v___x_1442_; lean_object* v_bs_x27_1443_; size_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; 
v_v_1440_ = lean_array_uget_borrowed(v_bs_1438_, v_i_1437_);
v_msg_1441_ = lean_ctor_get(v_v_1440_, 1);
lean_inc_ref(v_msg_1441_);
v___x_1442_ = lean_unsigned_to_nat(0u);
v_bs_x27_1443_ = lean_array_uset(v_bs_1438_, v_i_1437_, v___x_1442_);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_add(v_i_1437_, v___x_1444_);
v___x_1446_ = lean_array_uset(v_bs_x27_1443_, v_i_1437_, v_msg_1441_);
v_i_1437_ = v___x_1445_;
v_bs_1438_ = v___x_1446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_1448_, lean_object* v_i_1449_, lean_object* v_bs_1450_){
_start:
{
size_t v_sz_boxed_1451_; size_t v_i_boxed_1452_; lean_object* v_res_1453_; 
v_sz_boxed_1451_ = lean_unbox_usize(v_sz_1448_);
lean_dec(v_sz_1448_);
v_i_boxed_1452_ = lean_unbox_usize(v_i_1449_);
lean_dec(v_i_1449_);
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(v_sz_boxed_1451_, v_i_boxed_1452_, v_bs_1450_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_oldTraces_1454_, lean_object* v_data_1455_, lean_object* v_ref_1456_, lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_fileName_1463_; lean_object* v_fileMap_1464_; lean_object* v_options_1465_; lean_object* v_currRecDepth_1466_; lean_object* v_maxRecDepth_1467_; lean_object* v_ref_1468_; lean_object* v_currNamespace_1469_; lean_object* v_openDecls_1470_; lean_object* v_initHeartbeats_1471_; lean_object* v_maxHeartbeats_1472_; lean_object* v_quotContext_1473_; lean_object* v_currMacroScope_1474_; uint8_t v_diag_1475_; lean_object* v_cancelTk_x3f_1476_; uint8_t v_suppressElabErrors_1477_; lean_object* v_inheritedTraceOptions_1478_; lean_object* v___x_1479_; lean_object* v_traceState_1480_; lean_object* v_traces_1481_; lean_object* v_ref_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; size_t v_sz_1485_; size_t v___x_1486_; lean_object* v___x_1487_; lean_object* v_msg_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1527_; 
v_fileName_1463_ = lean_ctor_get(v___y_1460_, 0);
v_fileMap_1464_ = lean_ctor_get(v___y_1460_, 1);
v_options_1465_ = lean_ctor_get(v___y_1460_, 2);
v_currRecDepth_1466_ = lean_ctor_get(v___y_1460_, 3);
v_maxRecDepth_1467_ = lean_ctor_get(v___y_1460_, 4);
v_ref_1468_ = lean_ctor_get(v___y_1460_, 5);
v_currNamespace_1469_ = lean_ctor_get(v___y_1460_, 6);
v_openDecls_1470_ = lean_ctor_get(v___y_1460_, 7);
v_initHeartbeats_1471_ = lean_ctor_get(v___y_1460_, 8);
v_maxHeartbeats_1472_ = lean_ctor_get(v___y_1460_, 9);
v_quotContext_1473_ = lean_ctor_get(v___y_1460_, 10);
v_currMacroScope_1474_ = lean_ctor_get(v___y_1460_, 11);
v_diag_1475_ = lean_ctor_get_uint8(v___y_1460_, sizeof(void*)*14);
v_cancelTk_x3f_1476_ = lean_ctor_get(v___y_1460_, 12);
v_suppressElabErrors_1477_ = lean_ctor_get_uint8(v___y_1460_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1478_ = lean_ctor_get(v___y_1460_, 13);
v___x_1479_ = lean_st_ref_get(v___y_1461_);
v_traceState_1480_ = lean_ctor_get(v___x_1479_, 4);
lean_inc_ref(v_traceState_1480_);
lean_dec(v___x_1479_);
v_traces_1481_ = lean_ctor_get(v_traceState_1480_, 0);
lean_inc_ref(v_traces_1481_);
lean_dec_ref(v_traceState_1480_);
v_ref_1482_ = l_Lean_replaceRef(v_ref_1456_, v_ref_1468_);
lean_inc_ref(v_inheritedTraceOptions_1478_);
lean_inc(v_cancelTk_x3f_1476_);
lean_inc(v_currMacroScope_1474_);
lean_inc(v_quotContext_1473_);
lean_inc(v_maxHeartbeats_1472_);
lean_inc(v_initHeartbeats_1471_);
lean_inc(v_openDecls_1470_);
lean_inc(v_currNamespace_1469_);
lean_inc(v_maxRecDepth_1467_);
lean_inc(v_currRecDepth_1466_);
lean_inc_ref(v_options_1465_);
lean_inc_ref(v_fileMap_1464_);
lean_inc_ref(v_fileName_1463_);
v___x_1483_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1483_, 0, v_fileName_1463_);
lean_ctor_set(v___x_1483_, 1, v_fileMap_1464_);
lean_ctor_set(v___x_1483_, 2, v_options_1465_);
lean_ctor_set(v___x_1483_, 3, v_currRecDepth_1466_);
lean_ctor_set(v___x_1483_, 4, v_maxRecDepth_1467_);
lean_ctor_set(v___x_1483_, 5, v_ref_1482_);
lean_ctor_set(v___x_1483_, 6, v_currNamespace_1469_);
lean_ctor_set(v___x_1483_, 7, v_openDecls_1470_);
lean_ctor_set(v___x_1483_, 8, v_initHeartbeats_1471_);
lean_ctor_set(v___x_1483_, 9, v_maxHeartbeats_1472_);
lean_ctor_set(v___x_1483_, 10, v_quotContext_1473_);
lean_ctor_set(v___x_1483_, 11, v_currMacroScope_1474_);
lean_ctor_set(v___x_1483_, 12, v_cancelTk_x3f_1476_);
lean_ctor_set(v___x_1483_, 13, v_inheritedTraceOptions_1478_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*14, v_diag_1475_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*14 + 1, v_suppressElabErrors_1477_);
v___x_1484_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1481_);
lean_dec_ref(v_traces_1481_);
v_sz_1485_ = lean_array_size(v___x_1484_);
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(v_sz_1485_, v___x_1486_, v___x_1484_);
v_msg_1488_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1488_, 0, v_data_1455_);
lean_ctor_set(v_msg_1488_, 1, v_msg_1457_);
lean_ctor_set(v_msg_1488_, 2, v___x_1487_);
v___x_1489_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1488_, v___y_1458_, v___y_1459_, v___x_1483_, v___y_1461_);
lean_dec_ref(v___x_1483_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1527_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1527_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v_traceState_1495_; lean_object* v_env_1496_; lean_object* v_nextMacroScope_1497_; lean_object* v_ngen_1498_; lean_object* v_auxDeclNGen_1499_; lean_object* v_cache_1500_; lean_object* v_messages_1501_; lean_object* v_infoState_1502_; lean_object* v_snapshotTasks_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1526_; 
v___x_1494_ = lean_st_ref_take(v___y_1461_);
v_traceState_1495_ = lean_ctor_get(v___x_1494_, 4);
v_env_1496_ = lean_ctor_get(v___x_1494_, 0);
v_nextMacroScope_1497_ = lean_ctor_get(v___x_1494_, 1);
v_ngen_1498_ = lean_ctor_get(v___x_1494_, 2);
v_auxDeclNGen_1499_ = lean_ctor_get(v___x_1494_, 3);
v_cache_1500_ = lean_ctor_get(v___x_1494_, 5);
v_messages_1501_ = lean_ctor_get(v___x_1494_, 6);
v_infoState_1502_ = lean_ctor_get(v___x_1494_, 7);
v_snapshotTasks_1503_ = lean_ctor_get(v___x_1494_, 8);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1505_ = v___x_1494_;
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_snapshotTasks_1503_);
lean_inc(v_infoState_1502_);
lean_inc(v_messages_1501_);
lean_inc(v_cache_1500_);
lean_inc(v_traceState_1495_);
lean_inc(v_auxDeclNGen_1499_);
lean_inc(v_ngen_1498_);
lean_inc(v_nextMacroScope_1497_);
lean_inc(v_env_1496_);
lean_dec(v___x_1494_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1526_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
uint64_t v_tid_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1524_; 
v_tid_1507_ = lean_ctor_get_uint64(v_traceState_1495_, sizeof(void*)*1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_traceState_1495_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v_traceState_1495_, 0);
lean_dec(v_unused_1525_);
v___x_1509_ = v_traceState_1495_;
v_isShared_1510_ = v_isSharedCheck_1524_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_traceState_1495_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1524_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_ref_1456_);
lean_ctor_set(v___x_1511_, 1, v_a_1490_);
v___x_1512_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1454_, v___x_1511_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1512_);
v___x_1514_ = v___x_1509_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1512_);
lean_ctor_set_uint64(v_reuseFailAlloc_1523_, sizeof(void*)*1, v_tid_1507_);
v___x_1514_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v___x_1514_);
v___x_1516_ = v___x_1505_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_env_1496_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_nextMacroScope_1497_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_ngen_1498_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_auxDeclNGen_1499_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1522_, 5, v_cache_1500_);
lean_ctor_set(v_reuseFailAlloc_1522_, 6, v_messages_1501_);
lean_ctor_set(v_reuseFailAlloc_1522_, 7, v_infoState_1502_);
lean_ctor_set(v_reuseFailAlloc_1522_, 8, v_snapshotTasks_1503_);
v___x_1516_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1517_ = lean_st_ref_set(v___y_1461_, v___x_1516_);
v___x_1518_ = lean_box(0);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1518_);
v___x_1520_ = v___x_1492_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_oldTraces_1528_, lean_object* v_data_1529_, lean_object* v_ref_1530_, lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_oldTraces_1528_, v_data_1529_, v_ref_1530_, v_msg_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_e_1538_){
_start:
{
if (lean_obj_tag(v_e_1538_) == 0)
{
uint8_t v___x_1539_; 
v___x_1539_ = 2;
return v___x_1539_;
}
else
{
lean_object* v_a_1540_; uint8_t v___x_1541_; 
v_a_1540_ = lean_ctor_get(v_e_1538_, 0);
v___x_1541_ = lean_unbox(v_a_1540_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; 
v___x_1542_ = 1;
return v___x_1542_;
}
else
{
uint8_t v___x_1543_; 
v___x_1543_ = 0;
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_e_1544_){
_start:
{
uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_res_1545_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_e_1544_);
lean_dec_ref(v_e_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1550_; double v___x_1551_; 
v___x_1550_ = lean_unsigned_to_nat(1000u);
v___x_1551_ = lean_float_of_nat(v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1552_, uint8_t v_collapsed_1553_, lean_object* v_tag_1554_, lean_object* v_opts_1555_, uint8_t v_clsEnabled_1556_, lean_object* v_oldTraces_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v_resStartStop_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1657_; 
v_fst_1566_ = lean_ctor_get(v_resStartStop_1560_, 0);
v_snd_1567_ = lean_ctor_get(v_resStartStop_1560_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_resStartStop_1560_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1569_ = v_resStartStop_1560_;
v_isShared_1570_ = v_isSharedCheck_1657_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1567_);
lean_inc(v_fst_1566_);
lean_dec(v_resStartStop_1560_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1657_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___y_1572_; lean_object* v_data_1573_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1656_; 
v_fst_1584_ = lean_ctor_get(v_snd_1567_, 0);
v_snd_1585_ = lean_ctor_get(v_snd_1567_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_snd_1567_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1587_ = v_snd_1567_;
v_isShared_1588_ = v_isSharedCheck_1656_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_inc(v_fst_1584_);
lean_dec(v_snd_1567_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1656_;
goto v_resetjp_1586_;
}
v___jp_1571_:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_oldTraces_1557_, v_data_1573_, v_ref_1558_, v___y_1572_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v___x_1574_);
v___x_1575_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_fst_1566_);
return v___x_1575_;
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_fst_1566_);
v_a_1576_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1574_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; uint8_t v___x_1590_; uint8_t v___y_1610_; double v___y_1641_; 
v___x_1589_ = l_Lean_trace_profiler;
v___x_1590_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1555_, v___x_1589_);
if (v___x_1590_ == 0)
{
v___y_1610_ = v___x_1590_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1647_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1555_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; double v___x_1650_; double v___x_1651_; double v___x_1652_; 
v___x_1648_ = l_Lean_trace_profiler_threshold;
v___x_1649_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1555_, v___x_1648_);
v___x_1650_ = lean_float_of_nat(v___x_1649_);
v___x_1651_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2);
v___x_1652_ = lean_float_div(v___x_1650_, v___x_1651_);
v___y_1641_ = v___x_1652_;
goto v___jp_1640_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; double v___x_1655_; 
v___x_1653_ = l_Lean_trace_profiler_threshold;
v___x_1654_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1555_, v___x_1653_);
v___x_1655_ = lean_float_of_nat(v___x_1654_);
v___y_1641_ = v___x_1655_;
goto v___jp_1640_;
}
}
v___jp_1591_:
{
uint8_t v_result_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v_result_1592_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_fst_1566_);
v___x_1593_ = l_Lean_TraceResult_toEmoji(v_result_1592_);
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
v___x_1595_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 7);
lean_ctor_set(v___x_1587_, 1, v___x_1595_);
lean_ctor_set(v___x_1587_, 0, v___x_1594_);
v___x_1597_ = v___x_1587_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v_msg_1599_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 7);
lean_ctor_set(v___x_1569_, 1, v_msg_1559_);
lean_ctor_set(v___x_1569_, 0, v___x_1597_);
v_msg_1599_ = v___x_1569_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_msg_1559_);
v_msg_1599_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; double v___x_1602_; lean_object* v_data_1603_; 
v___x_1600_ = lean_box(v_result_1592_);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1554_);
lean_inc_ref(v___x_1601_);
lean_inc(v_cls_1552_);
v_data_1603_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1603_, 0, v_cls_1552_);
lean_ctor_set(v_data_1603_, 1, v___x_1601_);
lean_ctor_set(v_data_1603_, 2, v_tag_1554_);
lean_ctor_set_float(v_data_1603_, sizeof(void*)*3, v___x_1602_);
lean_ctor_set_float(v_data_1603_, sizeof(void*)*3 + 8, v___x_1602_);
lean_ctor_set_uint8(v_data_1603_, sizeof(void*)*3 + 16, v_collapsed_1553_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v___x_1601_);
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_dec_ref(v_tag_1554_);
lean_dec(v_cls_1552_);
v___y_1572_ = v_msg_1599_;
v_data_1573_ = v_data_1603_;
goto v___jp_1571_;
}
else
{
lean_object* v_data_1604_; double v___x_1605_; double v___x_1606_; 
lean_dec_ref(v_data_1603_);
v_data_1604_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1604_, 0, v_cls_1552_);
lean_ctor_set(v_data_1604_, 1, v___x_1601_);
lean_ctor_set(v_data_1604_, 2, v_tag_1554_);
v___x_1605_ = lean_unbox_float(v_fst_1584_);
lean_dec(v_fst_1584_);
lean_ctor_set_float(v_data_1604_, sizeof(void*)*3, v___x_1605_);
v___x_1606_ = lean_unbox_float(v_snd_1585_);
lean_dec(v_snd_1585_);
lean_ctor_set_float(v_data_1604_, sizeof(void*)*3 + 8, v___x_1606_);
lean_ctor_set_uint8(v_data_1604_, sizeof(void*)*3 + 16, v_collapsed_1553_);
v___y_1572_ = v_msg_1599_;
v_data_1573_ = v_data_1604_;
goto v___jp_1571_;
}
}
}
}
v___jp_1609_:
{
if (v_clsEnabled_1556_ == 0)
{
if (v___y_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v_traceState_1612_; lean_object* v_env_1613_; lean_object* v_nextMacroScope_1614_; lean_object* v_ngen_1615_; lean_object* v_auxDeclNGen_1616_; lean_object* v_cache_1617_; lean_object* v_messages_1618_; lean_object* v_infoState_1619_; lean_object* v_snapshotTasks_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1639_; 
lean_del_object(v___x_1587_);
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_del_object(v___x_1569_);
lean_dec_ref(v_msg_1559_);
lean_dec(v_ref_1558_);
lean_dec_ref(v_tag_1554_);
lean_dec(v_cls_1552_);
v___x_1611_ = lean_st_ref_take(v___y_1564_);
v_traceState_1612_ = lean_ctor_get(v___x_1611_, 4);
v_env_1613_ = lean_ctor_get(v___x_1611_, 0);
v_nextMacroScope_1614_ = lean_ctor_get(v___x_1611_, 1);
v_ngen_1615_ = lean_ctor_get(v___x_1611_, 2);
v_auxDeclNGen_1616_ = lean_ctor_get(v___x_1611_, 3);
v_cache_1617_ = lean_ctor_get(v___x_1611_, 5);
v_messages_1618_ = lean_ctor_get(v___x_1611_, 6);
v_infoState_1619_ = lean_ctor_get(v___x_1611_, 7);
v_snapshotTasks_1620_ = lean_ctor_get(v___x_1611_, 8);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1639_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_snapshotTasks_1620_);
lean_inc(v_infoState_1619_);
lean_inc(v_messages_1618_);
lean_inc(v_cache_1617_);
lean_inc(v_traceState_1612_);
lean_inc(v_auxDeclNGen_1616_);
lean_inc(v_ngen_1615_);
lean_inc(v_nextMacroScope_1614_);
lean_inc(v_env_1613_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1639_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
uint64_t v_tid_1624_; lean_object* v_traces_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1638_; 
v_tid_1624_ = lean_ctor_get_uint64(v_traceState_1612_, sizeof(void*)*1);
v_traces_1625_ = lean_ctor_get(v_traceState_1612_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_traceState_1612_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1627_ = v_traceState_1612_;
v_isShared_1628_ = v_isSharedCheck_1638_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_traces_1625_);
lean_dec(v_traceState_1612_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1638_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1557_, v_traces_1625_);
lean_dec_ref(v_traces_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1629_);
lean_ctor_set_uint64(v_reuseFailAlloc_1637_, sizeof(void*)*1, v_tid_1624_);
v___x_1631_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v___x_1631_);
v___x_1633_ = v___x_1622_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_env_1613_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_nextMacroScope_1614_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_ngen_1615_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_auxDeclNGen_1616_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1636_, 5, v_cache_1617_);
lean_ctor_set(v_reuseFailAlloc_1636_, 6, v_messages_1618_);
lean_ctor_set(v_reuseFailAlloc_1636_, 7, v_infoState_1619_);
lean_ctor_set(v_reuseFailAlloc_1636_, 8, v_snapshotTasks_1620_);
v___x_1633_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_st_ref_set(v___y_1564_, v___x_1633_);
v___x_1635_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_fst_1566_);
return v___x_1635_;
}
}
}
}
}
else
{
goto v___jp_1591_;
}
}
else
{
goto v___jp_1591_;
}
}
v___jp_1640_:
{
double v___x_1642_; double v___x_1643_; double v___x_1644_; uint8_t v___x_1645_; 
v___x_1642_ = lean_unbox_float(v_snd_1585_);
v___x_1643_ = lean_unbox_float(v_fst_1584_);
v___x_1644_ = lean_float_sub(v___x_1642_, v___x_1643_);
v___x_1645_ = lean_float_decLt(v___y_1641_, v___x_1644_);
v___y_1610_ = v___x_1645_;
goto v___jp_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1658_, lean_object* v_collapsed_1659_, lean_object* v_tag_1660_, lean_object* v_opts_1661_, lean_object* v_clsEnabled_1662_, lean_object* v_oldTraces_1663_, lean_object* v_ref_1664_, lean_object* v_msg_1665_, lean_object* v_resStartStop_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v_collapsed_boxed_1672_; uint8_t v_clsEnabled_boxed_1673_; lean_object* v_res_1674_; 
v_collapsed_boxed_1672_ = lean_unbox(v_collapsed_1659_);
v_clsEnabled_boxed_1673_ = lean_unbox(v_clsEnabled_1662_);
v_res_1674_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1658_, v_collapsed_boxed_1672_, v_tag_1660_, v_opts_1661_, v_clsEnabled_boxed_1673_, v_oldTraces_1663_, v_ref_1664_, v_msg_1665_, v_resStartStop_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec_ref(v_opts_1661_);
return v_res_1674_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1675_; double v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(1000000000u);
v___x_1676_ = lean_float_of_nat(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1692_ = l_Lean_Name_append(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1693_, lean_object* v_x_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v_a_1714_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v_a_1737_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; uint8_t v___y_1756_; uint8_t v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; uint8_t v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v_fileName_1766_; lean_object* v_fileMap_1767_; lean_object* v_currRecDepth_1768_; lean_object* v_ref_1769_; lean_object* v_currNamespace_1770_; lean_object* v_openDecls_1771_; lean_object* v_initHeartbeats_1772_; lean_object* v_maxHeartbeats_1773_; lean_object* v_quotContext_1774_; lean_object* v_currMacroScope_1775_; lean_object* v_cancelTk_x3f_1776_; uint8_t v_suppressElabErrors_1777_; lean_object* v_inheritedTraceOptions_1778_; lean_object* v___y_1779_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; uint8_t v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; uint8_t v___y_1872_; lean_object* v___y_1873_; uint8_t v___y_1874_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; uint8_t v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1919_; uint8_t v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v_lhs_1941_; lean_object* v_rhs_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; 
if (lean_obj_tag(v_x_1693_) == 1)
{
if (lean_obj_tag(v_x_1694_) == 1)
{
lean_object* v_a_1981_; lean_object* v_a_1982_; lean_object* v___x_1983_; 
v_a_1981_ = lean_ctor_get(v_x_1693_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v_x_1693_);
v_a_1982_ = lean_ctor_get(v_x_1694_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v_x_1694_);
v___x_1983_ = lean_is_level_def_eq(v_a_1981_, v_a_1982_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
return v___x_1983_;
}
else
{
v_lhs_1941_ = v_x_1693_;
v_rhs_1942_ = v_x_1694_;
v___y_1943_ = v_a_1695_;
v___y_1944_ = v_a_1696_;
v___y_1945_ = v_a_1697_;
v___y_1946_ = v_a_1698_;
goto v___jp_1940_;
}
}
else
{
v_lhs_1941_ = v_x_1693_;
v_rhs_1942_ = v_x_1694_;
v___y_1943_ = v_a_1695_;
v___y_1944_ = v_a_1696_;
v___y_1945_ = v_a_1697_;
v___y_1946_ = v_a_1698_;
goto v___jp_1940_;
}
v___jp_1700_:
{
lean_object* v___x_1715_; double v___x_1716_; double v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1715_ = lean_io_get_num_heartbeats();
v___x_1716_ = lean_float_of_nat(v___y_1710_);
v___x_1717_ = lean_float_of_nat(v___x_1715_);
v___x_1718_ = lean_box_float(v___x_1716_);
v___x_1719_ = lean_box_float(v___x_1717_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1714_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1713_);
v___x_1722_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1713_, v___y_1708_, v___y_1711_, v___y_1702_, v___y_1709_, v___y_1712_, v___y_1707_, v___y_1701_, v___x_1721_, v___y_1703_, v___y_1704_, v___y_1706_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v___x_1722_;
}
v___jp_1723_:
{
lean_object* v___x_1738_; double v___x_1739_; double v___x_1740_; double v___x_1741_; double v___x_1742_; double v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1738_ = lean_io_mono_nanos_now();
v___x_1739_ = lean_float_of_nat(v___y_1733_);
v___x_1740_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1741_ = lean_float_div(v___x_1739_, v___x_1740_);
v___x_1742_ = lean_float_of_nat(v___x_1738_);
v___x_1743_ = lean_float_div(v___x_1742_, v___x_1740_);
v___x_1744_ = lean_box_float(v___x_1741_);
v___x_1745_ = lean_box_float(v___x_1743_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_a_1737_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
lean_inc_ref(v___y_1734_);
lean_inc(v___y_1736_);
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1736_, v___y_1731_, v___y_1734_, v___y_1725_, v___y_1732_, v___y_1735_, v___y_1730_, v___y_1724_, v___x_1747_, v___y_1726_, v___y_1727_, v___y_1729_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v___x_1748_;
}
v___jp_1749_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v_a_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1780_ = l_Lean_maxRecDepth;
v___x_1781_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1765_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1782_, 0, v_fileName_1766_);
lean_ctor_set(v___x_1782_, 1, v_fileMap_1767_);
lean_ctor_set(v___x_1782_, 2, v___y_1765_);
lean_ctor_set(v___x_1782_, 3, v_currRecDepth_1768_);
lean_ctor_set(v___x_1782_, 4, v___x_1781_);
lean_ctor_set(v___x_1782_, 5, v_ref_1769_);
lean_ctor_set(v___x_1782_, 6, v_currNamespace_1770_);
lean_ctor_set(v___x_1782_, 7, v_openDecls_1771_);
lean_ctor_set(v___x_1782_, 8, v_initHeartbeats_1772_);
lean_ctor_set(v___x_1782_, 9, v_maxHeartbeats_1773_);
lean_ctor_set(v___x_1782_, 10, v_quotContext_1774_);
lean_ctor_set(v___x_1782_, 11, v_currMacroScope_1775_);
lean_ctor_set(v___x_1782_, 12, v_cancelTk_x3f_1776_);
lean_ctor_set(v___x_1782_, 13, v_inheritedTraceOptions_1778_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*14, v___y_1763_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*14 + 1, v_suppressElabErrors_1777_);
v___x_1783_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1764_, v___y_1751_, v___y_1752_, v___x_1782_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___x_1782_);
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1784_, v___y_1751_, v___y_1752_, v___y_1758_, v___y_1753_);
lean_dec_ref(v___y_1758_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1788_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1750_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_io_mono_nanos_now();
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
v___x_1790_ = lean_apply_5(v___y_1761_, v___y_1751_, v___y_1752_, v___y_1754_, v___y_1753_, lean_box(0));
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 1);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
v___y_1724_ = v_a_1786_;
v___y_1725_ = v___y_1750_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___y_1753_;
v___y_1729_ = v___y_1754_;
v___y_1730_ = v___y_1755_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1757_;
v___y_1733_ = v___x_1789_;
v___y_1734_ = v___y_1759_;
v___y_1735_ = v___y_1760_;
v___y_1736_ = v___y_1762_;
v_a_1737_ = v___x_1796_;
goto v___jp_1723_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1790_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 0);
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
v___y_1724_ = v_a_1786_;
v___y_1725_ = v___y_1750_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___y_1753_;
v___y_1729_ = v___y_1754_;
v___y_1730_ = v___y_1755_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1757_;
v___y_1733_ = v___x_1789_;
v___y_1734_ = v___y_1759_;
v___y_1735_ = v___y_1760_;
v___y_1736_ = v___y_1762_;
v_a_1737_ = v___x_1804_;
goto v___jp_1723_;
}
}
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
v___x_1808_ = lean_apply_5(v___y_1761_, v___y_1751_, v___y_1752_, v___y_1754_, v___y_1753_, lean_box(0));
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
v___y_1701_ = v_a_1786_;
v___y_1702_ = v___y_1750_;
v___y_1703_ = v___y_1751_;
v___y_1704_ = v___y_1752_;
v___y_1705_ = v___y_1753_;
v___y_1706_ = v___y_1754_;
v___y_1707_ = v___y_1755_;
v___y_1708_ = v___y_1756_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___x_1807_;
v___y_1711_ = v___y_1759_;
v___y_1712_ = v___y_1760_;
v___y_1713_ = v___y_1762_;
v_a_1714_ = v___x_1814_;
goto v___jp_1700_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1808_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1808_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 0);
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
v___y_1701_ = v_a_1786_;
v___y_1702_ = v___y_1750_;
v___y_1703_ = v___y_1751_;
v___y_1704_ = v___y_1752_;
v___y_1705_ = v___y_1753_;
v___y_1706_ = v___y_1754_;
v___y_1707_ = v___y_1755_;
v___y_1708_ = v___y_1756_;
v___y_1709_ = v___y_1757_;
v___y_1710_ = v___x_1807_;
v___y_1711_ = v___y_1759_;
v___y_1712_ = v___y_1760_;
v___y_1713_ = v___y_1762_;
v_a_1714_ = v___x_1822_;
goto v___jp_1700_;
}
}
}
}
}
v___jp_1825_:
{
lean_object* v_fileName_1844_; lean_object* v_fileMap_1845_; lean_object* v_currRecDepth_1846_; lean_object* v_ref_1847_; lean_object* v_currNamespace_1848_; lean_object* v_openDecls_1849_; lean_object* v_initHeartbeats_1850_; lean_object* v_maxHeartbeats_1851_; lean_object* v_quotContext_1852_; lean_object* v_currMacroScope_1853_; lean_object* v_cancelTk_x3f_1854_; uint8_t v_suppressElabErrors_1855_; lean_object* v_inheritedTraceOptions_1856_; 
v_fileName_1844_ = lean_ctor_get(v___y_1842_, 0);
lean_inc_ref(v_fileName_1844_);
v_fileMap_1845_ = lean_ctor_get(v___y_1842_, 1);
lean_inc_ref(v_fileMap_1845_);
v_currRecDepth_1846_ = lean_ctor_get(v___y_1842_, 3);
lean_inc(v_currRecDepth_1846_);
v_ref_1847_ = lean_ctor_get(v___y_1842_, 5);
lean_inc(v_ref_1847_);
v_currNamespace_1848_ = lean_ctor_get(v___y_1842_, 6);
lean_inc(v_currNamespace_1848_);
v_openDecls_1849_ = lean_ctor_get(v___y_1842_, 7);
lean_inc(v_openDecls_1849_);
v_initHeartbeats_1850_ = lean_ctor_get(v___y_1842_, 8);
lean_inc(v_initHeartbeats_1850_);
v_maxHeartbeats_1851_ = lean_ctor_get(v___y_1842_, 9);
lean_inc(v_maxHeartbeats_1851_);
v_quotContext_1852_ = lean_ctor_get(v___y_1842_, 10);
lean_inc(v_quotContext_1852_);
v_currMacroScope_1853_ = lean_ctor_get(v___y_1842_, 11);
lean_inc(v_currMacroScope_1853_);
v_cancelTk_x3f_1854_ = lean_ctor_get(v___y_1842_, 12);
lean_inc(v_cancelTk_x3f_1854_);
v_suppressElabErrors_1855_ = lean_ctor_get_uint8(v___y_1842_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1856_ = lean_ctor_get(v___y_1842_, 13);
lean_inc_ref(v_inheritedTraceOptions_1856_);
lean_dec_ref(v___y_1842_);
v___y_1750_ = v___y_1826_;
v___y_1751_ = v___y_1827_;
v___y_1752_ = v___y_1828_;
v___y_1753_ = v___y_1829_;
v___y_1754_ = v___y_1830_;
v___y_1755_ = v___y_1831_;
v___y_1756_ = v___y_1832_;
v___y_1757_ = v___y_1833_;
v___y_1758_ = v___y_1834_;
v___y_1759_ = v___y_1835_;
v___y_1760_ = v___y_1836_;
v___y_1761_ = v___y_1837_;
v___y_1762_ = v___y_1838_;
v___y_1763_ = v___y_1839_;
v___y_1764_ = v___y_1840_;
v___y_1765_ = v___y_1841_;
v_fileName_1766_ = v_fileName_1844_;
v_fileMap_1767_ = v_fileMap_1845_;
v_currRecDepth_1768_ = v_currRecDepth_1846_;
v_ref_1769_ = v_ref_1847_;
v_currNamespace_1770_ = v_currNamespace_1848_;
v_openDecls_1771_ = v_openDecls_1849_;
v_initHeartbeats_1772_ = v_initHeartbeats_1850_;
v_maxHeartbeats_1773_ = v_maxHeartbeats_1851_;
v_quotContext_1774_ = v_quotContext_1852_;
v_currMacroScope_1775_ = v_currMacroScope_1853_;
v_cancelTk_x3f_1776_ = v_cancelTk_x3f_1854_;
v_suppressElabErrors_1777_ = v_suppressElabErrors_1855_;
v_inheritedTraceOptions_1778_ = v_inheritedTraceOptions_1856_;
v___y_1779_ = v___y_1843_;
goto v___jp_1749_;
}
v___jp_1857_:
{
if (v___y_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v_env_1876_; lean_object* v_nextMacroScope_1877_; lean_object* v_ngen_1878_; lean_object* v_auxDeclNGen_1879_; lean_object* v_traceState_1880_; lean_object* v_messages_1881_; lean_object* v_infoState_1882_; lean_object* v_snapshotTasks_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1893_; 
v___x_1875_ = lean_st_ref_take(v___y_1861_);
v_env_1876_ = lean_ctor_get(v___x_1875_, 0);
v_nextMacroScope_1877_ = lean_ctor_get(v___x_1875_, 1);
v_ngen_1878_ = lean_ctor_get(v___x_1875_, 2);
v_auxDeclNGen_1879_ = lean_ctor_get(v___x_1875_, 3);
v_traceState_1880_ = lean_ctor_get(v___x_1875_, 4);
v_messages_1881_ = lean_ctor_get(v___x_1875_, 6);
v_infoState_1882_ = lean_ctor_get(v___x_1875_, 7);
v_snapshotTasks_1883_ = lean_ctor_get(v___x_1875_, 8);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1875_, 5);
lean_dec(v_unused_1894_);
v___x_1885_ = v___x_1875_;
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snapshotTasks_1883_);
lean_inc(v_infoState_1882_);
lean_inc(v_messages_1881_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1879_);
lean_inc(v_ngen_1878_);
lean_inc(v_nextMacroScope_1877_);
lean_inc(v_env_1876_);
lean_dec(v___x_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_Kernel_enableDiag(v_env_1876_, v___y_1872_);
v___x_1888_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 5, v___x_1888_);
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_nextMacroScope_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_ngen_1878_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_auxDeclNGen_1879_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_traceState_1880_);
lean_ctor_set(v_reuseFailAlloc_1892_, 5, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1892_, 6, v_messages_1881_);
lean_ctor_set(v_reuseFailAlloc_1892_, 7, v_infoState_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 8, v_snapshotTasks_1883_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_st_ref_set(v___y_1861_, v___x_1890_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1861_);
v___y_1826_ = v___y_1858_;
v___y_1827_ = v___y_1859_;
v___y_1828_ = v___y_1860_;
v___y_1829_ = v___y_1861_;
v___y_1830_ = v___y_1862_;
v___y_1831_ = v___y_1863_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1865_;
v___y_1834_ = v___y_1866_;
v___y_1835_ = v___y_1867_;
v___y_1836_ = v___y_1868_;
v___y_1837_ = v___y_1870_;
v___y_1838_ = v___y_1869_;
v___y_1839_ = v___y_1872_;
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1873_;
v___y_1842_ = v___y_1866_;
v___y_1843_ = v___y_1861_;
goto v___jp_1825_;
}
}
}
else
{
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1861_);
v___y_1826_ = v___y_1858_;
v___y_1827_ = v___y_1859_;
v___y_1828_ = v___y_1860_;
v___y_1829_ = v___y_1861_;
v___y_1830_ = v___y_1862_;
v___y_1831_ = v___y_1863_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1865_;
v___y_1834_ = v___y_1866_;
v___y_1835_ = v___y_1867_;
v___y_1836_ = v___y_1868_;
v___y_1837_ = v___y_1870_;
v___y_1838_ = v___y_1869_;
v___y_1839_ = v___y_1872_;
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1873_;
v___y_1842_ = v___y_1866_;
v___y_1843_ = v___y_1861_;
goto v___jp_1825_;
}
}
v___jp_1895_:
{
lean_object* v___x_1923_; lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v_env_1926_; lean_object* v_ref_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1923_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1900_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = lean_st_ref_get(v___y_1900_);
v_env_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc_ref(v_env_1926_);
lean_dec(v___x_1925_);
v_ref_1927_ = l_Lean_replaceRef(v___y_1915_, v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1904_);
lean_inc(v___y_1918_);
lean_inc(v___y_1917_);
lean_inc(v___y_1909_);
lean_inc(v___y_1899_);
lean_inc(v___y_1897_);
lean_inc(v___y_1908_);
lean_inc(v_ref_1927_);
lean_inc(v___y_1907_);
lean_inc_ref_n(v___y_1896_, 2);
lean_inc_ref(v___y_1912_);
lean_inc_ref(v___y_1903_);
v___x_1928_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1928_, 0, v___y_1903_);
lean_ctor_set(v___x_1928_, 1, v___y_1912_);
lean_ctor_set(v___x_1928_, 2, v___y_1896_);
lean_ctor_set(v___x_1928_, 3, v___y_1907_);
lean_ctor_set(v___x_1928_, 4, v___y_1911_);
lean_ctor_set(v___x_1928_, 5, v_ref_1927_);
lean_ctor_set(v___x_1928_, 6, v___y_1908_);
lean_ctor_set(v___x_1928_, 7, v___y_1897_);
lean_ctor_set(v___x_1928_, 8, v___y_1899_);
lean_ctor_set(v___x_1928_, 9, v___y_1909_);
lean_ctor_set(v___x_1928_, 10, v___y_1917_);
lean_ctor_set(v___x_1928_, 11, v___y_1918_);
lean_ctor_set(v___x_1928_, 12, v___y_1904_);
lean_ctor_set(v___x_1928_, 13, v___y_1914_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*14, v___y_1901_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*14 + 1, v___y_1916_);
v___x_1929_ = l_Lean_MessageData_ofLevel(v___y_1902_);
v___x_1930_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_MessageData_ofLevel(v___y_1906_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1935_ = 0;
v___x_1936_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1896_, v___x_1934_, v___x_1935_);
v___x_1937_ = l_Lean_diagnostics;
v___x_1938_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___x_1936_, v___x_1937_);
v___x_1939_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1926_);
lean_dec_ref(v_env_1926_);
if (v___x_1939_ == 0)
{
if (v___x_1938_ == 0)
{
lean_inc(v___y_1900_);
v___y_1750_ = v___y_1896_;
v___y_1751_ = v___y_1910_;
v___y_1752_ = v___y_1898_;
v___y_1753_ = v___y_1900_;
v___y_1754_ = v___y_1913_;
v___y_1755_ = v___y_1915_;
v___y_1756_ = v___y_1919_;
v___y_1757_ = v___y_1920_;
v___y_1758_ = v___x_1928_;
v___y_1759_ = v___y_1921_;
v___y_1760_ = v_a_1924_;
v___y_1761_ = v___y_1905_;
v___y_1762_ = v___y_1922_;
v___y_1763_ = v___x_1938_;
v___y_1764_ = v___x_1933_;
v___y_1765_ = v___x_1936_;
v_fileName_1766_ = v___y_1903_;
v_fileMap_1767_ = v___y_1912_;
v_currRecDepth_1768_ = v___y_1907_;
v_ref_1769_ = v_ref_1927_;
v_currNamespace_1770_ = v___y_1908_;
v_openDecls_1771_ = v___y_1897_;
v_initHeartbeats_1772_ = v___y_1899_;
v_maxHeartbeats_1773_ = v___y_1909_;
v_quotContext_1774_ = v___y_1917_;
v_currMacroScope_1775_ = v___y_1918_;
v_cancelTk_x3f_1776_ = v___y_1904_;
v_suppressElabErrors_1777_ = v___y_1916_;
v_inheritedTraceOptions_1778_ = v___y_1914_;
v___y_1779_ = v___y_1900_;
goto v___jp_1749_;
}
else
{
lean_dec(v_ref_1927_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1899_);
lean_dec(v___y_1897_);
v___y_1858_ = v___y_1896_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1898_;
v___y_1861_ = v___y_1900_;
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1915_;
v___y_1864_ = v___y_1919_;
v___y_1865_ = v___y_1920_;
v___y_1866_ = v___x_1928_;
v___y_1867_ = v___y_1921_;
v___y_1868_ = v_a_1924_;
v___y_1869_ = v___y_1922_;
v___y_1870_ = v___y_1905_;
v___y_1871_ = v___x_1933_;
v___y_1872_ = v___x_1938_;
v___y_1873_ = v___x_1936_;
v___y_1874_ = v___x_1939_;
goto v___jp_1857_;
}
}
else
{
lean_dec(v_ref_1927_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1899_);
lean_dec(v___y_1897_);
v___y_1858_ = v___y_1896_;
v___y_1859_ = v___y_1910_;
v___y_1860_ = v___y_1898_;
v___y_1861_ = v___y_1900_;
v___y_1862_ = v___y_1913_;
v___y_1863_ = v___y_1915_;
v___y_1864_ = v___y_1919_;
v___y_1865_ = v___y_1920_;
v___y_1866_ = v___x_1928_;
v___y_1867_ = v___y_1921_;
v___y_1868_ = v_a_1924_;
v___y_1869_ = v___y_1922_;
v___y_1870_ = v___y_1905_;
v___y_1871_ = v___x_1933_;
v___y_1872_ = v___x_1938_;
v___y_1873_ = v___x_1936_;
v___y_1874_ = v___x_1938_;
goto v___jp_1857_;
}
}
v___jp_1940_:
{
lean_object* v_options_1947_; lean_object* v_fileName_1948_; lean_object* v_fileMap_1949_; lean_object* v_currRecDepth_1950_; lean_object* v_maxRecDepth_1951_; lean_object* v_ref_1952_; lean_object* v_currNamespace_1953_; lean_object* v_openDecls_1954_; lean_object* v_initHeartbeats_1955_; lean_object* v_maxHeartbeats_1956_; lean_object* v_quotContext_1957_; lean_object* v_currMacroScope_1958_; uint8_t v_diag_1959_; lean_object* v_cancelTk_x3f_1960_; uint8_t v_suppressElabErrors_1961_; lean_object* v_inheritedTraceOptions_1962_; uint8_t v_hasTrace_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___y_1972_; 
v_options_1947_ = lean_ctor_get(v___y_1945_, 2);
v_fileName_1948_ = lean_ctor_get(v___y_1945_, 0);
v_fileMap_1949_ = lean_ctor_get(v___y_1945_, 1);
v_currRecDepth_1950_ = lean_ctor_get(v___y_1945_, 3);
v_maxRecDepth_1951_ = lean_ctor_get(v___y_1945_, 4);
v_ref_1952_ = lean_ctor_get(v___y_1945_, 5);
v_currNamespace_1953_ = lean_ctor_get(v___y_1945_, 6);
v_openDecls_1954_ = lean_ctor_get(v___y_1945_, 7);
v_initHeartbeats_1955_ = lean_ctor_get(v___y_1945_, 8);
v_maxHeartbeats_1956_ = lean_ctor_get(v___y_1945_, 9);
v_quotContext_1957_ = lean_ctor_get(v___y_1945_, 10);
v_currMacroScope_1958_ = lean_ctor_get(v___y_1945_, 11);
v_diag_1959_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*14);
v_cancelTk_x3f_1960_ = lean_ctor_get(v___y_1945_, 12);
v_suppressElabErrors_1961_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1962_ = lean_ctor_get(v___y_1945_, 13);
v_hasTrace_1963_ = lean_ctor_get_uint8(v_options_1947_, sizeof(void*)*1);
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1966_ = l_Lean_Level_getLevelOffset(v_lhs_1941_);
v___x_1967_ = l_Lean_Level_getLevelOffset(v_rhs_1942_);
v___x_1968_ = lean_level_eq(v___x_1966_, v___x_1967_);
lean_dec(v___x_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = 1;
v___x_1970_ = lean_box(v___x_1968_);
v___x_1971_ = lean_box(v___x_1969_);
lean_inc(v_rhs_1942_);
lean_inc(v_lhs_1941_);
v___y_1972_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1972_, 0, v___x_1970_);
lean_closure_set(v___y_1972_, 1, v_lhs_1941_);
lean_closure_set(v___y_1972_, 2, v_rhs_1942_);
lean_closure_set(v___y_1972_, 3, v___x_1964_);
lean_closure_set(v___y_1972_, 4, v___x_1965_);
lean_closure_set(v___y_1972_, 5, v___x_1971_);
if (v_hasTrace_1963_ == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref(v___y_1972_);
v___x_1973_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1968_, v_lhs_1941_, v_rhs_1942_, v___x_1964_, v___x_1965_, v___x_1969_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1974_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1975_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1976_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1962_, v_options_1947_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = l_Lean_trace_profiler;
v___x_1979_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_options_1947_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec_ref(v___y_1972_);
v___x_1980_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1968_, v_lhs_1941_, v_rhs_1942_, v___x_1964_, v___x_1965_, v___x_1969_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v___x_1980_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1962_);
lean_inc(v_cancelTk_x3f_1960_);
lean_inc(v_currMacroScope_1958_);
lean_inc(v_quotContext_1957_);
lean_inc(v_maxHeartbeats_1956_);
lean_inc(v_initHeartbeats_1955_);
lean_inc(v_openDecls_1954_);
lean_inc(v_currNamespace_1953_);
lean_inc(v_ref_1952_);
lean_inc(v_maxRecDepth_1951_);
lean_inc(v_currRecDepth_1950_);
lean_inc_ref(v_fileMap_1949_);
lean_inc_ref(v_fileName_1948_);
lean_inc_ref(v_options_1947_);
v___y_1896_ = v_options_1947_;
v___y_1897_ = v_openDecls_1954_;
v___y_1898_ = v___y_1944_;
v___y_1899_ = v_initHeartbeats_1955_;
v___y_1900_ = v___y_1946_;
v___y_1901_ = v_diag_1959_;
v___y_1902_ = v_lhs_1941_;
v___y_1903_ = v_fileName_1948_;
v___y_1904_ = v_cancelTk_x3f_1960_;
v___y_1905_ = v___y_1972_;
v___y_1906_ = v_rhs_1942_;
v___y_1907_ = v_currRecDepth_1950_;
v___y_1908_ = v_currNamespace_1953_;
v___y_1909_ = v_maxHeartbeats_1956_;
v___y_1910_ = v___y_1943_;
v___y_1911_ = v_maxRecDepth_1951_;
v___y_1912_ = v_fileMap_1949_;
v___y_1913_ = v___y_1945_;
v___y_1914_ = v_inheritedTraceOptions_1962_;
v___y_1915_ = v_ref_1952_;
v___y_1916_ = v_suppressElabErrors_1961_;
v___y_1917_ = v_quotContext_1957_;
v___y_1918_ = v_currMacroScope_1958_;
v___y_1919_ = v___x_1969_;
v___y_1920_ = v___x_1977_;
v___y_1921_ = v___x_1975_;
v___y_1922_ = v___x_1974_;
goto v___jp_1895_;
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1962_);
lean_inc(v_cancelTk_x3f_1960_);
lean_inc(v_currMacroScope_1958_);
lean_inc(v_quotContext_1957_);
lean_inc(v_maxHeartbeats_1956_);
lean_inc(v_initHeartbeats_1955_);
lean_inc(v_openDecls_1954_);
lean_inc(v_currNamespace_1953_);
lean_inc(v_ref_1952_);
lean_inc(v_maxRecDepth_1951_);
lean_inc(v_currRecDepth_1950_);
lean_inc_ref(v_fileMap_1949_);
lean_inc_ref(v_fileName_1948_);
lean_inc_ref(v_options_1947_);
v___y_1896_ = v_options_1947_;
v___y_1897_ = v_openDecls_1954_;
v___y_1898_ = v___y_1944_;
v___y_1899_ = v_initHeartbeats_1955_;
v___y_1900_ = v___y_1946_;
v___y_1901_ = v_diag_1959_;
v___y_1902_ = v_lhs_1941_;
v___y_1903_ = v_fileName_1948_;
v___y_1904_ = v_cancelTk_x3f_1960_;
v___y_1905_ = v___y_1972_;
v___y_1906_ = v_rhs_1942_;
v___y_1907_ = v_currRecDepth_1950_;
v___y_1908_ = v_currNamespace_1953_;
v___y_1909_ = v_maxHeartbeats_1956_;
v___y_1910_ = v___y_1943_;
v___y_1911_ = v_maxRecDepth_1951_;
v___y_1912_ = v_fileMap_1949_;
v___y_1913_ = v___y_1945_;
v___y_1914_ = v_inheritedTraceOptions_1962_;
v___y_1915_ = v_ref_1952_;
v___y_1916_ = v_suppressElabErrors_1961_;
v___y_1917_ = v_quotContext_1957_;
v___y_1918_ = v_currMacroScope_1958_;
v___y_1919_ = v___x_1969_;
v___y_1920_ = v___x_1977_;
v___y_1921_ = v___x_1975_;
v___y_1922_ = v___x_1974_;
goto v___jp_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = lean_is_level_def_eq(v_x_1984_, v_x_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_00_u03b1_1992_, lean_object* v_x_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_x_1993_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_00_u03b1_2000_, v_x_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2064_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2065_ = 0;
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2067_ = l_Lean_registerTraceClass(v___x_2064_, v___x_2065_, v___x_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v___x_2067_);
v___x_2068_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2069_ = 1;
v___x_2070_ = l_Lean_registerTraceClass(v___x_2068_, v___x_2069_, v___x_2066_);
return v___x_2070_;
}
else
{
return v___x_2067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2072_;
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
