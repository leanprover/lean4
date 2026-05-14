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
lean_object* v___f_47_; lean_object* v___x_1321__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_1321__overap_48_ = lean_panic_fn_borrowed(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_1321__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
size_t v_x_3055__boxed_204_; size_t v_x_3056__boxed_205_; lean_object* v_res_206_; 
v_x_3055__boxed_204_ = lean_unbox_usize(v_x_200_);
lean_dec(v_x_200_);
v_x_3056__boxed_205_ = lean_unbox_usize(v_x_201_);
lean_dec(v_x_201_);
v_res_206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_199_, v_x_3055__boxed_204_, v_x_3056__boxed_205_, v_x_202_, v_x_203_);
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
lean_object* v_ref_291_; lean_object* v___x_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_338_; 
v_ref_291_ = lean_ctor_get(v___y_288_, 5);
v___x_292_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_338_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_338_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_338_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v_traceState_298_; lean_object* v_env_299_; lean_object* v_nextMacroScope_300_; lean_object* v_ngen_301_; lean_object* v_auxDeclNGen_302_; lean_object* v_cache_303_; lean_object* v_messages_304_; lean_object* v_infoState_305_; lean_object* v_snapshotTasks_306_; lean_object* v_newDecls_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_337_; 
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
v_newDecls_307_ = lean_ctor_get(v___x_297_, 9);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_337_ == 0)
{
v___x_309_ = v___x_297_;
v_isShared_310_ = v_isSharedCheck_337_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_newDecls_307_);
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
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_337_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint64_t v_tid_311_; lean_object* v_traces_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_336_; 
v_tid_311_ = lean_ctor_get_uint64(v_traceState_298_, sizeof(void*)*1);
v_traces_312_ = lean_ctor_get(v_traceState_298_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_traceState_298_);
if (v_isSharedCheck_336_ == 0)
{
v___x_314_ = v_traceState_298_;
v_isShared_315_ = v_isSharedCheck_336_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_traces_312_);
lean_dec(v_traceState_298_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_336_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; double v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_316_ = lean_box(0);
v___x_317_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_318_ = 0;
v___x_319_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_320_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_320_, 0, v_cls_284_);
lean_ctor_set(v___x_320_, 1, v___x_316_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
lean_ctor_set_float(v___x_320_, sizeof(void*)*3, v___x_317_);
lean_ctor_set_float(v___x_320_, sizeof(void*)*3 + 8, v___x_317_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*3 + 16, v___x_318_);
v___x_321_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_322_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v_a_293_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
lean_inc(v_ref_291_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_ref_291_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_PersistentArray_push___redArg(v_traces_312_, v___x_323_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_324_);
v___x_326_ = v___x_314_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_324_);
lean_ctor_set_uint64(v_reuseFailAlloc_335_, sizeof(void*)*1, v_tid_311_);
v___x_326_ = v_reuseFailAlloc_335_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 4, v___x_326_);
v___x_328_ = v___x_309_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_env_299_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_nextMacroScope_300_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_ngen_301_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_auxDeclNGen_302_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v_cache_303_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_messages_304_);
lean_ctor_set(v_reuseFailAlloc_334_, 7, v_infoState_305_);
lean_ctor_set(v_reuseFailAlloc_334_, 8, v_snapshotTasks_306_);
lean_ctor_set(v_reuseFailAlloc_334_, 9, v_newDecls_307_);
v___x_328_ = v_reuseFailAlloc_334_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_st_ref_set(v___y_289_, v___x_328_);
v___x_330_ = lean_box(0);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_330_);
v___x_332_ = v___x_295_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_339_, v_msg_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_351_ = lean_unsigned_to_nat(2u);
v___x_352_ = lean_unsigned_to_nat(39u);
v___x_353_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_355_ = l_mkPanicMessageWithDecl(v___x_354_, v___x_353_, v___x_352_, v___x_351_, v___x_350_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_368_ = l_Lean_Name_append(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_375_, lean_object* v_v_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Level_isMax(v_v_376_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_v_376_);
lean_dec(v_mvarId_375_);
v___x_383_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_384_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_383_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_mkFreshLevelMVar(v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_options_386_; lean_object* v_a_387_; lean_object* v_inheritedTraceOptions_388_; uint8_t v_hasTrace_389_; lean_object* v___x_390_; 
v_options_386_ = lean_ctor_get(v_a_379_, 2);
v_a_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_385_);
v_inheritedTraceOptions_388_ = lean_ctor_get(v_a_379_, 13);
v_hasTrace_389_ = lean_ctor_get_uint8(v_options_386_, sizeof(void*)*1);
v___x_390_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_375_, v_v_376_, v_a_387_);
if (v_hasTrace_389_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_375_, v___x_390_, v_a_378_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_393_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_394_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_388_, v_options_386_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_375_, v___x_390_, v_a_378_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_396_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_375_);
v___x_397_ = l_Lean_mkLevelMVar(v_mvarId_375_);
v___x_398_ = l_Lean_MessageData_ofLevel(v___x_397_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_396_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
lean_inc(v___x_390_);
v___x_402_ = l_Lean_MessageData_ofLevel(v___x_390_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_392_, v___x_403_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_404_);
v___x_405_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_375_, v___x_390_, v_a_378_);
return v___x_405_;
}
else
{
lean_dec(v___x_390_);
lean_dec(v_mvarId_375_);
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_v_376_);
lean_dec(v_mvarId_375_);
v_a_406_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_385_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_385_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_414_, lean_object* v_v_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_414_, v_v_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_422_, lean_object* v_val_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_422_, v_val_423_, v___y_425_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_430_, lean_object* v_val_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_430_, v_val_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_439_, v_x_440_, v_x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, size_t v_x_445_, size_t v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_444_, v_x_445_, v_x_446_, v_x_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
size_t v_x_3573__boxed_456_; size_t v_x_3574__boxed_457_; lean_object* v_res_458_; 
v_x_3573__boxed_456_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_x_3574__boxed_457_ = lean_unbox_usize(v_x_453_);
lean_dec(v_x_453_);
v_res_458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_450_, v_x_451_, v_x_3573__boxed_456_, v_x_3574__boxed_457_, v_x_454_, v_x_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_459_, lean_object* v_n_460_, lean_object* v_k_461_, lean_object* v_v_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_460_, v_k_461_, v_v_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_464_, size_t v_depth_465_, lean_object* v_keys_466_, lean_object* v_vals_467_, lean_object* v_heq_468_, lean_object* v_i_469_, lean_object* v_entries_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_465_, v_keys_466_, v_vals_467_, v_i_469_, v_entries_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_472_, lean_object* v_depth_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_entries_478_){
_start:
{
size_t v_depth_boxed_479_; lean_object* v_res_480_; 
v_depth_boxed_479_ = lean_unbox_usize(v_depth_473_);
lean_dec(v_depth_473_);
v_res_480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_472_, v_depth_boxed_479_, v_keys_474_, v_vals_475_, v_heq_476_, v_i_477_, v_entries_478_);
lean_dec_ref(v_vals_475_);
lean_dec_ref(v_keys_474_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_482_, v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_490_, lean_object* v_v_x27_491_, lean_object* v_mvarId_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
uint8_t v___x_498_; lean_object* v___y_500_; 
v___x_498_ = lean_level_eq(v_u_490_, v_v_x27_491_);
if (v___x_498_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_mvarId_492_);
lean_dec(v_u_490_);
v___x_511_ = lean_box(v___x_498_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_options_513_; uint8_t v_hasTrace_514_; 
v_options_513_ = lean_ctor_get(v_a_495_, 2);
v_hasTrace_514_ = lean_ctor_get_uint8(v_options_513_, sizeof(void*)*1);
if (v_hasTrace_514_ == 0)
{
v___y_500_ = v_a_494_;
goto v___jp_499_;
}
else
{
lean_object* v_inheritedTraceOptions_515_; lean_object* v_cls_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_inheritedTraceOptions_515_ = lean_ctor_get(v_a_495_, 13);
v_cls_516_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_515_, v_options_513_, v___x_517_);
if (v___x_518_ == 0)
{
v___y_500_ = v_a_494_;
goto v___jp_499_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_519_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_492_);
v___x_520_ = l_Lean_mkLevelMVar(v_mvarId_492_);
v___x_521_ = l_Lean_MessageData_ofLevel(v___x_520_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_519_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_inc(v_u_490_);
v___x_525_ = l_Lean_MessageData_ofLevel(v_u_490_);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_516_, v___x_526_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_dec_ref(v___x_527_);
v___y_500_ = v_a_494_;
goto v___jp_499_;
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_mvarId_492_);
lean_dec(v_u_490_);
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v___x_501_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_492_, v_u_490_, v___y_500_);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_510_);
v___x_503_ = v___x_501_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_dec(v___x_501_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_box(v___x_498_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_536_, lean_object* v_v_x27_537_, lean_object* v_mvarId_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_536_, v_v_x27_537_, v_mvarId_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_v_x27_537_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_545_, lean_object* v_v_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
if (lean_obj_tag(v_v_546_) == 2)
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v_v_546_, 1);
lean_inc(v_a_556_);
if (lean_obj_tag(v_a_556_) == 5)
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_557_ = lean_ctor_get(v_v_546_, 0);
lean_inc(v_a_557_);
lean_dec_ref(v_v_546_);
v_a_558_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_a_558_);
lean_dec_ref(v_a_556_);
v___x_559_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_545_, v_a_557_, v_a_558_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_557_);
return v___x_559_;
}
else
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v_v_546_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v_v_546_);
if (lean_obj_tag(v_a_560_) == 5)
{
lean_object* v_a_561_; lean_object* v___x_562_; 
v_a_561_ = lean_ctor_get(v_a_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v_a_560_);
v___x_562_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_545_, v_a_556_, v_a_561_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_556_);
return v___x_562_;
}
else
{
lean_dec(v_a_560_);
lean_dec(v_a_556_);
lean_dec(v_u_545_);
goto v___jp_552_;
}
}
}
else
{
lean_dec(v_v_546_);
lean_dec(v_u_545_);
goto v___jp_552_;
}
v___jp_552_:
{
uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = 0;
v___x_554_ = lean_box(v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_563_, lean_object* v_v_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_563_, v_v_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_574_, lean_object* v_u_u2082_575_, lean_object* v_v_x27_576_, lean_object* v_mvarId_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
uint8_t v___x_583_; uint8_t v___x_584_; lean_object* v___y_586_; lean_object* v___y_598_; 
v___x_583_ = lean_level_eq(v_u_u2081_574_, v_v_x27_576_);
v___x_584_ = 1;
if (v___x_583_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = lean_level_eq(v_u_u2082_575_, v_v_x27_576_);
lean_dec(v_u_u2082_575_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_mvarId_577_);
lean_dec(v_u_u2081_574_);
v___x_610_ = lean_box(v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_options_612_; uint8_t v_hasTrace_613_; 
v_options_612_ = lean_ctor_get(v_a_580_, 2);
v_hasTrace_613_ = lean_ctor_get_uint8(v_options_612_, sizeof(void*)*1);
if (v_hasTrace_613_ == 0)
{
v___y_598_ = v_a_579_;
goto v___jp_597_;
}
else
{
lean_object* v_inheritedTraceOptions_614_; lean_object* v_cls_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_inheritedTraceOptions_614_ = lean_ctor_get(v_a_580_, 13);
v_cls_615_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_614_, v_options_612_, v___x_616_);
if (v___x_617_ == 0)
{
v___y_598_ = v_a_579_;
goto v___jp_597_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_618_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_577_);
v___x_619_ = l_Lean_mkLevelMVar(v_mvarId_577_);
v___x_620_ = l_Lean_MessageData_ofLevel(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
lean_inc(v_u_u2081_574_);
v___x_624_ = l_Lean_MessageData_ofLevel(v_u_u2081_574_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_615_, v___x_625_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref(v___x_626_);
v___y_598_ = v_a_579_;
goto v___jp_597_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_mvarId_577_);
lean_dec(v_u_u2081_574_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_635_; uint8_t v_hasTrace_636_; 
lean_dec(v_u_u2081_574_);
v_options_635_ = lean_ctor_get(v_a_580_, 2);
v_hasTrace_636_ = lean_ctor_get_uint8(v_options_635_, sizeof(void*)*1);
if (v_hasTrace_636_ == 0)
{
v___y_586_ = v_a_579_;
goto v___jp_585_;
}
else
{
lean_object* v_inheritedTraceOptions_637_; lean_object* v_cls_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_inheritedTraceOptions_637_ = lean_ctor_get(v_a_580_, 13);
v_cls_638_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_639_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_637_, v_options_635_, v___x_639_);
if (v___x_640_ == 0)
{
v___y_586_ = v_a_579_;
goto v___jp_585_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_641_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_577_);
v___x_642_ = l_Lean_mkLevelMVar(v_mvarId_577_);
v___x_643_ = l_Lean_MessageData_ofLevel(v___x_642_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_641_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_inc(v_u_u2082_575_);
v___x_647_ = l_Lean_MessageData_ofLevel(v_u_u2082_575_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_638_, v___x_648_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_dec_ref(v___x_649_);
v___y_586_ = v_a_579_;
goto v___jp_585_;
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_mvarId_577_);
lean_dec(v_u_u2082_575_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v___x_587_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_577_, v_u_u2082_575_, v___y_586_);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_587_, 0);
lean_dec(v_unused_596_);
v___x_589_ = v___x_587_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_dec(v___x_587_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_box(v___x_584_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
v___jp_597_:
{
lean_object* v___x_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v___x_599_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_577_, v_u_u2081_574_, v___y_598_);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_599_, 0);
lean_dec(v_unused_608_);
v___x_601_ = v___x_599_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_dec(v___x_599_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_box(v___x_584_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_658_, lean_object* v_u_u2082_659_, lean_object* v_v_x27_660_, lean_object* v_mvarId_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_658_, v_u_u2082_659_, v_v_x27_660_, v_mvarId_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_v_x27_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_668_, lean_object* v_v_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
if (lean_obj_tag(v_u_668_) == 2)
{
if (lean_obj_tag(v_v_669_) == 2)
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v_v_669_, 1);
lean_inc(v_a_679_);
if (lean_obj_tag(v_a_679_) == 5)
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_680_ = lean_ctor_get(v_u_668_, 0);
lean_inc(v_a_680_);
v_a_681_ = lean_ctor_get(v_u_668_, 1);
lean_inc(v_a_681_);
lean_dec_ref(v_u_668_);
v_a_682_ = lean_ctor_get(v_v_669_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v_v_669_);
v_a_683_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_683_);
lean_dec_ref(v_a_679_);
v___x_684_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_682_);
return v___x_684_;
}
else
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v_v_669_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v_v_669_);
if (lean_obj_tag(v_a_685_) == 5)
{
lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v___x_689_; 
v_a_686_ = lean_ctor_get(v_u_668_, 0);
lean_inc(v_a_686_);
v_a_687_ = lean_ctor_get(v_u_668_, 1);
lean_inc(v_a_687_);
lean_dec_ref(v_u_668_);
v_a_688_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_a_688_);
lean_dec_ref(v_a_685_);
v___x_689_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_686_, v_a_687_, v_a_679_, v_a_688_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_679_);
return v___x_689_;
}
else
{
lean_dec(v_a_685_);
lean_dec(v_a_679_);
lean_dec_ref(v_u_668_);
goto v___jp_675_;
}
}
}
else
{
lean_dec_ref(v_u_668_);
lean_dec(v_v_669_);
goto v___jp_675_;
}
}
else
{
lean_dec(v_v_669_);
lean_dec(v_u_668_);
goto v___jp_675_;
}
v___jp_675_:
{
uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = 0;
v___x_677_ = lean_box(v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_690_, lean_object* v_v_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_690_, v_v_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_705_ = l_Lean_Name_append(v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_709_, lean_object* v_rhs_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_options_716_; lean_object* v_ref_717_; lean_object* v_inheritedTraceOptions_718_; lean_object* v___y_720_; uint8_t v_hasTrace_740_; 
v_options_716_ = lean_ctor_get(v_a_713_, 2);
v_ref_717_ = lean_ctor_get(v_a_713_, 5);
v_inheritedTraceOptions_718_ = lean_ctor_get(v_a_713_, 13);
v_hasTrace_740_ = lean_ctor_get_uint8(v_options_716_, sizeof(void*)*1);
if (v_hasTrace_740_ == 0)
{
v___y_720_ = v_a_712_;
goto v___jp_719_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_718_, v_options_716_, v___x_742_);
if (v___x_743_ == 0)
{
v___y_720_ = v_a_712_;
goto v___jp_719_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_inc(v_lhs_709_);
v___x_744_ = l_Lean_MessageData_ofLevel(v_lhs_709_);
v___x_745_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
lean_inc(v_rhs_710_);
v___x_747_ = l_Lean_MessageData_ofLevel(v_rhs_710_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_741_, v___x_748_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec_ref(v___x_749_);
v___y_720_ = v_a_712_;
goto v___jp_719_;
}
else
{
lean_dec(v_rhs_710_);
lean_dec(v_lhs_709_);
return v___x_749_;
}
}
}
v___jp_719_:
{
lean_object* v___x_721_; lean_object* v_mctx_722_; lean_object* v_cache_723_; lean_object* v_zetaDeltaFVarIds_724_; lean_object* v_postponed_725_; lean_object* v_diag_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_739_; 
v___x_721_ = lean_st_ref_take(v___y_720_);
v_mctx_722_ = lean_ctor_get(v___x_721_, 0);
v_cache_723_ = lean_ctor_get(v___x_721_, 1);
v_zetaDeltaFVarIds_724_ = lean_ctor_get(v___x_721_, 2);
v_postponed_725_ = lean_ctor_get(v___x_721_, 3);
v_diag_726_ = lean_ctor_get(v___x_721_, 4);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_739_ == 0)
{
v___x_728_ = v___x_721_;
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_diag_726_);
lean_inc(v_postponed_725_);
lean_inc(v_zetaDeltaFVarIds_724_);
lean_inc(v_cache_723_);
lean_inc(v_mctx_722_);
lean_dec(v___x_721_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_defEqCtx_x3f_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v_defEqCtx_x3f_730_ = lean_ctor_get(v_a_711_, 4);
lean_inc(v_defEqCtx_x3f_730_);
lean_inc(v_ref_717_);
v___x_731_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_731_, 0, v_ref_717_);
lean_ctor_set(v___x_731_, 1, v_lhs_709_);
lean_ctor_set(v___x_731_, 2, v_rhs_710_);
lean_ctor_set(v___x_731_, 3, v_defEqCtx_x3f_730_);
v___x_732_ = l_Lean_PersistentArray_push___redArg(v_postponed_725_, v___x_731_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v___x_732_);
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_mctx_722_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_cache_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_zetaDeltaFVarIds_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_diag_726_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_st_ref_set(v___y_720_, v___x_734_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_750_, lean_object* v_rhs_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_750_, v_rhs_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_758_, lean_object* v_mvarId_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
if (lean_obj_tag(v_v_758_) == 5)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v_v_758_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v_v_758_);
v___x_766_ = l_Lean_LMVarId_getLevel(v_a_765_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = l_Lean_LMVarId_getLevel(v_mvarId_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_778_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_778_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = lean_nat_dec_lt(v_a_769_, v_a_767_);
lean_dec(v_a_767_);
lean_dec(v_a_769_);
v___x_774_ = lean_box(v___x_773_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_767_);
v_a_779_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_768_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_mvarId_759_);
v_a_787_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_766_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_766_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_mvarId_759_);
lean_dec(v_v_758_);
v___x_795_ = 0;
v___x_796_ = lean_box(v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_798_, lean_object* v_mvarId_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_798_, v_mvarId_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_806_, lean_object* v_v_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___y_814_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_889_; lean_object* v___y_903_; 
switch(lean_obj_tag(v_u_806_))
{
case 5:
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v_u_806_, 0);
lean_inc(v_a_916_);
v___x_917_ = l_Lean_LMVarId_isReadOnly(v_a_916_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_1014_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_1014_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_1014_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v___x_922_; 
v___x_922_ = lean_unbox(v_a_918_);
lean_dec(v_a_918_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_del_object(v___x_920_);
lean_inc(v_a_916_);
lean_inc(v_v_807_);
v___x_923_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_807_, v_a_916_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_1000_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_1000_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_1000_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
uint8_t v___y_935_; uint8_t v___x_956_; 
v___x_956_ = lean_unbox(v_a_924_);
lean_dec(v_a_924_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; 
v___x_957_ = l_Lean_Level_occurs(v_u_806_, v_v_807_);
if (v___x_957_ == 0)
{
lean_object* v_options_958_; uint8_t v_hasTrace_959_; 
lean_del_object(v___x_926_);
v_options_958_ = lean_ctor_get(v_a_810_, 2);
v_hasTrace_959_ = lean_ctor_get_uint8(v_options_958_, sizeof(void*)*1);
if (v_hasTrace_959_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_889_ = v_a_809_;
goto v___jp_888_;
}
else
{
lean_object* v_inheritedTraceOptions_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_inheritedTraceOptions_960_ = lean_ctor_get(v_a_810_, 13);
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_960_, v_options_958_, v___x_962_);
if (v___x_963_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_889_ = v_a_809_;
goto v___jp_888_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc_ref(v_u_806_);
v___x_964_ = l_Lean_MessageData_ofLevel(v_u_806_);
v___x_965_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_inc(v_v_807_);
v___x_967_ = l_Lean_MessageData_ofLevel(v_v_807_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_961_, v___x_968_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_dec_ref(v___x_969_);
v___y_889_ = v_a_809_;
goto v___jp_888_;
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_u_806_);
lean_dec(v_a_809_);
lean_dec(v_v_807_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
else
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_Level_isMax(v_v_807_);
if (v___x_978_ == 0)
{
v___y_935_ = v___x_978_;
goto v___jp_934_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_806_, v_v_807_);
if (v___x_979_ == 0)
{
v___y_935_ = v___x_978_;
goto v___jp_934_;
}
else
{
lean_dec_ref(v_u_806_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
goto v___jp_928_;
}
}
}
}
else
{
lean_object* v_options_980_; uint8_t v_hasTrace_981_; 
lean_del_object(v___x_926_);
v_options_980_ = lean_ctor_get(v_a_810_, 2);
v_hasTrace_981_ = lean_ctor_get_uint8(v_options_980_, sizeof(void*)*1);
if (v_hasTrace_981_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_903_ = v_a_809_;
goto v___jp_902_;
}
else
{
lean_object* v_inheritedTraceOptions_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_inheritedTraceOptions_982_ = lean_ctor_get(v_a_810_, 13);
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_985_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_982_, v_options_980_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_903_ = v_a_809_;
goto v___jp_902_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_inc(v_v_807_);
v___x_986_ = l_Lean_MessageData_ofLevel(v_v_807_);
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_inc_ref(v_u_806_);
v___x_989_ = l_Lean_MessageData_ofLevel(v_u_806_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_983_, v___x_990_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_dec_ref(v___x_991_);
v___y_903_ = v_a_809_;
goto v___jp_902_;
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_u_806_);
lean_dec(v_a_809_);
lean_dec(v_v_807_);
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
v___jp_928_:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_929_ = 2;
v___x_930_ = lean_box(v___x_929_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_930_);
v___x_932_ = v___x_926_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
v___jp_934_:
{
if (v___y_935_ == 0)
{
lean_dec_ref(v_u_806_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
goto v___jp_928_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_926_);
v___x_936_ = l_Lean_Level_mvarId_x21(v_u_806_);
lean_dec_ref(v_u_806_);
v___x_937_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_936_, v_v_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_946_; 
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_937_, 0);
lean_dec(v_unused_947_);
v___x_939_ = v___x_937_;
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
else
{
lean_dec(v___x_937_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = 1;
v___x_942_ = lean_box(v___x_941_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_937_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_937_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_u_806_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v_a_1001_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_923_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_923_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
lean_dec_ref(v_u_806_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v___x_1009_ = 2;
v___x_1010_ = lean_box(v___x_1009_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_1010_);
v___x_1012_ = v___x_920_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_u_806_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v_a_1015_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_917_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_917_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_807_))
{
case 5:
{
lean_dec_ref(v_v_807_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
goto v___jp_834_;
}
case 2:
{
lean_object* v_a_1023_; lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1023_ = lean_ctor_get(v_v_807_, 0);
lean_inc(v_a_1023_);
v_a_1024_ = lean_ctor_get(v_v_807_, 1);
lean_inc(v_a_1024_);
lean_dec_ref(v_v_807_);
lean_inc(v_a_811_);
lean_inc_ref(v_a_810_);
lean_inc(v_a_809_);
lean_inc_ref(v_a_808_);
v___x_1025_ = lean_is_level_def_eq(v_u_806_, v_a_1023_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; uint8_t v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
v___x_1027_ = lean_unbox(v_a_1026_);
lean_dec(v_a_1026_);
if (v___x_1027_ == 0)
{
lean_dec(v_a_1024_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v___y_814_ = v___x_1025_;
goto v___jp_813_;
}
else
{
lean_object* v___x_1028_; 
lean_dec_ref(v___x_1025_);
v___x_1028_ = lean_is_level_def_eq(v_u_806_, v_a_1024_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
v___y_814_ = v___x_1028_;
goto v___jp_813_;
}
}
else
{
lean_dec(v_a_1024_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v___y_814_ = v___x_1025_;
goto v___jp_813_;
}
}
case 3:
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
v_a_1029_ = lean_ctor_get(v_v_807_, 1);
lean_inc(v_a_1029_);
lean_dec_ref(v_v_807_);
v___x_1030_ = lean_is_level_def_eq(v_u_806_, v_a_1029_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1041_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1035_ = lean_unbox(v_a_1031_);
lean_dec(v_a_1031_);
v___x_1036_ = l_Bool_toLBool(v___x_1035_);
v___x_1037_ = lean_box(v___x_1036_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1039_ = v___x_1033_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1030_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1030_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
case 1:
{
uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref(v_v_807_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v___x_1050_ = 0;
v___x_1051_ = lean_box(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
default: 
{
v___y_843_ = v_a_808_;
v___y_844_ = v_a_809_;
v___y_845_ = v_a_810_;
v___y_846_ = v_a_811_;
goto v___jp_842_;
}
}
}
case 1:
{
lean_object* v_a_1053_; uint8_t v___y_1055_; 
v_a_1053_ = lean_ctor_get(v_u_806_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v_u_806_);
if (lean_obj_tag(v_v_807_) == 5)
{
lean_dec_ref(v_v_807_);
lean_dec(v_a_1053_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
goto v___jp_834_;
}
else
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Lean_Level_isParam(v_v_807_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Lean_Level_isMVar(v_a_1053_);
if (v___x_1100_ == 0)
{
v___y_1055_ = v___x_1100_;
goto v___jp_1054_;
}
else
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Level_occurs(v_a_1053_, v_v_807_);
v___y_1055_ = v___x_1101_;
goto v___jp_1054_;
}
}
else
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v_a_1053_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v___x_1102_ = 0;
v___x_1103_ = lean_box(v___x_1102_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
v___jp_1054_:
{
if (v___y_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_decLevel_x3f(v_v_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1087_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1087_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1087_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
if (lean_obj_tag(v_a_1057_) == 0)
{
uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec(v_a_1053_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v___x_1061_ = 2;
v___x_1062_ = lean_box(v___x_1061_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1062_);
v___x_1064_ = v___x_1059_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v_val_1066_; lean_object* v___x_1067_; 
lean_del_object(v___x_1059_);
v_val_1066_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_val_1066_);
lean_dec_ref(v_a_1057_);
v___x_1067_ = lean_is_level_def_eq(v_a_1053_, v_val_1066_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1078_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1078_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1078_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1072_ = lean_unbox(v_a_1068_);
lean_dec(v_a_1068_);
v___x_1073_ = l_Bool_toLBool(v___x_1072_);
v___x_1074_ = lean_box(v___x_1073_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1074_);
v___x_1076_ = v___x_1070_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1067_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1067_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_1053_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v_a_1088_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1056_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1056_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_a_1053_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v___x_1096_ = 2;
v___x_1097_ = lean_box(v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_807_) == 5)
{
lean_dec_ref(v_v_807_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_u_806_);
goto v___jp_834_;
}
else
{
v___y_843_ = v_a_808_;
v___y_844_ = v_a_809_;
v___y_845_ = v_a_810_;
v___y_846_ = v_a_811_;
goto v___jp_842_;
}
}
}
v___jp_813_:
{
if (lean_obj_tag(v___y_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_825_; 
v_a_815_ = lean_ctor_get(v___y_814_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___y_814_);
if (v_isSharedCheck_825_ == 0)
{
v___x_817_ = v___y_814_;
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___y_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_819_ = lean_unbox(v_a_815_);
lean_dec(v_a_815_);
v___x_820_ = l_Bool_toLBool(v___x_819_);
v___x_821_ = lean_box(v___x_820_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_821_);
v___x_823_ = v___x_817_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___y_814_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___y_814_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___y_814_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___y_814_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
v___jp_834_:
{
uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = 2;
v___x_836_ = lean_box(v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
v___jp_838_:
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = 2;
v___x_840_ = lean_box(v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
v___jp_842_:
{
uint8_t v_univApprox_847_; 
v_univApprox_847_ = lean_ctor_get_uint8(v___y_843_, sizeof(void*)*7 + 1);
if (v_univApprox_847_ == 0)
{
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v_v_807_);
lean_dec(v_u_806_);
goto v___jp_838_;
}
else
{
lean_object* v___x_848_; 
lean_inc(v_v_807_);
lean_inc(v_u_806_);
v___x_848_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_806_, v_v_807_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_879_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_879_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_879_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_879_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
uint8_t v___x_853_; 
v___x_853_ = lean_unbox(v_a_849_);
lean_dec(v_a_849_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_del_object(v___x_851_);
v___x_854_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_806_, v_v_807_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
uint8_t v___x_859_; 
v___x_859_ = lean_unbox(v_a_855_);
lean_dec(v_a_855_);
if (v___x_859_ == 0)
{
lean_del_object(v___x_857_);
goto v___jp_838_;
}
else
{
uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = 1;
v___x_861_ = lean_box(v___x_860_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_861_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_854_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_854_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v_v_807_);
lean_dec(v_u_806_);
v___x_874_ = 1;
v___x_875_ = lean_box(v___x_874_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_875_);
v___x_877_ = v___x_851_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v_v_807_);
lean_dec(v_u_806_);
v_a_880_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_848_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_848_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
v___jp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_900_; 
v___x_890_ = l_Lean_Level_mvarId_x21(v_u_806_);
lean_dec(v_u_806_);
v___x_891_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_890_, v_v_807_, v___y_889_);
lean_dec(v___y_889_);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_891_, 0);
lean_dec(v_unused_901_);
v___x_893_ = v___x_891_;
v_isShared_894_ = v_isSharedCheck_900_;
goto v_resetjp_892_;
}
else
{
lean_dec(v___x_891_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_900_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_895_ = 1;
v___x_896_ = lean_box(v___x_895_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_896_);
v___x_898_ = v___x_893_;
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
v___jp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_914_; 
v___x_904_ = l_Lean_Level_mvarId_x21(v_v_807_);
lean_dec(v_v_807_);
v___x_905_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_904_, v_u_806_, v___y_903_);
lean_dec(v___y_903_);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_905_, 0);
lean_dec(v_unused_915_);
v___x_907_ = v___x_905_;
v_isShared_908_ = v_isSharedCheck_914_;
goto v_resetjp_906_;
}
else
{
lean_dec(v___x_905_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_914_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_909_ = 1;
v___x_910_ = lean_box(v___x_909_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_910_);
v___x_912_ = v___x_907_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1105_, lean_object* v_v_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1105_, v_v_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_mctx_1117_; lean_object* v___x_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1121_; lean_object* v_cache_1122_; lean_object* v_zetaDeltaFVarIds_1123_; lean_object* v_postponed_1124_; lean_object* v_diag_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1134_; 
v___x_1116_ = lean_st_ref_get(v___y_1114_);
v_mctx_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_mctx_1117_);
lean_dec(v___x_1116_);
v___x_1118_ = lean_instantiate_level_mvars(v_mctx_1117_, v_l_1113_);
v_fst_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_fst_1119_);
v_snd_1120_ = lean_ctor_get(v___x_1118_, 1);
lean_inc(v_snd_1120_);
lean_dec_ref(v___x_1118_);
v___x_1121_ = lean_st_ref_take(v___y_1114_);
v_cache_1122_ = lean_ctor_get(v___x_1121_, 1);
v_zetaDeltaFVarIds_1123_ = lean_ctor_get(v___x_1121_, 2);
v_postponed_1124_ = lean_ctor_get(v___x_1121_, 3);
v_diag_1125_ = lean_ctor_get(v___x_1121_, 4);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1135_);
v___x_1127_ = v___x_1121_;
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_diag_1125_);
lean_inc(v_postponed_1124_);
lean_inc(v_zetaDeltaFVarIds_1123_);
lean_inc(v_cache_1122_);
lean_dec(v___x_1121_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_fst_1119_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_fst_1119_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_zetaDeltaFVarIds_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_postponed_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_diag_1125_);
v___x_1130_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_st_ref_set(v___y_1114_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_snd_1120_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1136_, v___y_1137_);
lean_dec(v___y_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1140_, v___y_1142_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_unsigned_to_nat(32u);
v___x_1155_ = lean_mk_empty_array_with_capacity(v___x_1154_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1157_ = ((size_t)5ULL);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_unsigned_to_nat(32u);
v___x_1160_ = lean_mk_empty_array_with_capacity(v___x_1159_);
v___x_1161_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1162_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
lean_ctor_set(v___x_1162_, 2, v___x_1158_);
lean_ctor_set(v___x_1162_, 3, v___x_1158_);
lean_ctor_set_usize(v___x_1162_, 4, v___x_1157_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v_traceState_1166_; lean_object* v_traces_1167_; lean_object* v___x_1168_; lean_object* v_traceState_1169_; lean_object* v_env_1170_; lean_object* v_nextMacroScope_1171_; lean_object* v_ngen_1172_; lean_object* v_auxDeclNGen_1173_; lean_object* v_cache_1174_; lean_object* v_messages_1175_; lean_object* v_infoState_1176_; lean_object* v_snapshotTasks_1177_; lean_object* v_newDecls_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1197_; 
v___x_1165_ = lean_st_ref_get(v___y_1163_);
v_traceState_1166_ = lean_ctor_get(v___x_1165_, 4);
lean_inc_ref(v_traceState_1166_);
lean_dec(v___x_1165_);
v_traces_1167_ = lean_ctor_get(v_traceState_1166_, 0);
lean_inc_ref(v_traces_1167_);
lean_dec_ref(v_traceState_1166_);
v___x_1168_ = lean_st_ref_take(v___y_1163_);
v_traceState_1169_ = lean_ctor_get(v___x_1168_, 4);
v_env_1170_ = lean_ctor_get(v___x_1168_, 0);
v_nextMacroScope_1171_ = lean_ctor_get(v___x_1168_, 1);
v_ngen_1172_ = lean_ctor_get(v___x_1168_, 2);
v_auxDeclNGen_1173_ = lean_ctor_get(v___x_1168_, 3);
v_cache_1174_ = lean_ctor_get(v___x_1168_, 5);
v_messages_1175_ = lean_ctor_get(v___x_1168_, 6);
v_infoState_1176_ = lean_ctor_get(v___x_1168_, 7);
v_snapshotTasks_1177_ = lean_ctor_get(v___x_1168_, 8);
v_newDecls_1178_ = lean_ctor_get(v___x_1168_, 9);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1180_ = v___x_1168_;
v_isShared_1181_ = v_isSharedCheck_1197_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_newDecls_1178_);
lean_inc(v_snapshotTasks_1177_);
lean_inc(v_infoState_1176_);
lean_inc(v_messages_1175_);
lean_inc(v_cache_1174_);
lean_inc(v_traceState_1169_);
lean_inc(v_auxDeclNGen_1173_);
lean_inc(v_ngen_1172_);
lean_inc(v_nextMacroScope_1171_);
lean_inc(v_env_1170_);
lean_dec(v___x_1168_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1197_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
uint64_t v_tid_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1195_; 
v_tid_1182_ = lean_ctor_get_uint64(v_traceState_1169_, sizeof(void*)*1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_traceState_1169_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_traceState_1169_, 0);
lean_dec(v_unused_1196_);
v___x_1184_ = v_traceState_1169_;
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_traceState_1169_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1186_);
lean_ctor_set_uint64(v_reuseFailAlloc_1194_, sizeof(void*)*1, v_tid_1182_);
v___x_1188_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 4, v___x_1188_);
v___x_1190_ = v___x_1180_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_env_1170_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_nextMacroScope_1171_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_ngen_1172_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_auxDeclNGen_1173_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_cache_1174_);
lean_ctor_set(v_reuseFailAlloc_1193_, 6, v_messages_1175_);
lean_ctor_set(v_reuseFailAlloc_1193_, 7, v_infoState_1176_);
lean_ctor_set(v_reuseFailAlloc_1193_, 8, v_snapshotTasks_1177_);
lean_ctor_set(v_reuseFailAlloc_1193_, 9, v_newDecls_1178_);
v___x_1190_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_st_ref_set(v___y_1163_, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_traces_1167_);
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1198_);
lean_dec(v___y_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1213_, lean_object* v_k_1214_, uint8_t v_v_1215_){
_start:
{
lean_object* v_map_1216_; uint8_t v_hasTrace_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1231_; 
v_map_1216_ = lean_ctor_get(v_o_1213_, 0);
v_hasTrace_1217_ = lean_ctor_get_uint8(v_o_1213_, sizeof(void*)*1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_o_1213_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1219_ = v_o_1213_;
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_map_1216_);
lean_dec(v_o_1213_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1221_, 0, v_v_1215_);
lean_inc(v_k_1214_);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1214_, v___x_1221_, v_map_1216_);
if (v_hasTrace_1217_ == 0)
{
lean_object* v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1224_ = l_Lean_Name_isPrefixOf(v___x_1223_, v_k_1214_);
lean_dec(v_k_1214_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1222_);
v___x_1226_ = v___x_1219_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1222_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*1, v___x_1224_);
return v___x_1226_;
}
}
else
{
lean_object* v___x_1229_; 
lean_dec(v_k_1214_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1222_);
v___x_1229_ = v___x_1219_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*1, v_hasTrace_1217_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1232_, lean_object* v_k_1233_, lean_object* v_v_1234_){
_start:
{
uint8_t v_v_boxed_1235_; lean_object* v_res_1236_; 
v_v_boxed_1235_ = lean_unbox(v_v_1234_);
v_res_1236_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1232_, v_k_1233_, v_v_boxed_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1237_, lean_object* v_opt_1238_){
_start:
{
lean_object* v_name_1239_; lean_object* v_defValue_1240_; lean_object* v_map_1241_; lean_object* v___x_1242_; 
v_name_1239_ = lean_ctor_get(v_opt_1238_, 0);
v_defValue_1240_ = lean_ctor_get(v_opt_1238_, 1);
v_map_1241_ = lean_ctor_get(v_opts_1237_, 0);
v___x_1242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1241_, v_name_1239_);
if (lean_obj_tag(v___x_1242_) == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_unbox(v_defValue_1240_);
return v___x_1243_;
}
else
{
lean_object* v_val_1244_; 
v_val_1244_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v_val_1244_) == 1)
{
uint8_t v_v_1245_; 
v_v_1245_ = lean_ctor_get_uint8(v_val_1244_, 0);
lean_dec_ref(v_val_1244_);
return v_v_1245_;
}
else
{
uint8_t v___x_1246_; 
lean_dec(v_val_1244_);
v___x_1246_ = lean_unbox(v_defValue_1240_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1247_, lean_object* v_opt_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1247_, v_opt_1248_);
lean_dec_ref(v_opt_1248_);
lean_dec_ref(v_opts_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1251_, lean_object* v_opt_1252_){
_start:
{
lean_object* v_name_1253_; lean_object* v_defValue_1254_; lean_object* v_map_1255_; lean_object* v___x_1256_; 
v_name_1253_ = lean_ctor_get(v_opt_1252_, 0);
v_defValue_1254_ = lean_ctor_get(v_opt_1252_, 1);
v_map_1255_ = lean_ctor_get(v_opts_1251_, 0);
v___x_1256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1255_, v_name_1253_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_inc(v_defValue_1254_);
return v_defValue_1254_;
}
else
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_val_1257_);
lean_dec_ref(v___x_1256_);
if (lean_obj_tag(v_val_1257_) == 3)
{
lean_object* v_v_1258_; 
v_v_1258_ = lean_ctor_get(v_val_1257_, 0);
lean_inc(v_v_1258_);
lean_dec_ref(v_val_1257_);
return v_v_1258_;
}
else
{
lean_dec(v_val_1257_);
lean_inc(v_defValue_1254_);
return v_defValue_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1259_, lean_object* v_opt_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1259_, v_opt_1260_);
lean_dec_ref(v_opt_1260_);
lean_dec_ref(v_opts_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1262_, lean_object* v_lhs_1263_, lean_object* v_rhs_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, uint8_t v___x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___y_1300_; 
if (v___x_1262_ == 0)
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
lean_inc(v_lhs_1263_);
v___x_1337_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1263_, v___y_1269_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
lean_inc(v_rhs_1264_);
v___x_1339_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1264_, v___y_1269_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = l_Lean_Level_normalize(v_a_1338_);
lean_dec(v_a_1338_);
v___x_1342_ = l_Lean_Level_normalize(v_a_1340_);
lean_dec(v_a_1340_);
v___x_1343_ = lean_level_eq(v_lhs_1263_, v___x_1341_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
v___x_1344_ = lean_is_level_def_eq(v___x_1341_, v___x_1342_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1344_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_level_eq(v_rhs_1264_, v___x_1342_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
v___x_1346_ = lean_is_level_def_eq(v___x_1341_, v___x_1342_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v___x_1342_);
lean_dec(v___x_1341_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v_rhs_1264_);
lean_inc(v_lhs_1263_);
v___x_1347_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1263_, v_rhs_1264_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1389_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1389_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1389_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; 
v___x_1352_ = 2;
v___x_1353_ = lean_unbox(v_a_1348_);
v___x_1354_ = l_Lean_instBEqLBool_beq(v___x_1353_, v___x_1352_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v___x_1355_ = 1;
v___x_1356_ = lean_unbox(v_a_1348_);
lean_dec(v_a_1348_);
v___x_1357_ = l_Lean_instBEqLBool_beq(v___x_1356_, v___x_1355_);
v___x_1358_ = lean_box(v___x_1357_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1358_);
v___x_1360_ = v___x_1350_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v___x_1362_; 
lean_del_object(v___x_1350_);
lean_dec(v_a_1348_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v_lhs_1263_);
lean_inc(v_rhs_1264_);
v___x_1362_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1264_, v_lhs_1263_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1380_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1380_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1380_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_unbox(v_a_1363_);
v___x_1368_ = l_Lean_instBEqLBool_beq(v___x_1367_, v___x_1352_);
if (v___x_1368_ == 0)
{
uint8_t v___x_1369_; uint8_t v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v___x_1369_ = 1;
v___x_1370_ = lean_unbox(v_a_1363_);
lean_dec(v_a_1363_);
v___x_1371_ = l_Lean_instBEqLBool_beq(v___x_1370_, v___x_1369_);
v___x_1372_ = lean_box(v___x_1371_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1372_);
v___x_1374_ = v___x_1365_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
else
{
lean_object* v___x_1376_; 
lean_del_object(v___x_1365_);
lean_dec(v_a_1363_);
lean_inc(v_lhs_1263_);
v___x_1376_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1263_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; uint8_t v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
v___x_1378_ = lean_unbox(v_a_1377_);
lean_dec(v_a_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v___x_1376_);
lean_inc(v_rhs_1264_);
v___x_1379_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1264_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
v___y_1300_ = v___x_1379_;
goto v___jp_1299_;
}
else
{
v___y_1300_ = v___x_1376_;
goto v___jp_1299_;
}
}
else
{
v___y_1300_ = v___x_1376_;
goto v___jp_1299_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v_a_1381_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1362_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1362_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v_a_1390_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1347_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1347_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1398_ = l_Lean_Level_getOffset(v_lhs_1263_);
lean_dec(v_lhs_1263_);
v___x_1399_ = l_Lean_Level_getOffset(v_rhs_1264_);
lean_dec(v_rhs_1264_);
v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
lean_dec(v___x_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
v___jp_1273_:
{
lean_object* v_options_1274_; uint8_t v_hasTrace_1275_; 
v_options_1274_ = lean_ctor_get(v___y_1270_, 2);
v_hasTrace_1275_ = lean_ctor_get_uint8(v_options_1274_, sizeof(void*)*1);
if (v_hasTrace_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v___x_1276_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1276_;
}
else
{
lean_object* v_inheritedTraceOptions_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_inheritedTraceOptions_1277_ = lean_ctor_get(v___y_1270_, 13);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1279_ = l_Lean_Name_mkStr3(v___x_1265_, v___x_1266_, v___x_1278_);
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1279_);
v___x_1281_ = l_Lean_Name_append(v___x_1280_, v___x_1279_);
v___x_1282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1277_, v_options_1274_, v___x_1281_);
lean_dec(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v___x_1279_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v___x_1283_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1284_ = l_Lean_MessageData_ofLevel(v_lhs_1263_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_MessageData_ofLevel(v_rhs_1264_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1279_, v___x_1288_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref(v___x_1289_);
v___x_1290_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1290_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1289_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
v___jp_1299_:
{
if (lean_obj_tag(v___y_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1336_; 
v_a_1301_ = lean_ctor_get(v___y_1300_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___y_1300_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1303_ = v___y_1300_;
v_isShared_1304_ = v_isSharedCheck_1336_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___y_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1336_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_unbox(v_a_1301_);
lean_dec(v_a_1301_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; uint8_t v_isDefEqStuckEx_1307_; 
v___x_1306_ = l_Lean_Meta_Context_config(v___y_1268_);
v_isDefEqStuckEx_1307_ = lean_ctor_get_uint8(v___x_1306_, 4);
lean_dec_ref(v___x_1306_);
if (v_isDefEqStuckEx_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v___x_1308_ = lean_box(v_isDefEqStuckEx_1307_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1308_);
v___x_1310_ = v___x_1303_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
uint8_t v___x_1312_; 
v___x_1312_ = l_Lean_Level_isMVar(v_lhs_1263_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_Level_isMVar(v_rhs_1264_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
v___x_1314_ = lean_box(v___x_1313_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1314_);
v___x_1316_ = v___x_1303_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
else
{
lean_del_object(v___x_1303_);
goto v___jp_1273_;
}
}
else
{
lean_del_object(v___x_1303_);
goto v___jp_1273_;
}
}
}
else
{
lean_object* v___x_1318_; 
lean_del_object(v___x_1303_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1318_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1263_, v_rhs_1264_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1318_, 0);
lean_dec(v_unused_1327_);
v___x_1320_ = v___x_1318_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_dec(v___x_1318_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_box(v___x_1267_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1328_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1318_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1318_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec(v_rhs_1264_);
lean_dec(v_lhs_1263_);
return v___y_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1403_, lean_object* v_lhs_1404_, lean_object* v_rhs_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___x_15067__boxed_1414_; uint8_t v___x_15070__boxed_1415_; lean_object* v_res_1416_; 
v___x_15067__boxed_1414_ = lean_unbox(v___x_1403_);
v___x_15070__boxed_1415_ = lean_unbox(v___x_1408_);
v_res_1416_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_15067__boxed_1414_, v_lhs_1404_, v_rhs_1405_, v___x_1406_, v___x_1407_, v___x_15070__boxed_1415_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_a_1419_ = lean_ctor_get(v_x_1417_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1417_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v_x_1417_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v_x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 1);
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v_x_1417_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1417_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v_x_1417_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v_x_1417_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 0);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg___boxed(lean_object* v_x_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_x_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(size_t v_sz_1438_, size_t v_i_1439_, lean_object* v_bs_1440_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1439_, v_sz_1438_);
if (v___x_1441_ == 0)
{
return v_bs_1440_;
}
else
{
lean_object* v_v_1442_; lean_object* v_msg_1443_; lean_object* v___x_1444_; lean_object* v_bs_x27_1445_; size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v_v_1442_ = lean_array_uget_borrowed(v_bs_1440_, v_i_1439_);
v_msg_1443_ = lean_ctor_get(v_v_1442_, 1);
lean_inc_ref(v_msg_1443_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v_bs_x27_1445_ = lean_array_uset(v_bs_1440_, v_i_1439_, v___x_1444_);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_add(v_i_1439_, v___x_1446_);
v___x_1448_ = lean_array_uset(v_bs_x27_1445_, v_i_1439_, v_msg_1443_);
v_i_1439_ = v___x_1447_;
v_bs_1440_ = v___x_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_1450_, lean_object* v_i_1451_, lean_object* v_bs_1452_){
_start:
{
size_t v_sz_boxed_1453_; size_t v_i_boxed_1454_; lean_object* v_res_1455_; 
v_sz_boxed_1453_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1454_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(v_sz_boxed_1453_, v_i_boxed_1454_, v_bs_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_oldTraces_1456_, lean_object* v_data_1457_, lean_object* v_ref_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_fileName_1465_; lean_object* v_fileMap_1466_; lean_object* v_options_1467_; lean_object* v_currRecDepth_1468_; lean_object* v_maxRecDepth_1469_; lean_object* v_ref_1470_; lean_object* v_currNamespace_1471_; lean_object* v_openDecls_1472_; lean_object* v_initHeartbeats_1473_; lean_object* v_maxHeartbeats_1474_; lean_object* v_quotContext_1475_; lean_object* v_currMacroScope_1476_; uint8_t v_diag_1477_; lean_object* v_cancelTk_x3f_1478_; uint8_t v_suppressElabErrors_1479_; lean_object* v_inheritedTraceOptions_1480_; lean_object* v___x_1481_; lean_object* v_traceState_1482_; lean_object* v_traces_1483_; lean_object* v_ref_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; size_t v_sz_1487_; size_t v___x_1488_; lean_object* v___x_1489_; lean_object* v_msg_1490_; lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1530_; 
v_fileName_1465_ = lean_ctor_get(v___y_1462_, 0);
v_fileMap_1466_ = lean_ctor_get(v___y_1462_, 1);
v_options_1467_ = lean_ctor_get(v___y_1462_, 2);
v_currRecDepth_1468_ = lean_ctor_get(v___y_1462_, 3);
v_maxRecDepth_1469_ = lean_ctor_get(v___y_1462_, 4);
v_ref_1470_ = lean_ctor_get(v___y_1462_, 5);
v_currNamespace_1471_ = lean_ctor_get(v___y_1462_, 6);
v_openDecls_1472_ = lean_ctor_get(v___y_1462_, 7);
v_initHeartbeats_1473_ = lean_ctor_get(v___y_1462_, 8);
v_maxHeartbeats_1474_ = lean_ctor_get(v___y_1462_, 9);
v_quotContext_1475_ = lean_ctor_get(v___y_1462_, 10);
v_currMacroScope_1476_ = lean_ctor_get(v___y_1462_, 11);
v_diag_1477_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*14);
v_cancelTk_x3f_1478_ = lean_ctor_get(v___y_1462_, 12);
v_suppressElabErrors_1479_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1480_ = lean_ctor_get(v___y_1462_, 13);
v___x_1481_ = lean_st_ref_get(v___y_1463_);
v_traceState_1482_ = lean_ctor_get(v___x_1481_, 4);
lean_inc_ref(v_traceState_1482_);
lean_dec(v___x_1481_);
v_traces_1483_ = lean_ctor_get(v_traceState_1482_, 0);
lean_inc_ref(v_traces_1483_);
lean_dec_ref(v_traceState_1482_);
v_ref_1484_ = l_Lean_replaceRef(v_ref_1458_, v_ref_1470_);
lean_inc_ref(v_inheritedTraceOptions_1480_);
lean_inc(v_cancelTk_x3f_1478_);
lean_inc(v_currMacroScope_1476_);
lean_inc(v_quotContext_1475_);
lean_inc(v_maxHeartbeats_1474_);
lean_inc(v_initHeartbeats_1473_);
lean_inc(v_openDecls_1472_);
lean_inc(v_currNamespace_1471_);
lean_inc(v_maxRecDepth_1469_);
lean_inc(v_currRecDepth_1468_);
lean_inc_ref(v_options_1467_);
lean_inc_ref(v_fileMap_1466_);
lean_inc_ref(v_fileName_1465_);
v___x_1485_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1485_, 0, v_fileName_1465_);
lean_ctor_set(v___x_1485_, 1, v_fileMap_1466_);
lean_ctor_set(v___x_1485_, 2, v_options_1467_);
lean_ctor_set(v___x_1485_, 3, v_currRecDepth_1468_);
lean_ctor_set(v___x_1485_, 4, v_maxRecDepth_1469_);
lean_ctor_set(v___x_1485_, 5, v_ref_1484_);
lean_ctor_set(v___x_1485_, 6, v_currNamespace_1471_);
lean_ctor_set(v___x_1485_, 7, v_openDecls_1472_);
lean_ctor_set(v___x_1485_, 8, v_initHeartbeats_1473_);
lean_ctor_set(v___x_1485_, 9, v_maxHeartbeats_1474_);
lean_ctor_set(v___x_1485_, 10, v_quotContext_1475_);
lean_ctor_set(v___x_1485_, 11, v_currMacroScope_1476_);
lean_ctor_set(v___x_1485_, 12, v_cancelTk_x3f_1478_);
lean_ctor_set(v___x_1485_, 13, v_inheritedTraceOptions_1480_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*14, v_diag_1477_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*14 + 1, v_suppressElabErrors_1479_);
v___x_1486_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1483_);
lean_dec_ref(v_traces_1483_);
v_sz_1487_ = lean_array_size(v___x_1486_);
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_spec__7(v_sz_1487_, v___x_1488_, v___x_1486_);
v_msg_1490_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1490_, 0, v_data_1457_);
lean_ctor_set(v_msg_1490_, 1, v_msg_1459_);
lean_ctor_set(v_msg_1490_, 2, v___x_1489_);
v___x_1491_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1490_, v___y_1460_, v___y_1461_, v___x_1485_, v___y_1463_);
lean_dec_ref(v___x_1485_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1530_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1530_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v_traceState_1497_; lean_object* v_env_1498_; lean_object* v_nextMacroScope_1499_; lean_object* v_ngen_1500_; lean_object* v_auxDeclNGen_1501_; lean_object* v_cache_1502_; lean_object* v_messages_1503_; lean_object* v_infoState_1504_; lean_object* v_snapshotTasks_1505_; lean_object* v_newDecls_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1529_; 
v___x_1496_ = lean_st_ref_take(v___y_1463_);
v_traceState_1497_ = lean_ctor_get(v___x_1496_, 4);
v_env_1498_ = lean_ctor_get(v___x_1496_, 0);
v_nextMacroScope_1499_ = lean_ctor_get(v___x_1496_, 1);
v_ngen_1500_ = lean_ctor_get(v___x_1496_, 2);
v_auxDeclNGen_1501_ = lean_ctor_get(v___x_1496_, 3);
v_cache_1502_ = lean_ctor_get(v___x_1496_, 5);
v_messages_1503_ = lean_ctor_get(v___x_1496_, 6);
v_infoState_1504_ = lean_ctor_get(v___x_1496_, 7);
v_snapshotTasks_1505_ = lean_ctor_get(v___x_1496_, 8);
v_newDecls_1506_ = lean_ctor_get(v___x_1496_, 9);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1508_ = v___x_1496_;
v_isShared_1509_ = v_isSharedCheck_1529_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_newDecls_1506_);
lean_inc(v_snapshotTasks_1505_);
lean_inc(v_infoState_1504_);
lean_inc(v_messages_1503_);
lean_inc(v_cache_1502_);
lean_inc(v_traceState_1497_);
lean_inc(v_auxDeclNGen_1501_);
lean_inc(v_ngen_1500_);
lean_inc(v_nextMacroScope_1499_);
lean_inc(v_env_1498_);
lean_dec(v___x_1496_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1529_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint64_t v_tid_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1527_; 
v_tid_1510_ = lean_ctor_get_uint64(v_traceState_1497_, sizeof(void*)*1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_traceState_1497_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_traceState_1497_, 0);
lean_dec(v_unused_1528_);
v___x_1512_ = v_traceState_1497_;
v_isShared_1513_ = v_isSharedCheck_1527_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v_traceState_1497_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1527_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_ref_1458_);
lean_ctor_set(v___x_1514_, 1, v_a_1492_);
v___x_1515_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1456_, v___x_1514_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1515_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1515_);
lean_ctor_set_uint64(v_reuseFailAlloc_1526_, sizeof(void*)*1, v_tid_1510_);
v___x_1517_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v___x_1517_);
v___x_1519_ = v___x_1508_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_env_1498_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_nextMacroScope_1499_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_ngen_1500_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_auxDeclNGen_1501_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1525_, 5, v_cache_1502_);
lean_ctor_set(v_reuseFailAlloc_1525_, 6, v_messages_1503_);
lean_ctor_set(v_reuseFailAlloc_1525_, 7, v_infoState_1504_);
lean_ctor_set(v_reuseFailAlloc_1525_, 8, v_snapshotTasks_1505_);
lean_ctor_set(v_reuseFailAlloc_1525_, 9, v_newDecls_1506_);
v___x_1519_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = lean_st_ref_set(v___y_1463_, v___x_1519_);
v___x_1521_ = lean_box(0);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1521_);
v___x_1523_ = v___x_1494_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_oldTraces_1531_, lean_object* v_data_1532_, lean_object* v_ref_1533_, lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_oldTraces_1531_, v_data_1532_, v_ref_1533_, v_msg_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_e_1541_){
_start:
{
if (lean_obj_tag(v_e_1541_) == 0)
{
uint8_t v___x_1542_; 
v___x_1542_ = 2;
return v___x_1542_;
}
else
{
lean_object* v_a_1543_; uint8_t v___x_1544_; 
v_a_1543_ = lean_ctor_get(v_e_1541_, 0);
v___x_1544_ = lean_unbox(v_a_1543_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = 1;
return v___x_1545_;
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = 0;
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_e_1547_){
_start:
{
uint8_t v_res_1548_; lean_object* v_r_1549_; 
v_res_1548_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_e_1547_);
lean_dec_ref(v_e_1547_);
v_r_1549_ = lean_box(v_res_1548_);
return v_r_1549_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1553_; double v___x_1554_; 
v___x_1553_ = lean_unsigned_to_nat(1000u);
v___x_1554_ = lean_float_of_nat(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1555_, uint8_t v_collapsed_1556_, lean_object* v_tag_1557_, lean_object* v_opts_1558_, uint8_t v_clsEnabled_1559_, lean_object* v_oldTraces_1560_, lean_object* v_ref_1561_, lean_object* v_msg_1562_, lean_object* v_resStartStop_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_fst_1569_; lean_object* v_snd_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1661_; 
v_fst_1569_ = lean_ctor_get(v_resStartStop_1563_, 0);
v_snd_1570_ = lean_ctor_get(v_resStartStop_1563_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_resStartStop_1563_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1572_ = v_resStartStop_1563_;
v_isShared_1573_ = v_isSharedCheck_1661_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snd_1570_);
lean_inc(v_fst_1569_);
lean_dec(v_resStartStop_1563_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1661_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___y_1575_; lean_object* v_data_1576_; lean_object* v_fst_1587_; lean_object* v_snd_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1660_; 
v_fst_1587_ = lean_ctor_get(v_snd_1570_, 0);
v_snd_1588_ = lean_ctor_get(v_snd_1570_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_snd_1570_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1590_ = v_snd_1570_;
v_isShared_1591_ = v_isSharedCheck_1660_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snd_1588_);
lean_inc(v_fst_1587_);
lean_dec(v_snd_1570_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1660_;
goto v_resetjp_1589_;
}
v___jp_1574_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_oldTraces_1560_, v_data_1576_, v_ref_1561_, v___y_1575_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___x_1577_);
v___x_1578_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_fst_1569_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_fst_1569_);
v_a_1579_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1577_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; uint8_t v___y_1613_; double v___y_1645_; 
v___x_1592_ = l_Lean_trace_profiler;
v___x_1593_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1558_, v___x_1592_);
if (v___x_1593_ == 0)
{
v___y_1613_ = v___x_1593_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1651_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1558_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; double v___x_1654_; double v___x_1655_; double v___x_1656_; 
v___x_1652_ = l_Lean_trace_profiler_threshold;
v___x_1653_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1558_, v___x_1652_);
v___x_1654_ = lean_float_of_nat(v___x_1653_);
v___x_1655_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__2);
v___x_1656_ = lean_float_div(v___x_1654_, v___x_1655_);
v___y_1645_ = v___x_1656_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; double v___x_1659_; 
v___x_1657_ = l_Lean_trace_profiler_threshold;
v___x_1658_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1558_, v___x_1657_);
v___x_1659_ = lean_float_of_nat(v___x_1658_);
v___y_1645_ = v___x_1659_;
goto v___jp_1644_;
}
}
v___jp_1594_:
{
uint8_t v_result_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v_result_1595_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_fst_1569_);
v___x_1596_ = l_Lean_TraceResult_toEmoji(v_result_1595_);
v___x_1597_ = l_Lean_stringToMessageData(v___x_1596_);
v___x_1598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__1);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 7);
lean_ctor_set(v___x_1590_, 1, v___x_1598_);
lean_ctor_set(v___x_1590_, 0, v___x_1597_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v_msg_1602_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 7);
lean_ctor_set(v___x_1572_, 1, v_msg_1562_);
lean_ctor_set(v___x_1572_, 0, v___x_1600_);
v_msg_1602_ = v___x_1572_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_msg_1562_);
v_msg_1602_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; double v___x_1605_; lean_object* v_data_1606_; 
v___x_1603_ = lean_box(v_result_1595_);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1557_);
lean_inc_ref(v___x_1604_);
lean_inc(v_cls_1555_);
v_data_1606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1606_, 0, v_cls_1555_);
lean_ctor_set(v_data_1606_, 1, v___x_1604_);
lean_ctor_set(v_data_1606_, 2, v_tag_1557_);
lean_ctor_set_float(v_data_1606_, sizeof(void*)*3, v___x_1605_);
lean_ctor_set_float(v_data_1606_, sizeof(void*)*3 + 8, v___x_1605_);
lean_ctor_set_uint8(v_data_1606_, sizeof(void*)*3 + 16, v_collapsed_1556_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v___x_1604_);
lean_dec(v_snd_1588_);
lean_dec(v_fst_1587_);
lean_dec_ref(v_tag_1557_);
lean_dec(v_cls_1555_);
v___y_1575_ = v_msg_1602_;
v_data_1576_ = v_data_1606_;
goto v___jp_1574_;
}
else
{
lean_object* v_data_1607_; double v___x_1608_; double v___x_1609_; 
lean_dec_ref(v_data_1606_);
v_data_1607_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1607_, 0, v_cls_1555_);
lean_ctor_set(v_data_1607_, 1, v___x_1604_);
lean_ctor_set(v_data_1607_, 2, v_tag_1557_);
v___x_1608_ = lean_unbox_float(v_fst_1587_);
lean_dec(v_fst_1587_);
lean_ctor_set_float(v_data_1607_, sizeof(void*)*3, v___x_1608_);
v___x_1609_ = lean_unbox_float(v_snd_1588_);
lean_dec(v_snd_1588_);
lean_ctor_set_float(v_data_1607_, sizeof(void*)*3 + 8, v___x_1609_);
lean_ctor_set_uint8(v_data_1607_, sizeof(void*)*3 + 16, v_collapsed_1556_);
v___y_1575_ = v_msg_1602_;
v_data_1576_ = v_data_1607_;
goto v___jp_1574_;
}
}
}
}
v___jp_1612_:
{
if (v_clsEnabled_1559_ == 0)
{
if (v___y_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v_traceState_1615_; lean_object* v_env_1616_; lean_object* v_nextMacroScope_1617_; lean_object* v_ngen_1618_; lean_object* v_auxDeclNGen_1619_; lean_object* v_cache_1620_; lean_object* v_messages_1621_; lean_object* v_infoState_1622_; lean_object* v_snapshotTasks_1623_; lean_object* v_newDecls_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1643_; 
lean_del_object(v___x_1590_);
lean_dec(v_snd_1588_);
lean_dec(v_fst_1587_);
lean_del_object(v___x_1572_);
lean_dec_ref(v_msg_1562_);
lean_dec(v_ref_1561_);
lean_dec_ref(v_tag_1557_);
lean_dec(v_cls_1555_);
v___x_1614_ = lean_st_ref_take(v___y_1567_);
v_traceState_1615_ = lean_ctor_get(v___x_1614_, 4);
v_env_1616_ = lean_ctor_get(v___x_1614_, 0);
v_nextMacroScope_1617_ = lean_ctor_get(v___x_1614_, 1);
v_ngen_1618_ = lean_ctor_get(v___x_1614_, 2);
v_auxDeclNGen_1619_ = lean_ctor_get(v___x_1614_, 3);
v_cache_1620_ = lean_ctor_get(v___x_1614_, 5);
v_messages_1621_ = lean_ctor_get(v___x_1614_, 6);
v_infoState_1622_ = lean_ctor_get(v___x_1614_, 7);
v_snapshotTasks_1623_ = lean_ctor_get(v___x_1614_, 8);
v_newDecls_1624_ = lean_ctor_get(v___x_1614_, 9);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1626_ = v___x_1614_;
v_isShared_1627_ = v_isSharedCheck_1643_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_newDecls_1624_);
lean_inc(v_snapshotTasks_1623_);
lean_inc(v_infoState_1622_);
lean_inc(v_messages_1621_);
lean_inc(v_cache_1620_);
lean_inc(v_traceState_1615_);
lean_inc(v_auxDeclNGen_1619_);
lean_inc(v_ngen_1618_);
lean_inc(v_nextMacroScope_1617_);
lean_inc(v_env_1616_);
lean_dec(v___x_1614_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1643_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
uint64_t v_tid_1628_; lean_object* v_traces_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1642_; 
v_tid_1628_ = lean_ctor_get_uint64(v_traceState_1615_, sizeof(void*)*1);
v_traces_1629_ = lean_ctor_get(v_traceState_1615_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_traceState_1615_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1631_ = v_traceState_1615_;
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_traces_1629_);
lean_dec(v_traceState_1615_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1560_, v_traces_1629_);
lean_dec_ref(v_traces_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1633_);
lean_ctor_set_uint64(v_reuseFailAlloc_1641_, sizeof(void*)*1, v_tid_1628_);
v___x_1635_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 4, v___x_1635_);
v___x_1637_ = v___x_1626_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_env_1616_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_nextMacroScope_1617_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_ngen_1618_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_auxDeclNGen_1619_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1640_, 5, v_cache_1620_);
lean_ctor_set(v_reuseFailAlloc_1640_, 6, v_messages_1621_);
lean_ctor_set(v_reuseFailAlloc_1640_, 7, v_infoState_1622_);
lean_ctor_set(v_reuseFailAlloc_1640_, 8, v_snapshotTasks_1623_);
lean_ctor_set(v_reuseFailAlloc_1640_, 9, v_newDecls_1624_);
v___x_1637_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_st_ref_set(v___y_1567_, v___x_1637_);
v___x_1639_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_fst_1569_);
return v___x_1639_;
}
}
}
}
}
else
{
goto v___jp_1594_;
}
}
else
{
goto v___jp_1594_;
}
}
v___jp_1644_:
{
double v___x_1646_; double v___x_1647_; double v___x_1648_; uint8_t v___x_1649_; 
v___x_1646_ = lean_unbox_float(v_snd_1588_);
v___x_1647_ = lean_unbox_float(v_fst_1587_);
v___x_1648_ = lean_float_sub(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_float_decLt(v___y_1645_, v___x_1648_);
v___y_1613_ = v___x_1649_;
goto v___jp_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1662_, lean_object* v_collapsed_1663_, lean_object* v_tag_1664_, lean_object* v_opts_1665_, lean_object* v_clsEnabled_1666_, lean_object* v_oldTraces_1667_, lean_object* v_ref_1668_, lean_object* v_msg_1669_, lean_object* v_resStartStop_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_collapsed_boxed_1676_; uint8_t v_clsEnabled_boxed_1677_; lean_object* v_res_1678_; 
v_collapsed_boxed_1676_ = lean_unbox(v_collapsed_1663_);
v_clsEnabled_boxed_1677_ = lean_unbox(v_clsEnabled_1666_);
v_res_1678_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1662_, v_collapsed_boxed_1676_, v_tag_1664_, v_opts_1665_, v_clsEnabled_boxed_1677_, v_oldTraces_1667_, v_ref_1668_, v_msg_1669_, v_resStartStop_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_opts_1665_);
return v_res_1678_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1679_; double v___x_1680_; 
v___x_1679_ = lean_unsigned_to_nat(1000000000u);
v___x_1680_ = lean_float_of_nat(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1696_ = l_Lean_Name_append(v___x_1695_, v___x_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1697_, lean_object* v_x_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
uint8_t v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v_a_1718_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v_a_1741_; uint8_t v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; uint8_t v___y_1759_; uint8_t v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v_fileName_1770_; lean_object* v_fileMap_1771_; lean_object* v_currRecDepth_1772_; lean_object* v_ref_1773_; lean_object* v_currNamespace_1774_; lean_object* v_openDecls_1775_; lean_object* v_initHeartbeats_1776_; lean_object* v_maxHeartbeats_1777_; lean_object* v_quotContext_1778_; lean_object* v_currMacroScope_1779_; lean_object* v_cancelTk_x3f_1780_; uint8_t v_suppressElabErrors_1781_; lean_object* v_inheritedTraceOptions_1782_; lean_object* v___y_1783_; uint8_t v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; uint8_t v___y_1867_; uint8_t v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1878_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; uint8_t v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_lhs_1946_; lean_object* v_rhs_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; 
if (lean_obj_tag(v_x_1697_) == 1)
{
if (lean_obj_tag(v_x_1698_) == 1)
{
lean_object* v_a_1986_; lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1986_ = lean_ctor_get(v_x_1697_, 0);
lean_inc(v_a_1986_);
lean_dec_ref(v_x_1697_);
v_a_1987_ = lean_ctor_get(v_x_1698_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v_x_1698_);
v___x_1988_ = lean_is_level_def_eq(v_a_1986_, v_a_1987_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1988_;
}
else
{
v_lhs_1946_ = v_x_1697_;
v_rhs_1947_ = v_x_1698_;
v___y_1948_ = v_a_1699_;
v___y_1949_ = v_a_1700_;
v___y_1950_ = v_a_1701_;
v___y_1951_ = v_a_1702_;
goto v___jp_1945_;
}
}
else
{
v_lhs_1946_ = v_x_1697_;
v_rhs_1947_ = v_x_1698_;
v___y_1948_ = v_a_1699_;
v___y_1949_ = v_a_1700_;
v___y_1950_ = v_a_1701_;
v___y_1951_ = v_a_1702_;
goto v___jp_1945_;
}
v___jp_1704_:
{
lean_object* v___x_1719_; double v___x_1720_; double v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1719_ = lean_io_get_num_heartbeats();
v___x_1720_ = lean_float_of_nat(v___y_1715_);
v___x_1721_ = lean_float_of_nat(v___x_1719_);
v___x_1722_ = lean_box_float(v___x_1720_);
v___x_1723_ = lean_box_float(v___x_1721_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_a_1718_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
lean_inc_ref(v___y_1712_);
lean_inc(v___y_1706_);
v___x_1726_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1706_, v___y_1709_, v___y_1712_, v___y_1716_, v___y_1705_, v___y_1708_, v___y_1710_, v___y_1717_, v___x_1725_, v___y_1711_, v___y_1707_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1716_);
return v___x_1726_;
}
v___jp_1727_:
{
lean_object* v___x_1742_; double v___x_1743_; double v___x_1744_; double v___x_1745_; double v___x_1746_; double v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1742_ = lean_io_mono_nanos_now();
v___x_1743_ = lean_float_of_nat(v___y_1732_);
v___x_1744_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1745_ = lean_float_div(v___x_1743_, v___x_1744_);
v___x_1746_ = lean_float_of_nat(v___x_1742_);
v___x_1747_ = lean_float_div(v___x_1746_, v___x_1744_);
v___x_1748_ = lean_box_float(v___x_1745_);
v___x_1749_ = lean_box_float(v___x_1747_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_a_1741_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
lean_inc_ref(v___y_1736_);
lean_inc(v___y_1729_);
v___x_1752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1729_, v___y_1733_, v___y_1736_, v___y_1739_, v___y_1728_, v___y_1731_, v___y_1734_, v___y_1740_, v___x_1751_, v___y_1735_, v___y_1730_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v___y_1739_);
return v___x_1752_;
}
v___jp_1753_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_a_1788_; lean_object* v___x_1789_; lean_object* v_a_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1784_ = l_Lean_maxRecDepth;
v___x_1785_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1766_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1786_, 0, v_fileName_1770_);
lean_ctor_set(v___x_1786_, 1, v_fileMap_1771_);
lean_ctor_set(v___x_1786_, 2, v___y_1766_);
lean_ctor_set(v___x_1786_, 3, v_currRecDepth_1772_);
lean_ctor_set(v___x_1786_, 4, v___x_1785_);
lean_ctor_set(v___x_1786_, 5, v_ref_1773_);
lean_ctor_set(v___x_1786_, 6, v_currNamespace_1774_);
lean_ctor_set(v___x_1786_, 7, v_openDecls_1775_);
lean_ctor_set(v___x_1786_, 8, v_initHeartbeats_1776_);
lean_ctor_set(v___x_1786_, 9, v_maxHeartbeats_1777_);
lean_ctor_set(v___x_1786_, 10, v_quotContext_1778_);
lean_ctor_set(v___x_1786_, 11, v_currMacroScope_1779_);
lean_ctor_set(v___x_1786_, 12, v_cancelTk_x3f_1780_);
lean_ctor_set(v___x_1786_, 13, v_inheritedTraceOptions_1782_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*14, v___y_1760_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*14 + 1, v_suppressElabErrors_1781_);
v___x_1787_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1755_, v___y_1762_, v___y_1756_, v___x_1786_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___x_1786_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1788_, v___y_1762_, v___y_1756_, v___y_1769_, v___y_1765_);
lean_dec_ref(v___y_1769_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1792_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1768_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_io_mono_nanos_now();
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1762_);
v___x_1794_ = lean_apply_5(v___y_1767_, v___y_1762_, v___y_1756_, v___y_1764_, v___y_1765_, lean_box(0));
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
v___y_1728_ = v___y_1754_;
v___y_1729_ = v___y_1757_;
v___y_1730_ = v___y_1756_;
v___y_1731_ = v___y_1758_;
v___y_1732_ = v___x_1793_;
v___y_1733_ = v___y_1759_;
v___y_1734_ = v___y_1761_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v___y_1763_;
v___y_1737_ = v___y_1764_;
v___y_1738_ = v___y_1765_;
v___y_1739_ = v___y_1768_;
v___y_1740_ = v_a_1790_;
v_a_1741_ = v___x_1800_;
goto v___jp_1727_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1794_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1794_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 0);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
v___y_1728_ = v___y_1754_;
v___y_1729_ = v___y_1757_;
v___y_1730_ = v___y_1756_;
v___y_1731_ = v___y_1758_;
v___y_1732_ = v___x_1793_;
v___y_1733_ = v___y_1759_;
v___y_1734_ = v___y_1761_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v___y_1763_;
v___y_1737_ = v___y_1764_;
v___y_1738_ = v___y_1765_;
v___y_1739_ = v___y_1768_;
v___y_1740_ = v_a_1790_;
v_a_1741_ = v___x_1808_;
goto v___jp_1727_;
}
}
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1762_);
v___x_1812_ = lean_apply_5(v___y_1767_, v___y_1762_, v___y_1756_, v___y_1764_, v___y_1765_, lean_box(0));
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 1);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v___y_1705_ = v___y_1754_;
v___y_1706_ = v___y_1757_;
v___y_1707_ = v___y_1756_;
v___y_1708_ = v___y_1758_;
v___y_1709_ = v___y_1759_;
v___y_1710_ = v___y_1761_;
v___y_1711_ = v___y_1762_;
v___y_1712_ = v___y_1763_;
v___y_1713_ = v___y_1764_;
v___y_1714_ = v___y_1765_;
v___y_1715_ = v___x_1811_;
v___y_1716_ = v___y_1768_;
v___y_1717_ = v_a_1790_;
v_a_1718_ = v___x_1818_;
goto v___jp_1704_;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1812_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1812_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 0);
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v___y_1705_ = v___y_1754_;
v___y_1706_ = v___y_1757_;
v___y_1707_ = v___y_1756_;
v___y_1708_ = v___y_1758_;
v___y_1709_ = v___y_1759_;
v___y_1710_ = v___y_1761_;
v___y_1711_ = v___y_1762_;
v___y_1712_ = v___y_1763_;
v___y_1713_ = v___y_1764_;
v___y_1714_ = v___y_1765_;
v___y_1715_ = v___x_1811_;
v___y_1716_ = v___y_1768_;
v___y_1717_ = v_a_1790_;
v_a_1718_ = v___x_1826_;
goto v___jp_1704_;
}
}
}
}
}
v___jp_1829_:
{
lean_object* v_fileName_1848_; lean_object* v_fileMap_1849_; lean_object* v_currRecDepth_1850_; lean_object* v_ref_1851_; lean_object* v_currNamespace_1852_; lean_object* v_openDecls_1853_; lean_object* v_initHeartbeats_1854_; lean_object* v_maxHeartbeats_1855_; lean_object* v_quotContext_1856_; lean_object* v_currMacroScope_1857_; lean_object* v_cancelTk_x3f_1858_; uint8_t v_suppressElabErrors_1859_; lean_object* v_inheritedTraceOptions_1860_; 
v_fileName_1848_ = lean_ctor_get(v___y_1846_, 0);
lean_inc_ref(v_fileName_1848_);
v_fileMap_1849_ = lean_ctor_get(v___y_1846_, 1);
lean_inc_ref(v_fileMap_1849_);
v_currRecDepth_1850_ = lean_ctor_get(v___y_1846_, 3);
lean_inc(v_currRecDepth_1850_);
v_ref_1851_ = lean_ctor_get(v___y_1846_, 5);
lean_inc(v_ref_1851_);
v_currNamespace_1852_ = lean_ctor_get(v___y_1846_, 6);
lean_inc(v_currNamespace_1852_);
v_openDecls_1853_ = lean_ctor_get(v___y_1846_, 7);
lean_inc(v_openDecls_1853_);
v_initHeartbeats_1854_ = lean_ctor_get(v___y_1846_, 8);
lean_inc(v_initHeartbeats_1854_);
v_maxHeartbeats_1855_ = lean_ctor_get(v___y_1846_, 9);
lean_inc(v_maxHeartbeats_1855_);
v_quotContext_1856_ = lean_ctor_get(v___y_1846_, 10);
lean_inc(v_quotContext_1856_);
v_currMacroScope_1857_ = lean_ctor_get(v___y_1846_, 11);
lean_inc(v_currMacroScope_1857_);
v_cancelTk_x3f_1858_ = lean_ctor_get(v___y_1846_, 12);
lean_inc(v_cancelTk_x3f_1858_);
v_suppressElabErrors_1859_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1860_ = lean_ctor_get(v___y_1846_, 13);
lean_inc_ref(v_inheritedTraceOptions_1860_);
lean_dec_ref(v___y_1846_);
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
v___y_1766_ = v___y_1842_;
v___y_1767_ = v___y_1843_;
v___y_1768_ = v___y_1844_;
v___y_1769_ = v___y_1845_;
v_fileName_1770_ = v_fileName_1848_;
v_fileMap_1771_ = v_fileMap_1849_;
v_currRecDepth_1772_ = v_currRecDepth_1850_;
v_ref_1773_ = v_ref_1851_;
v_currNamespace_1774_ = v_currNamespace_1852_;
v_openDecls_1775_ = v_openDecls_1853_;
v_initHeartbeats_1776_ = v_initHeartbeats_1854_;
v_maxHeartbeats_1777_ = v_maxHeartbeats_1855_;
v_quotContext_1778_ = v_quotContext_1856_;
v_currMacroScope_1779_ = v_currMacroScope_1857_;
v_cancelTk_x3f_1780_ = v_cancelTk_x3f_1858_;
v_suppressElabErrors_1781_ = v_suppressElabErrors_1859_;
v_inheritedTraceOptions_1782_ = v_inheritedTraceOptions_1860_;
v___y_1783_ = v___y_1847_;
goto v___jp_1753_;
}
v___jp_1861_:
{
if (v___y_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v_env_1880_; lean_object* v_nextMacroScope_1881_; lean_object* v_ngen_1882_; lean_object* v_auxDeclNGen_1883_; lean_object* v_traceState_1884_; lean_object* v_messages_1885_; lean_object* v_infoState_1886_; lean_object* v_snapshotTasks_1887_; lean_object* v_newDecls_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1898_; 
v___x_1879_ = lean_st_ref_take(v___y_1873_);
v_env_1880_ = lean_ctor_get(v___x_1879_, 0);
v_nextMacroScope_1881_ = lean_ctor_get(v___x_1879_, 1);
v_ngen_1882_ = lean_ctor_get(v___x_1879_, 2);
v_auxDeclNGen_1883_ = lean_ctor_get(v___x_1879_, 3);
v_traceState_1884_ = lean_ctor_get(v___x_1879_, 4);
v_messages_1885_ = lean_ctor_get(v___x_1879_, 6);
v_infoState_1886_ = lean_ctor_get(v___x_1879_, 7);
v_snapshotTasks_1887_ = lean_ctor_get(v___x_1879_, 8);
v_newDecls_1888_ = lean_ctor_get(v___x_1879_, 9);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1879_, 5);
lean_dec(v_unused_1899_);
v___x_1890_ = v___x_1879_;
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_newDecls_1888_);
lean_inc(v_snapshotTasks_1887_);
lean_inc(v_infoState_1886_);
lean_inc(v_messages_1885_);
lean_inc(v_traceState_1884_);
lean_inc(v_auxDeclNGen_1883_);
lean_inc(v_ngen_1882_);
lean_inc(v_nextMacroScope_1881_);
lean_inc(v_env_1880_);
lean_dec(v___x_1879_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1898_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1892_ = l_Lean_Kernel_enableDiag(v_env_1880_, v___y_1868_);
v___x_1893_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 5, v___x_1893_);
lean_ctor_set(v___x_1890_, 0, v___x_1892_);
v___x_1895_ = v___x_1890_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_nextMacroScope_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_ngen_1882_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_auxDeclNGen_1883_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v_traceState_1884_);
lean_ctor_set(v_reuseFailAlloc_1897_, 5, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1897_, 6, v_messages_1885_);
lean_ctor_set(v_reuseFailAlloc_1897_, 7, v_infoState_1886_);
lean_ctor_set(v_reuseFailAlloc_1897_, 8, v_snapshotTasks_1887_);
lean_ctor_set(v_reuseFailAlloc_1897_, 9, v_newDecls_1888_);
v___x_1895_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_st_ref_set(v___y_1873_, v___x_1895_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1873_);
v___y_1830_ = v___y_1862_;
v___y_1831_ = v___y_1863_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1865_;
v___y_1834_ = v___y_1866_;
v___y_1835_ = v___y_1867_;
v___y_1836_ = v___y_1868_;
v___y_1837_ = v___y_1869_;
v___y_1838_ = v___y_1870_;
v___y_1839_ = v___y_1871_;
v___y_1840_ = v___y_1872_;
v___y_1841_ = v___y_1873_;
v___y_1842_ = v___y_1874_;
v___y_1843_ = v___y_1875_;
v___y_1844_ = v___y_1876_;
v___y_1845_ = v___y_1877_;
v___y_1846_ = v___y_1877_;
v___y_1847_ = v___y_1873_;
goto v___jp_1829_;
}
}
}
else
{
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1873_);
v___y_1830_ = v___y_1862_;
v___y_1831_ = v___y_1863_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1865_;
v___y_1834_ = v___y_1866_;
v___y_1835_ = v___y_1867_;
v___y_1836_ = v___y_1868_;
v___y_1837_ = v___y_1869_;
v___y_1838_ = v___y_1870_;
v___y_1839_ = v___y_1871_;
v___y_1840_ = v___y_1872_;
v___y_1841_ = v___y_1873_;
v___y_1842_ = v___y_1874_;
v___y_1843_ = v___y_1875_;
v___y_1844_ = v___y_1876_;
v___y_1845_ = v___y_1877_;
v___y_1846_ = v___y_1877_;
v___y_1847_ = v___y_1873_;
goto v___jp_1829_;
}
}
v___jp_1900_:
{
lean_object* v___x_1928_; lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v_env_1931_; lean_object* v_ref_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1928_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1913_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_st_ref_get(v___y_1913_);
v_env_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_env_1931_);
lean_dec(v___x_1930_);
v_ref_1932_ = l_Lean_replaceRef(v___y_1908_, v___y_1908_);
lean_inc_ref(v___y_1901_);
lean_inc(v___y_1915_);
lean_inc(v___y_1911_);
lean_inc(v___y_1920_);
lean_inc(v___y_1905_);
lean_inc(v___y_1919_);
lean_inc(v___y_1906_);
lean_inc(v___y_1909_);
lean_inc(v_ref_1932_);
lean_inc(v___y_1924_);
lean_inc_ref_n(v___y_1927_, 2);
lean_inc_ref(v___y_1914_);
lean_inc_ref(v___y_1921_);
v___x_1933_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1933_, 0, v___y_1921_);
lean_ctor_set(v___x_1933_, 1, v___y_1914_);
lean_ctor_set(v___x_1933_, 2, v___y_1927_);
lean_ctor_set(v___x_1933_, 3, v___y_1924_);
lean_ctor_set(v___x_1933_, 4, v___y_1916_);
lean_ctor_set(v___x_1933_, 5, v_ref_1932_);
lean_ctor_set(v___x_1933_, 6, v___y_1909_);
lean_ctor_set(v___x_1933_, 7, v___y_1906_);
lean_ctor_set(v___x_1933_, 8, v___y_1919_);
lean_ctor_set(v___x_1933_, 9, v___y_1905_);
lean_ctor_set(v___x_1933_, 10, v___y_1920_);
lean_ctor_set(v___x_1933_, 11, v___y_1911_);
lean_ctor_set(v___x_1933_, 12, v___y_1915_);
lean_ctor_set(v___x_1933_, 13, v___y_1901_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*14, v___y_1917_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*14 + 1, v___y_1925_);
v___x_1934_ = l_Lean_MessageData_ofLevel(v___y_1912_);
v___x_1935_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_MessageData_ofLevel(v___y_1903_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1940_ = 0;
v___x_1941_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1927_, v___x_1939_, v___x_1940_);
v___x_1942_ = l_Lean_diagnostics;
v___x_1943_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___x_1941_, v___x_1942_);
v___x_1944_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1931_);
lean_dec_ref(v_env_1931_);
if (v___x_1944_ == 0)
{
if (v___x_1943_ == 0)
{
lean_inc(v___y_1913_);
v___y_1754_ = v___y_1918_;
v___y_1755_ = v___x_1938_;
v___y_1756_ = v___y_1902_;
v___y_1757_ = v___y_1904_;
v___y_1758_ = v_a_1929_;
v___y_1759_ = v___y_1907_;
v___y_1760_ = v___x_1943_;
v___y_1761_ = v___y_1908_;
v___y_1762_ = v___y_1922_;
v___y_1763_ = v___y_1923_;
v___y_1764_ = v___y_1910_;
v___y_1765_ = v___y_1913_;
v___y_1766_ = v___x_1941_;
v___y_1767_ = v___y_1926_;
v___y_1768_ = v___y_1927_;
v___y_1769_ = v___x_1933_;
v_fileName_1770_ = v___y_1921_;
v_fileMap_1771_ = v___y_1914_;
v_currRecDepth_1772_ = v___y_1924_;
v_ref_1773_ = v_ref_1932_;
v_currNamespace_1774_ = v___y_1909_;
v_openDecls_1775_ = v___y_1906_;
v_initHeartbeats_1776_ = v___y_1919_;
v_maxHeartbeats_1777_ = v___y_1905_;
v_quotContext_1778_ = v___y_1920_;
v_currMacroScope_1779_ = v___y_1911_;
v_cancelTk_x3f_1780_ = v___y_1915_;
v_suppressElabErrors_1781_ = v___y_1925_;
v_inheritedTraceOptions_1782_ = v___y_1901_;
v___y_1783_ = v___y_1913_;
goto v___jp_1753_;
}
else
{
lean_dec(v_ref_1932_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v___y_1909_);
lean_dec(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1901_);
v___y_1862_ = v___y_1918_;
v___y_1863_ = v___x_1938_;
v___y_1864_ = v___y_1902_;
v___y_1865_ = v___y_1904_;
v___y_1866_ = v_a_1929_;
v___y_1867_ = v___y_1907_;
v___y_1868_ = v___x_1943_;
v___y_1869_ = v___y_1908_;
v___y_1870_ = v___y_1922_;
v___y_1871_ = v___y_1923_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1913_;
v___y_1874_ = v___x_1941_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1927_;
v___y_1877_ = v___x_1933_;
v___y_1878_ = v___x_1944_;
goto v___jp_1861_;
}
}
else
{
lean_dec(v_ref_1932_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v___y_1909_);
lean_dec(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1901_);
v___y_1862_ = v___y_1918_;
v___y_1863_ = v___x_1938_;
v___y_1864_ = v___y_1902_;
v___y_1865_ = v___y_1904_;
v___y_1866_ = v_a_1929_;
v___y_1867_ = v___y_1907_;
v___y_1868_ = v___x_1943_;
v___y_1869_ = v___y_1908_;
v___y_1870_ = v___y_1922_;
v___y_1871_ = v___y_1923_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1913_;
v___y_1874_ = v___x_1941_;
v___y_1875_ = v___y_1926_;
v___y_1876_ = v___y_1927_;
v___y_1877_ = v___x_1933_;
v___y_1878_ = v___x_1943_;
goto v___jp_1861_;
}
}
v___jp_1945_:
{
lean_object* v_options_1952_; lean_object* v_fileName_1953_; lean_object* v_fileMap_1954_; lean_object* v_currRecDepth_1955_; lean_object* v_maxRecDepth_1956_; lean_object* v_ref_1957_; lean_object* v_currNamespace_1958_; lean_object* v_openDecls_1959_; lean_object* v_initHeartbeats_1960_; lean_object* v_maxHeartbeats_1961_; lean_object* v_quotContext_1962_; lean_object* v_currMacroScope_1963_; uint8_t v_diag_1964_; lean_object* v_cancelTk_x3f_1965_; uint8_t v_suppressElabErrors_1966_; lean_object* v_inheritedTraceOptions_1967_; uint8_t v_hasTrace_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___y_1977_; 
v_options_1952_ = lean_ctor_get(v___y_1950_, 2);
v_fileName_1953_ = lean_ctor_get(v___y_1950_, 0);
v_fileMap_1954_ = lean_ctor_get(v___y_1950_, 1);
v_currRecDepth_1955_ = lean_ctor_get(v___y_1950_, 3);
v_maxRecDepth_1956_ = lean_ctor_get(v___y_1950_, 4);
v_ref_1957_ = lean_ctor_get(v___y_1950_, 5);
v_currNamespace_1958_ = lean_ctor_get(v___y_1950_, 6);
v_openDecls_1959_ = lean_ctor_get(v___y_1950_, 7);
v_initHeartbeats_1960_ = lean_ctor_get(v___y_1950_, 8);
v_maxHeartbeats_1961_ = lean_ctor_get(v___y_1950_, 9);
v_quotContext_1962_ = lean_ctor_get(v___y_1950_, 10);
v_currMacroScope_1963_ = lean_ctor_get(v___y_1950_, 11);
v_diag_1964_ = lean_ctor_get_uint8(v___y_1950_, sizeof(void*)*14);
v_cancelTk_x3f_1965_ = lean_ctor_get(v___y_1950_, 12);
v_suppressElabErrors_1966_ = lean_ctor_get_uint8(v___y_1950_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1967_ = lean_ctor_get(v___y_1950_, 13);
v_hasTrace_1968_ = lean_ctor_get_uint8(v_options_1952_, sizeof(void*)*1);
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1970_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1971_ = l_Lean_Level_getLevelOffset(v_lhs_1946_);
v___x_1972_ = l_Lean_Level_getLevelOffset(v_rhs_1947_);
v___x_1973_ = lean_level_eq(v___x_1971_, v___x_1972_);
lean_dec(v___x_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = 1;
v___x_1975_ = lean_box(v___x_1973_);
v___x_1976_ = lean_box(v___x_1974_);
lean_inc(v_rhs_1947_);
lean_inc(v_lhs_1946_);
v___y_1977_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1977_, 0, v___x_1975_);
lean_closure_set(v___y_1977_, 1, v_lhs_1946_);
lean_closure_set(v___y_1977_, 2, v_rhs_1947_);
lean_closure_set(v___y_1977_, 3, v___x_1969_);
lean_closure_set(v___y_1977_, 4, v___x_1970_);
lean_closure_set(v___y_1977_, 5, v___x_1976_);
if (v_hasTrace_1968_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref(v___y_1977_);
v___x_1978_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1973_, v_lhs_1946_, v_rhs_1947_, v___x_1969_, v___x_1970_, v___x_1974_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1979_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1980_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1981_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1982_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1967_, v_options_1952_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = l_Lean_trace_profiler;
v___x_1984_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_options_1952_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec_ref(v___y_1977_);
v___x_1985_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1973_, v_lhs_1946_, v_rhs_1947_, v___x_1969_, v___x_1970_, v___x_1974_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v___x_1985_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1967_);
lean_inc(v_cancelTk_x3f_1965_);
lean_inc(v_currMacroScope_1963_);
lean_inc(v_quotContext_1962_);
lean_inc(v_maxHeartbeats_1961_);
lean_inc(v_initHeartbeats_1960_);
lean_inc(v_openDecls_1959_);
lean_inc(v_currNamespace_1958_);
lean_inc(v_ref_1957_);
lean_inc(v_maxRecDepth_1956_);
lean_inc(v_currRecDepth_1955_);
lean_inc_ref(v_fileMap_1954_);
lean_inc_ref(v_fileName_1953_);
lean_inc_ref(v_options_1952_);
v___y_1901_ = v_inheritedTraceOptions_1967_;
v___y_1902_ = v___y_1949_;
v___y_1903_ = v_rhs_1947_;
v___y_1904_ = v___x_1979_;
v___y_1905_ = v_maxHeartbeats_1961_;
v___y_1906_ = v_openDecls_1959_;
v___y_1907_ = v___x_1974_;
v___y_1908_ = v_ref_1957_;
v___y_1909_ = v_currNamespace_1958_;
v___y_1910_ = v___y_1950_;
v___y_1911_ = v_currMacroScope_1963_;
v___y_1912_ = v_lhs_1946_;
v___y_1913_ = v___y_1951_;
v___y_1914_ = v_fileMap_1954_;
v___y_1915_ = v_cancelTk_x3f_1965_;
v___y_1916_ = v_maxRecDepth_1956_;
v___y_1917_ = v_diag_1964_;
v___y_1918_ = v___x_1982_;
v___y_1919_ = v_initHeartbeats_1960_;
v___y_1920_ = v_quotContext_1962_;
v___y_1921_ = v_fileName_1953_;
v___y_1922_ = v___y_1948_;
v___y_1923_ = v___x_1980_;
v___y_1924_ = v_currRecDepth_1955_;
v___y_1925_ = v_suppressElabErrors_1966_;
v___y_1926_ = v___y_1977_;
v___y_1927_ = v_options_1952_;
goto v___jp_1900_;
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1967_);
lean_inc(v_cancelTk_x3f_1965_);
lean_inc(v_currMacroScope_1963_);
lean_inc(v_quotContext_1962_);
lean_inc(v_maxHeartbeats_1961_);
lean_inc(v_initHeartbeats_1960_);
lean_inc(v_openDecls_1959_);
lean_inc(v_currNamespace_1958_);
lean_inc(v_ref_1957_);
lean_inc(v_maxRecDepth_1956_);
lean_inc(v_currRecDepth_1955_);
lean_inc_ref(v_fileMap_1954_);
lean_inc_ref(v_fileName_1953_);
lean_inc_ref(v_options_1952_);
v___y_1901_ = v_inheritedTraceOptions_1967_;
v___y_1902_ = v___y_1949_;
v___y_1903_ = v_rhs_1947_;
v___y_1904_ = v___x_1979_;
v___y_1905_ = v_maxHeartbeats_1961_;
v___y_1906_ = v_openDecls_1959_;
v___y_1907_ = v___x_1974_;
v___y_1908_ = v_ref_1957_;
v___y_1909_ = v_currNamespace_1958_;
v___y_1910_ = v___y_1950_;
v___y_1911_ = v_currMacroScope_1963_;
v___y_1912_ = v_lhs_1946_;
v___y_1913_ = v___y_1951_;
v___y_1914_ = v_fileMap_1954_;
v___y_1915_ = v_cancelTk_x3f_1965_;
v___y_1916_ = v_maxRecDepth_1956_;
v___y_1917_ = v_diag_1964_;
v___y_1918_ = v___x_1982_;
v___y_1919_ = v_initHeartbeats_1960_;
v___y_1920_ = v_quotContext_1962_;
v___y_1921_ = v_fileName_1953_;
v___y_1922_ = v___y_1948_;
v___y_1923_ = v___x_1980_;
v___y_1924_ = v_currRecDepth_1955_;
v___y_1925_ = v_suppressElabErrors_1966_;
v___y_1926_ = v___y_1977_;
v___y_1927_ = v_options_1952_;
goto v___jp_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = lean_is_level_def_eq(v_x_1989_, v_x_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_00_u03b1_1997_, lean_object* v_x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___redArg(v_x_1998_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_00_u03b1_2005_, v_x_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2070_ = 0;
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2072_ = l_Lean_registerTraceClass(v___x_2069_, v___x_2070_, v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; 
lean_dec_ref(v___x_2072_);
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2074_ = 1;
v___x_2075_ = l_Lean_registerTraceClass(v___x_2073_, v___x_2074_, v___x_2071_);
return v___x_2075_;
}
else
{
return v___x_2072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2077_;
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
