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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object* v_lvl_1_, lean_object* v_a_2_){
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
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_lvl_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
uint8_t v_res_10_;
v_res_10_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_1_, v_a_2_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object* v_lvl_11_, lean_object* v_a_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_11_, v_a_12_);
lean_dec(v_a_12_);
lean_dec(v_lvl_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object* v_lvl_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 2)
{
lean_object* v_a_17_; lean_object* v_a_18_; uint8_t v___x_19_; 
v_a_17_ = lean_ctor_get(v_x_16_, 0);
v_a_18_ = lean_ctor_get(v_x_16_, 1);
v___x_19_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_15_, v_a_17_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(v_lvl_15_, v_a_18_);
return v___x_20_;
}
else
{
return v___x_19_;
}
}
else
{
uint8_t v___x_21_; 
v___x_21_ = 0;
return v___x_21_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_lvl_15_ = stack[0].m_obj;
lean_object* v_x_16_ = stack[1].m_obj;
uint8_t v_res_22_;
v_res_22_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_lvl_15_, v_x_16_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object* v_lvl_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_lvl_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_lvl_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object* v_mvarId_27_, lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
switch(lean_obj_tag(v_x_28_))
{
case 2:
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_32_; 
v_a_30_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_30_);
v_a_31_ = lean_ctor_get(v_x_28_, 1);
lean_inc(v_a_31_);
lean_dec_ref_known(v_x_28_, 2);
v___x_32_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_27_, v_a_30_, v_x_29_);
v_x_28_ = v_a_31_;
v_x_29_ = v___x_32_;
goto _start;
}
case 5:
{
lean_object* v_a_34_; uint8_t v___x_35_; 
v_a_34_ = lean_ctor_get(v_x_28_, 0);
v___x_35_ = l_Lean_instBEqLevelMVarId_beq(v_a_34_, v_mvarId_27_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_mkLevelMax_x27(v_x_29_, v_x_28_);
return v___x_36_;
}
else
{
lean_dec_ref_known(v_x_28_, 1);
return v_x_29_;
}
}
default: 
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_mkLevelMax_x27(v_x_29_, v_x_28_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* v_mvarId_38_, lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_38_, v_x_39_, v_x_40_);
lean_dec(v_mvarId_38_);
return v_res_41_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_952__overap_50_; lean_object* v___x_51_; 
v___f_49_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_952__overap_50_ = lean_panic_fn_borrowed(v___f_49_, v_msg_43_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
v___x_51_ = lean_apply_5(v___x_952__overap_50_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, lean_box(0));
return v___x_51_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_43_ = stack[0].m_obj;
lean_object* v___y_44_ = stack[1].m_obj;
lean_object* v___y_45_ = stack[2].m_obj;
lean_object* v___y_46_ = stack[3].m_obj;
lean_object* v___y_47_ = stack[4].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(lean_object* v_msg_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v_msg_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_ks_64_; lean_object* v_vs_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_89_; 
v_ks_64_ = lean_ctor_get(v_x_60_, 0);
v_vs_65_ = lean_ctor_get(v_x_60_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_89_ == 0)
{
v___x_67_ = v_x_60_;
v_isShared_68_ = v_isSharedCheck_89_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_vs_65_);
lean_inc(v_ks_64_);
lean_dec(v_x_60_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_89_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_array_get_size(v_ks_64_);
v___x_70_ = lean_nat_dec_lt(v_x_61_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
lean_dec(v_x_61_);
v___x_71_ = lean_array_push(v_ks_64_, v_x_62_);
v___x_72_ = lean_array_push(v_vs_65_, v_x_63_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_72_);
lean_ctor_set(v___x_67_, 0, v___x_71_);
v___x_74_ = v___x_67_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v_k_x27_76_; uint8_t v___x_77_; 
v_k_x27_76_ = lean_array_fget_borrowed(v_ks_64_, v_x_61_);
v___x_77_ = l_Lean_instBEqLevelMVarId_beq(v_x_62_, v_k_x27_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_79_; 
if (v_isShared_68_ == 0)
{
v___x_79_ = v___x_67_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_ks_64_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_vs_65_);
v___x_79_ = v_reuseFailAlloc_83_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_add(v_x_61_, v___x_80_);
lean_dec(v_x_61_);
v_x_60_ = v___x_79_;
v_x_61_ = v___x_81_;
goto _start;
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = lean_array_fset(v_ks_64_, v_x_61_, v_x_62_);
v___x_85_ = lean_array_fset(v_vs_65_, v_x_61_, v_x_63_);
lean_dec(v_x_61_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_85_);
lean_ctor_set(v___x_67_, 0, v___x_84_);
v___x_87_ = v___x_67_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_n_90_, lean_object* v_k_91_, lean_object* v_v_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_n_90_, v___x_93_, v_k_91_, v_v_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_95_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(lean_object* v_x_96_, size_t v_x_97_, size_t v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v_es_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v_j_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_es_101_ = lean_ctor_get(v_x_96_, 0);
v___x_102_ = ((size_t)31ULL);
v___x_103_ = lean_usize_land(v_x_97_, v___x_102_);
v_j_104_ = lean_usize_to_nat(v___x_103_);
v___x_105_ = lean_array_get_size(v_es_101_);
v___x_106_ = lean_nat_dec_lt(v_j_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec(v_j_104_);
lean_dec(v_x_100_);
lean_dec(v_x_99_);
return v_x_96_;
}
else
{
lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_145_; 
lean_inc_ref(v_es_101_);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_x_96_, 0);
lean_dec(v_unused_146_);
v___x_108_ = v_x_96_;
v_isShared_109_ = v_isSharedCheck_145_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_x_96_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_145_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_v_110_; lean_object* v___x_111_; lean_object* v_xs_x27_112_; lean_object* v___y_114_; 
v_v_110_ = lean_array_fget(v_es_101_, v_j_104_);
v___x_111_ = lean_box(0);
v_xs_x27_112_ = lean_array_fset(v_es_101_, v_j_104_, v___x_111_);
switch(lean_obj_tag(v_v_110_))
{
case 0:
{
lean_object* v_key_119_; lean_object* v_val_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_key_119_ = lean_ctor_get(v_v_110_, 0);
v_val_120_ = lean_ctor_get(v_v_110_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_v_110_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_v_110_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_val_120_);
lean_inc(v_key_119_);
lean_dec(v_v_110_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint8_t v___x_124_; 
v___x_124_ = l_Lean_instBEqLevelMVarId_beq(v_x_99_, v_key_119_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_del_object(v___x_122_);
v___x_125_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_119_, v_val_120_, v_x_99_, v_x_100_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___y_114_ = v___x_126_;
goto v___jp_113_;
}
else
{
lean_object* v___x_128_; 
lean_dec(v_val_120_);
lean_dec(v_key_119_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_x_100_);
lean_ctor_set(v___x_122_, 0, v_x_99_);
v___x_128_ = v___x_122_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_x_99_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_x_100_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v___y_114_ = v___x_128_;
goto v___jp_113_;
}
}
}
}
case 1:
{
lean_object* v_node_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_143_; 
v_node_131_ = lean_ctor_get(v_v_110_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v_v_110_);
if (v_isSharedCheck_143_ == 0)
{
v___x_133_ = v_v_110_;
v_isShared_134_ = v_isSharedCheck_143_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_node_131_);
lean_dec(v_v_110_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_143_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_135_ = ((size_t)5ULL);
v___x_136_ = lean_usize_shift_right(v_x_97_, v___x_135_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_add(v_x_98_, v___x_137_);
v___x_139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_node_131_, v___x_136_, v___x_138_, v_x_99_, v_x_100_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_139_);
v___x_141_ = v___x_133_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
v___y_114_ = v___x_141_;
goto v___jp_113_;
}
}
}
default: 
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v_x_99_);
lean_ctor_set(v___x_144_, 1, v_x_100_);
v___y_114_ = v___x_144_;
goto v___jp_113_;
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_array_fset(v_xs_x27_112_, v_j_104_, v___y_114_);
lean_dec(v_j_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_115_);
v___x_117_ = v___x_108_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
else
{
lean_object* v_ks_147_; lean_object* v_vs_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_166_; 
v_ks_147_ = lean_ctor_get(v_x_96_, 0);
v_vs_148_ = lean_ctor_get(v_x_96_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_166_ == 0)
{
v___x_150_ = v_x_96_;
v_isShared_151_ = v_isSharedCheck_166_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_vs_148_);
lean_inc(v_ks_147_);
lean_dec(v_x_96_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_166_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_ks_147_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_vs_148_);
v___x_153_ = v_reuseFailAlloc_165_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v_newNode_154_; size_t v___x_155_; uint8_t v___x_156_; 
v_newNode_154_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v___x_153_, v_x_99_, v_x_100_);
v___x_155_ = ((size_t)7ULL);
v___x_156_ = lean_usize_dec_le(v___x_155_, v_x_98_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_154_);
v___x_158_ = lean_unsigned_to_nat(4u);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
if (v___x_159_ == 0)
{
lean_object* v_ks_160_; lean_object* v_vs_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_ks_160_ = lean_ctor_get(v_newNode_154_, 0);
lean_inc_ref(v_ks_160_);
v_vs_161_ = lean_ctor_get(v_newNode_154_, 1);
lean_inc_ref(v_vs_161_);
lean_dec_ref(v_newNode_154_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_x_98_, v_ks_160_, v_vs_161_, v___x_162_, v___x_163_);
lean_dec_ref(v_vs_161_);
lean_dec_ref(v_ks_160_);
return v___x_164_;
}
else
{
return v_newNode_154_;
}
}
else
{
return v_newNode_154_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_96_ = stack[0].m_obj;
size_t v_x_97_ = stack[1].m_num;
size_t v_x_98_ = stack[2].m_num;
lean_object* v_x_99_ = stack[3].m_obj;
lean_object* v_x_100_ = stack[4].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_96_, v_x_97_, v_x_98_, v_x_99_, v_x_100_);
stack->m_obj
 = v_res_167_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(size_t v_depth_168_, lean_object* v_keys_169_, lean_object* v_vals_170_, lean_object* v_i_171_, lean_object* v_entries_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_array_get_size(v_keys_169_);
v___x_174_ = lean_nat_dec_lt(v_i_171_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v_i_171_);
return v_entries_172_;
}
else
{
lean_object* v_k_175_; lean_object* v_v_176_; uint64_t v___x_177_; size_t v_h_178_; size_t v___x_179_; lean_object* v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v_h_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_k_175_ = lean_array_fget_borrowed(v_keys_169_, v_i_171_);
v_v_176_ = lean_array_fget_borrowed(v_vals_170_, v_i_171_);
v___x_177_ = l_Lean_instHashableLevelMVarId_hash(v_k_175_);
v_h_178_ = lean_uint64_to_usize(v___x_177_);
v___x_179_ = ((size_t)5ULL);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = ((size_t)1ULL);
v___x_182_ = lean_usize_sub(v_depth_168_, v___x_181_);
v___x_183_ = lean_usize_mul(v___x_179_, v___x_182_);
v_h_184_ = lean_usize_shift_right(v_h_178_, v___x_183_);
v___x_185_ = lean_nat_add(v_i_171_, v___x_180_);
lean_dec(v_i_171_);
lean_inc(v_v_176_);
lean_inc(v_k_175_);
v___x_186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_entries_172_, v_h_184_, v_depth_168_, v_k_175_, v_v_176_);
v_i_171_ = v___x_185_;
v_entries_172_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_168_ = stack[0].m_num;
lean_object* v_keys_169_ = stack[1].m_obj;
lean_object* v_vals_170_ = stack[2].m_obj;
lean_object* v_i_171_ = stack[3].m_obj;
lean_object* v_entries_172_ = stack[4].m_obj;
lean_object* v_res_188_;
v_res_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_168_, v_keys_169_, v_vals_170_, v_i_171_, v_entries_172_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_189_, lean_object* v_keys_190_, lean_object* v_vals_191_, lean_object* v_i_192_, lean_object* v_entries_193_){
_start:
{
size_t v_depth_boxed_194_; lean_object* v_res_195_; 
v_depth_boxed_194_ = lean_unbox_usize(v_depth_189_);
lean_dec(v_depth_189_);
v_res_195_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_boxed_194_, v_keys_190_, v_vals_191_, v_i_192_, v_entries_193_);
lean_dec_ref(v_vals_191_);
lean_dec_ref(v_keys_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
size_t v_x_2745__boxed_201_; size_t v_x_2746__boxed_202_; lean_object* v_res_203_; 
v_x_2745__boxed_201_ = lean_unbox_usize(v_x_197_);
lean_dec(v_x_197_);
v_x_2746__boxed_202_ = lean_unbox_usize(v_x_198_);
lean_dec(v_x_198_);
v_res_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_196_, v_x_2745__boxed_201_, v_x_2746__boxed_202_, v_x_199_, v_x_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
uint64_t v___x_207_; size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; 
v___x_207_ = l_Lean_instHashableLevelMVarId_hash(v_x_205_);
v___x_208_ = lean_uint64_to_usize(v___x_207_);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_204_, v___x_208_, v___x_209_, v_x_205_, v_x_206_);
return v___x_210_;
}
}
lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object* v_mvarId_211_, lean_object* v_val_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; lean_object* v_mctx_216_; lean_object* v_cache_217_; lean_object* v_zetaDeltaFVarIds_218_; lean_object* v_postponed_219_; lean_object* v_diag_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_250_; 
v___x_215_ = lean_st_ref_take(v___y_213_);
v_mctx_216_ = lean_ctor_get(v___x_215_, 0);
v_cache_217_ = lean_ctor_get(v___x_215_, 1);
v_zetaDeltaFVarIds_218_ = lean_ctor_get(v___x_215_, 2);
v_postponed_219_ = lean_ctor_get(v___x_215_, 3);
v_diag_220_ = lean_ctor_get(v___x_215_, 4);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_250_ == 0)
{
v___x_222_ = v___x_215_;
v_isShared_223_ = v_isSharedCheck_250_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_diag_220_);
lean_inc(v_postponed_219_);
lean_inc(v_zetaDeltaFVarIds_218_);
lean_inc(v_cache_217_);
lean_inc(v_mctx_216_);
lean_dec(v___x_215_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_250_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_depth_224_; lean_object* v_levelAssignDepth_225_; lean_object* v_lmvarCounter_226_; lean_object* v_mvarCounter_227_; lean_object* v_lDecls_228_; lean_object* v_decls_229_; lean_object* v_userNames_230_; lean_object* v_lAssignment_231_; lean_object* v_eAssignment_232_; lean_object* v_dAssignment_233_; lean_object* v_instanceTypedMVars_234_; lean_object* v_synthNormMemo_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_249_; 
v_depth_224_ = lean_ctor_get(v_mctx_216_, 0);
v_levelAssignDepth_225_ = lean_ctor_get(v_mctx_216_, 1);
v_lmvarCounter_226_ = lean_ctor_get(v_mctx_216_, 2);
v_mvarCounter_227_ = lean_ctor_get(v_mctx_216_, 3);
v_lDecls_228_ = lean_ctor_get(v_mctx_216_, 4);
v_decls_229_ = lean_ctor_get(v_mctx_216_, 5);
v_userNames_230_ = lean_ctor_get(v_mctx_216_, 6);
v_lAssignment_231_ = lean_ctor_get(v_mctx_216_, 7);
v_eAssignment_232_ = lean_ctor_get(v_mctx_216_, 8);
v_dAssignment_233_ = lean_ctor_get(v_mctx_216_, 9);
v_instanceTypedMVars_234_ = lean_ctor_get(v_mctx_216_, 10);
v_synthNormMemo_235_ = lean_ctor_get(v_mctx_216_, 11);
v_isSharedCheck_249_ = !lean_is_exclusive(v_mctx_216_);
if (v_isSharedCheck_249_ == 0)
{
v___x_237_ = v_mctx_216_;
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_synthNormMemo_235_);
lean_inc(v_instanceTypedMVars_234_);
lean_inc(v_dAssignment_233_);
lean_inc(v_eAssignment_232_);
lean_inc(v_lAssignment_231_);
lean_inc(v_userNames_230_);
lean_inc(v_decls_229_);
lean_inc(v_lDecls_228_);
lean_inc(v_mvarCounter_227_);
lean_inc(v_lmvarCounter_226_);
lean_inc(v_levelAssignDepth_225_);
lean_inc(v_depth_224_);
lean_dec(v_mctx_216_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = lean_box(0);
v___x_240_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_231_, v_mvarId_211_, v_val_212_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 7, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_depth_224_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_levelAssignDepth_225_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_lmvarCounter_226_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_mvarCounter_227_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_lDecls_228_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_decls_229_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_userNames_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_eAssignment_232_);
lean_ctor_set(v_reuseFailAlloc_248_, 9, v_dAssignment_233_);
lean_ctor_set(v_reuseFailAlloc_248_, 10, v_instanceTypedMVars_234_);
lean_ctor_set(v_reuseFailAlloc_248_, 11, v_synthNormMemo_235_);
v___x_242_ = v_reuseFailAlloc_248_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_242_);
v___x_244_ = v___x_222_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_cache_217_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_zetaDeltaFVarIds_218_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v_postponed_219_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v_diag_220_);
v___x_244_ = v_reuseFailAlloc_247_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_st_ref_put(v___y_213_, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_239_);
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_211_ = stack[0].m_obj;
lean_object* v_val_212_ = stack[1].m_obj;
lean_object* v___y_213_ = stack[2].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_211_, v_val_212_, v___y_213_);
stack->m_obj
 = v_res_251_;
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object* v_msgData_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; lean_object* v_env_264_; uint8_t v___x_265_; lean_object* v_env_266_; lean_object* v___x_267_; lean_object* v_toCold_268_; lean_object* v_mctx_269_; lean_object* v_lctx_270_; lean_object* v_options_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_263_ = lean_st_ref_get(v___y_261_);
v_env_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_ref(v_env_264_);
lean_dec(v___x_263_);
v___x_265_ = 0;
v_env_266_ = l_Lean_Environment_setRecordingDeps(v_env_264_, v___x_265_);
v___x_267_ = lean_st_ref_get(v___y_259_);
v_toCold_268_ = lean_ctor_get(v___y_260_, 0);
v_mctx_269_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_mctx_269_);
lean_dec(v___x_267_);
v_lctx_270_ = lean_ctor_get(v___y_258_, 2);
v_options_271_ = lean_ctor_get(v_toCold_268_, 2);
lean_inc_ref(v_options_271_);
lean_inc_ref(v_lctx_270_);
v___x_272_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_272_, 0, v_env_266_);
lean_ctor_set(v___x_272_, 1, v_mctx_269_);
lean_ctor_set(v___x_272_, 2, v_lctx_270_);
lean_ctor_set(v___x_272_, 3, v_options_271_);
v___x_273_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_msgData_257_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_257_ = stack[0].m_obj;
lean_object* v___y_258_ = stack[1].m_obj;
lean_object* v___y_259_ = stack[2].m_obj;
lean_object* v___y_260_ = stack[3].m_obj;
lean_object* v___y_261_ = stack[4].m_obj;
lean_object* v_res_275_;
v_res_275_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_282_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_283_; double v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_float_of_nat(v___x_283_);
return v___x_284_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_288_, lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_342_; 
v_ref_295_ = lean_ctor_get(v___y_292_, 2);
v___x_296_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_342_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_342_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_342_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v_traceState_302_; lean_object* v_env_303_; lean_object* v_nextMacroScope_304_; lean_object* v_ngen_305_; lean_object* v_auxDeclNGen_306_; lean_object* v_cache_307_; lean_object* v_recordedDeps_308_; lean_object* v_messages_309_; lean_object* v_infoState_310_; lean_object* v_snapshotTasks_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_341_; 
v___x_301_ = lean_st_ref_take(v___y_293_);
v_traceState_302_ = lean_ctor_get(v___x_301_, 4);
v_env_303_ = lean_ctor_get(v___x_301_, 0);
v_nextMacroScope_304_ = lean_ctor_get(v___x_301_, 1);
v_ngen_305_ = lean_ctor_get(v___x_301_, 2);
v_auxDeclNGen_306_ = lean_ctor_get(v___x_301_, 3);
v_cache_307_ = lean_ctor_get(v___x_301_, 5);
v_recordedDeps_308_ = lean_ctor_get(v___x_301_, 6);
v_messages_309_ = lean_ctor_get(v___x_301_, 7);
v_infoState_310_ = lean_ctor_get(v___x_301_, 8);
v_snapshotTasks_311_ = lean_ctor_get(v___x_301_, 9);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_341_ == 0)
{
v___x_313_ = v___x_301_;
v_isShared_314_ = v_isSharedCheck_341_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snapshotTasks_311_);
lean_inc(v_infoState_310_);
lean_inc(v_messages_309_);
lean_inc(v_recordedDeps_308_);
lean_inc(v_cache_307_);
lean_inc(v_traceState_302_);
lean_inc(v_auxDeclNGen_306_);
lean_inc(v_ngen_305_);
lean_inc(v_nextMacroScope_304_);
lean_inc(v_env_303_);
lean_dec(v___x_301_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_341_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint64_t v_tid_315_; lean_object* v_traces_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_340_; 
v_tid_315_ = lean_ctor_get_uint64(v_traceState_302_, sizeof(void*)*1);
v_traces_316_ = lean_ctor_get(v_traceState_302_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_traceState_302_);
if (v_isSharedCheck_340_ == 0)
{
v___x_318_ = v_traceState_302_;
v_isShared_319_ = v_isSharedCheck_340_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_traces_316_);
lean_dec(v_traceState_302_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_340_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; double v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_320_ = lean_box(0);
v___x_321_ = lean_box(0);
v___x_322_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_323_ = 0;
v___x_324_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_325_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_325_, 0, v_cls_288_);
lean_ctor_set(v___x_325_, 1, v___x_321_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_ctor_set_float(v___x_325_, sizeof(void*)*3, v___x_322_);
lean_ctor_set_float(v___x_325_, sizeof(void*)*3 + 8, v___x_322_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*3 + 16, v___x_323_);
v___x_326_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_327_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v_a_297_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
lean_inc(v_ref_295_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_ref_295_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_PersistentArray_push___redArg(v_traces_316_, v___x_328_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_329_);
v___x_331_ = v___x_318_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_329_);
lean_ctor_set_uint64(v_reuseFailAlloc_339_, sizeof(void*)*1, v_tid_315_);
v___x_331_ = v_reuseFailAlloc_339_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_331_);
v___x_333_ = v___x_313_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_env_303_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_nextMacroScope_304_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_ngen_305_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_auxDeclNGen_306_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v_cache_307_);
lean_ctor_set(v_reuseFailAlloc_338_, 6, v_recordedDeps_308_);
lean_ctor_set(v_reuseFailAlloc_338_, 7, v_messages_309_);
lean_ctor_set(v_reuseFailAlloc_338_, 8, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_338_, 9, v_snapshotTasks_311_);
v___x_333_ = v_reuseFailAlloc_338_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_st_ref_put(v___y_293_, v___x_333_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_320_);
v___x_336_ = v___x_299_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_320_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_288_ = stack[0].m_obj;
lean_object* v_msg_289_ = stack[1].m_obj;
lean_object* v___y_290_ = stack[2].m_obj;
lean_object* v___y_291_ = stack[3].m_obj;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v___y_293_ = stack[5].m_obj;
lean_object* v_res_343_;
v_res_343_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_288_, v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_344_, v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_356_ = lean_unsigned_to_nat(2u);
v___x_357_ = lean_unsigned_to_nat(39u);
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_360_ = l_mkPanicMessageWithDecl(v___x_359_, v___x_358_, v___x_357_, v___x_356_, v___x_355_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_373_ = l_Lean_Name_append(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_380_, lean_object* v_v_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_Level_isMax(v_v_381_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_v_381_);
lean_dec(v_mvarId_380_);
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_389_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_388_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_mkFreshLevelMVar(v_a_382_, v_a_383_, v_a_384_, v_a_385_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_toCold_391_; lean_object* v_options_392_; lean_object* v_a_393_; lean_object* v_inheritedTraceOptions_394_; uint8_t v_hasTrace_395_; lean_object* v___x_396_; 
v_toCold_391_ = lean_ctor_get(v_a_384_, 0);
v_options_392_ = lean_ctor_get(v_toCold_391_, 2);
v_a_393_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_390_, 1);
v_inheritedTraceOptions_394_ = lean_ctor_get(v_toCold_391_, 11);
v_hasTrace_395_ = lean_ctor_get_uint8(v_options_392_, sizeof(void*)*1);
v___x_396_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_380_, v_v_381_, v_a_393_);
if (v_hasTrace_395_ == 0)
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_380_, v___x_396_, v_a_383_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_399_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_400_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_394_, v_options_392_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_380_, v___x_396_, v_a_383_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_402_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_380_);
v___x_403_ = l_Lean_mkLevelMVar(v_mvarId_380_);
v___x_404_ = l_Lean_MessageData_ofLevel(v___x_403_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_inc(v___x_396_);
v___x_408_ = l_Lean_MessageData_ofLevel(v___x_396_);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_398_, v___x_409_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; 
lean_dec_ref_known(v___x_410_, 1);
v___x_411_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_380_, v___x_396_, v_a_383_);
return v___x_411_;
}
else
{
lean_dec(v___x_396_);
lean_dec(v_mvarId_380_);
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_v_381_);
lean_dec(v_mvarId_380_);
v_a_412_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_390_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_390_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_380_ = stack[0].m_obj;
lean_object* v_v_381_ = stack[1].m_obj;
lean_object* v_a_382_ = stack[2].m_obj;
lean_object* v_a_383_ = stack[3].m_obj;
lean_object* v_a_384_ = stack[4].m_obj;
lean_object* v_a_385_ = stack[5].m_obj;
lean_object* v_res_420_;
v_res_420_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_380_, v_v_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_421_, lean_object* v_v_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_421_, v_v_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_428_;
}
}
lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_429_, lean_object* v_val_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_429_, v_val_430_, v___y_432_);
return v___x_436_;
}
}
LEAN_EXPORT void l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_429_ = stack[0].m_obj;
lean_object* v_val_430_ = stack[1].m_obj;
lean_object* v___y_431_ = stack[2].m_obj;
lean_object* v___y_432_ = stack[3].m_obj;
lean_object* v___y_433_ = stack[4].m_obj;
lean_object* v___y_434_ = stack[5].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_429_, v_val_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_438_, lean_object* v_val_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_438_, v_val_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_447_, v_x_448_, v_x_449_);
return v___x_450_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_451_, lean_object* v_x_452_, size_t v_x_453_, size_t v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_452_, v_x_453_, v_x_454_, v_x_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_452_ = stack[1].m_obj;
size_t v_x_453_ = stack[2].m_num;
size_t v_x_454_ = stack[3].m_num;
lean_object* v_x_455_ = stack[4].m_obj;
lean_object* v_x_456_ = stack[5].m_obj;
lean_object* v_res_458_;
v_res_458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_box(0), v_x_452_, v_x_453_, v_x_454_, v_x_455_, v_x_456_);
stack->m_obj
 = v_res_458_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
size_t v_x_3509__boxed_465_; size_t v_x_3510__boxed_466_; lean_object* v_res_467_; 
v_x_3509__boxed_465_ = lean_unbox_usize(v_x_461_);
lean_dec(v_x_461_);
v_x_3510__boxed_466_ = lean_unbox_usize(v_x_462_);
lean_dec(v_x_462_);
v_res_467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_459_, v_x_460_, v_x_3509__boxed_465_, v_x_3510__boxed_466_, v_x_463_, v_x_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_468_, lean_object* v_n_469_, lean_object* v_k_470_, lean_object* v_v_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_469_, v_k_470_, v_v_471_);
return v___x_472_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_473_, size_t v_depth_474_, lean_object* v_keys_475_, lean_object* v_vals_476_, lean_object* v_heq_477_, lean_object* v_i_478_, lean_object* v_entries_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_474_, v_keys_475_, v_vals_476_, v_i_478_, v_entries_479_);
return v___x_480_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_474_ = stack[1].m_num;
lean_object* v_keys_475_ = stack[2].m_obj;
lean_object* v_vals_476_ = stack[3].m_obj;
lean_object* v_i_478_ = stack[5].m_obj;
lean_object* v_entries_479_ = stack[6].m_obj;
lean_object* v_res_481_;
v_res_481_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_box(0), v_depth_474_, v_keys_475_, v_vals_476_, lean_box(0), v_i_478_, v_entries_479_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_482_, lean_object* v_depth_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_heq_486_, lean_object* v_i_487_, lean_object* v_entries_488_){
_start:
{
size_t v_depth_boxed_489_; lean_object* v_res_490_; 
v_depth_boxed_489_ = lean_unbox_usize(v_depth_483_);
lean_dec(v_depth_483_);
v_res_490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_482_, v_depth_boxed_489_, v_keys_484_, v_vals_485_, v_heq_486_, v_i_487_, v_entries_488_);
lean_dec_ref(v_vals_485_);
lean_dec_ref(v_keys_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_492_, v_x_493_, v_x_494_, v_x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_500_, lean_object* v_v_x27_501_, lean_object* v_mvarId_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
uint8_t v___x_508_; lean_object* v___y_510_; 
v___x_508_ = lean_level_eq(v_u_500_, v_v_x27_501_);
if (v___x_508_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_mvarId_502_);
lean_dec(v_u_500_);
v___x_521_ = lean_box(v___x_508_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_toCold_523_; lean_object* v_options_524_; uint8_t v_hasTrace_525_; 
v_toCold_523_ = lean_ctor_get(v_a_505_, 0);
v_options_524_ = lean_ctor_get(v_toCold_523_, 2);
v_hasTrace_525_ = lean_ctor_get_uint8(v_options_524_, sizeof(void*)*1);
if (v_hasTrace_525_ == 0)
{
v___y_510_ = v_a_504_;
goto v___jp_509_;
}
else
{
lean_object* v_inheritedTraceOptions_526_; lean_object* v_cls_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_inheritedTraceOptions_526_ = lean_ctor_get(v_toCold_523_, 11);
v_cls_527_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_526_, v_options_524_, v___x_528_);
if (v___x_529_ == 0)
{
v___y_510_ = v_a_504_;
goto v___jp_509_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_502_);
v___x_531_ = l_Lean_mkLevelMVar(v_mvarId_502_);
v___x_532_ = l_Lean_MessageData_ofLevel(v___x_531_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc(v_u_500_);
v___x_536_ = l_Lean_MessageData_ofLevel(v_u_500_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_527_, v___x_537_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_dec_ref_known(v___x_538_, 1);
v___y_510_ = v_a_504_;
goto v___jp_509_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_mvarId_502_);
lean_dec(v_u_500_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v___x_511_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_502_, v_u_500_, v___y_510_);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v___x_511_, 0);
lean_dec(v_unused_520_);
v___x_513_ = v___x_511_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_dec(v___x_511_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_box(v___x_508_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_500_ = stack[0].m_obj;
lean_object* v_v_x27_501_ = stack[1].m_obj;
lean_object* v_mvarId_502_ = stack[2].m_obj;
lean_object* v_a_503_ = stack[3].m_obj;
lean_object* v_a_504_ = stack[4].m_obj;
lean_object* v_a_505_ = stack[5].m_obj;
lean_object* v_a_506_ = stack[6].m_obj;
lean_object* v_res_547_;
v_res_547_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_500_, v_v_x27_501_, v_mvarId_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_548_, lean_object* v_v_x27_549_, lean_object* v_mvarId_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_548_, v_v_x27_549_, v_mvarId_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_v_x27_549_);
return v_res_556_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_557_, lean_object* v_v_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
if (lean_obj_tag(v_v_558_) == 2)
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v_v_558_, 1);
lean_inc(v_a_568_);
if (lean_obj_tag(v_a_568_) == 5)
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_569_ = lean_ctor_get(v_v_558_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v_v_558_, 2);
v_a_570_ = lean_ctor_get(v_a_568_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v_a_568_, 1);
v___x_571_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_557_, v_a_569_, v_a_570_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_569_);
return v___x_571_;
}
else
{
lean_object* v_a_572_; 
v_a_572_ = lean_ctor_get(v_v_558_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v_v_558_, 2);
if (lean_obj_tag(v_a_572_) == 5)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v_a_572_, 1);
v___x_574_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_557_, v_a_568_, v_a_573_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_568_);
return v___x_574_;
}
else
{
lean_dec(v_a_572_);
lean_dec(v_a_568_);
lean_dec(v_u_557_);
goto v___jp_564_;
}
}
}
else
{
lean_dec(v_v_558_);
lean_dec(v_u_557_);
goto v___jp_564_;
}
v___jp_564_:
{
uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = 0;
v___x_566_ = lean_box(v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_557_ = stack[0].m_obj;
lean_object* v_v_558_ = stack[1].m_obj;
lean_object* v_a_559_ = stack[2].m_obj;
lean_object* v_a_560_ = stack[3].m_obj;
lean_object* v_a_561_ = stack[4].m_obj;
lean_object* v_a_562_ = stack[5].m_obj;
lean_object* v_res_575_;
v_res_575_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_557_, v_v_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_576_, lean_object* v_v_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_576_, v_v_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_587_, lean_object* v_u_u2082_588_, lean_object* v_v_x27_589_, lean_object* v_mvarId_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
uint8_t v___x_596_; uint8_t v___x_597_; lean_object* v___y_599_; lean_object* v___y_611_; 
v___x_596_ = lean_level_eq(v_u_u2081_587_, v_v_x27_589_);
v___x_597_ = 1;
if (v___x_596_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = lean_level_eq(v_u_u2082_588_, v_v_x27_589_);
lean_dec(v_u_u2082_588_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec(v_mvarId_590_);
lean_dec(v_u_u2081_587_);
v___x_623_ = lean_box(v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
else
{
lean_object* v_toCold_625_; lean_object* v_options_626_; uint8_t v_hasTrace_627_; 
v_toCold_625_ = lean_ctor_get(v_a_593_, 0);
v_options_626_ = lean_ctor_get(v_toCold_625_, 2);
v_hasTrace_627_ = lean_ctor_get_uint8(v_options_626_, sizeof(void*)*1);
if (v_hasTrace_627_ == 0)
{
v___y_611_ = v_a_592_;
goto v___jp_610_;
}
else
{
lean_object* v_inheritedTraceOptions_628_; lean_object* v_cls_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_inheritedTraceOptions_628_ = lean_ctor_get(v_toCold_625_, 11);
v_cls_629_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_630_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_628_, v_options_626_, v___x_630_);
if (v___x_631_ == 0)
{
v___y_611_ = v_a_592_;
goto v___jp_610_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_632_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_590_);
v___x_633_ = l_Lean_mkLevelMVar(v_mvarId_590_);
v___x_634_ = l_Lean_MessageData_ofLevel(v___x_633_);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_632_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
lean_inc(v_u_u2081_587_);
v___x_638_ = l_Lean_MessageData_ofLevel(v_u_u2081_587_);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_629_, v___x_639_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref_known(v___x_640_, 1);
v___y_611_ = v_a_592_;
goto v___jp_610_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_mvarId_590_);
lean_dec(v_u_u2081_587_);
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_649_; lean_object* v_options_650_; uint8_t v_hasTrace_651_; 
lean_dec(v_u_u2081_587_);
v_toCold_649_ = lean_ctor_get(v_a_593_, 0);
v_options_650_ = lean_ctor_get(v_toCold_649_, 2);
v_hasTrace_651_ = lean_ctor_get_uint8(v_options_650_, sizeof(void*)*1);
if (v_hasTrace_651_ == 0)
{
v___y_599_ = v_a_592_;
goto v___jp_598_;
}
else
{
lean_object* v_inheritedTraceOptions_652_; lean_object* v_cls_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_inheritedTraceOptions_652_ = lean_ctor_get(v_toCold_649_, 11);
v_cls_653_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_654_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_652_, v_options_650_, v___x_654_);
if (v___x_655_ == 0)
{
v___y_599_ = v_a_592_;
goto v___jp_598_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_656_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_590_);
v___x_657_ = l_Lean_mkLevelMVar(v_mvarId_590_);
v___x_658_ = l_Lean_MessageData_ofLevel(v___x_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_656_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc(v_u_u2082_588_);
v___x_662_ = l_Lean_MessageData_ofLevel(v_u_u2082_588_);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_653_, v___x_663_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_dec_ref_known(v___x_664_, 1);
v___y_599_ = v_a_592_;
goto v___jp_598_;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_mvarId_590_);
lean_dec(v_u_u2082_588_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v___x_600_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_590_, v_u_u2082_588_, v___y_599_);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_609_);
v___x_602_ = v___x_600_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_dec(v___x_600_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_box(v___x_597_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
v___jp_610_:
{
lean_object* v___x_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v___x_612_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_590_, v_u_u2081_587_, v___y_611_);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_612_, 0);
lean_dec(v_unused_621_);
v___x_614_ = v___x_612_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_dec(v___x_612_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_box(v___x_597_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_u2081_587_ = stack[0].m_obj;
lean_object* v_u_u2082_588_ = stack[1].m_obj;
lean_object* v_v_x27_589_ = stack[2].m_obj;
lean_object* v_mvarId_590_ = stack[3].m_obj;
lean_object* v_a_591_ = stack[4].m_obj;
lean_object* v_a_592_ = stack[5].m_obj;
lean_object* v_a_593_ = stack[6].m_obj;
lean_object* v_a_594_ = stack[7].m_obj;
lean_object* v_res_673_;
v_res_673_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_587_, v_u_u2082_588_, v_v_x27_589_, v_mvarId_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_674_, lean_object* v_u_u2082_675_, lean_object* v_v_x27_676_, lean_object* v_mvarId_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_674_, v_u_u2082_675_, v_v_x27_676_, v_mvarId_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_v_x27_676_);
return v_res_683_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_684_, lean_object* v_v_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
if (lean_obj_tag(v_u_684_) == 2)
{
if (lean_obj_tag(v_v_685_) == 2)
{
lean_object* v_a_695_; 
v_a_695_ = lean_ctor_get(v_v_685_, 1);
lean_inc(v_a_695_);
if (lean_obj_tag(v_a_695_) == 5)
{
lean_object* v_a_696_; lean_object* v_a_697_; lean_object* v_a_698_; lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_696_ = lean_ctor_get(v_u_684_, 0);
lean_inc(v_a_696_);
v_a_697_ = lean_ctor_get(v_u_684_, 1);
lean_inc(v_a_697_);
lean_dec_ref_known(v_u_684_, 2);
v_a_698_ = lean_ctor_get(v_v_685_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v_v_685_, 2);
v_a_699_ = lean_ctor_get(v_a_695_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v_a_695_, 1);
v___x_700_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_698_);
return v___x_700_;
}
else
{
lean_object* v_a_701_; 
v_a_701_ = lean_ctor_get(v_v_685_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v_v_685_, 2);
if (lean_obj_tag(v_a_701_) == 5)
{
lean_object* v_a_702_; lean_object* v_a_703_; lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_702_ = lean_ctor_get(v_u_684_, 0);
lean_inc(v_a_702_);
v_a_703_ = lean_ctor_get(v_u_684_, 1);
lean_inc(v_a_703_);
lean_dec_ref_known(v_u_684_, 2);
v_a_704_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v_a_701_, 1);
v___x_705_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_702_, v_a_703_, v_a_695_, v_a_704_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_695_);
return v___x_705_;
}
else
{
lean_dec(v_a_701_);
lean_dec(v_a_695_);
lean_dec_ref_known(v_u_684_, 2);
goto v___jp_691_;
}
}
}
else
{
lean_dec_ref_known(v_u_684_, 2);
lean_dec(v_v_685_);
goto v___jp_691_;
}
}
else
{
lean_dec(v_v_685_);
lean_dec(v_u_684_);
goto v___jp_691_;
}
v___jp_691_:
{
uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = 0;
v___x_693_ = lean_box(v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_684_ = stack[0].m_obj;
lean_object* v_v_685_ = stack[1].m_obj;
lean_object* v_a_686_ = stack[2].m_obj;
lean_object* v_a_687_ = stack[3].m_obj;
lean_object* v_a_688_ = stack[4].m_obj;
lean_object* v_a_689_ = stack[5].m_obj;
lean_object* v_res_706_;
v_res_706_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_684_, v_v_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_707_, lean_object* v_v_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_707_, v_v_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_714_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_722_ = l_Lean_Name_append(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_726_, lean_object* v_rhs_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_toCold_733_; lean_object* v_ref_734_; lean_object* v___y_736_; lean_object* v_options_756_; uint8_t v_hasTrace_757_; 
v_toCold_733_ = lean_ctor_get(v_a_730_, 0);
v_ref_734_ = lean_ctor_get(v_a_730_, 2);
v_options_756_ = lean_ctor_get(v_toCold_733_, 2);
v_hasTrace_757_ = lean_ctor_get_uint8(v_options_756_, sizeof(void*)*1);
if (v_hasTrace_757_ == 0)
{
v___y_736_ = v_a_729_;
goto v___jp_735_;
}
else
{
lean_object* v_inheritedTraceOptions_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_inheritedTraceOptions_758_ = lean_ctor_get(v_toCold_733_, 11);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_760_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_761_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_758_, v_options_756_, v___x_760_);
if (v___x_761_ == 0)
{
v___y_736_ = v_a_729_;
goto v___jp_735_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_inc(v_lhs_726_);
v___x_762_ = l_Lean_MessageData_ofLevel(v_lhs_726_);
v___x_763_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_inc(v_rhs_727_);
v___x_765_ = l_Lean_MessageData_ofLevel(v_rhs_727_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_759_, v___x_766_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_dec_ref_known(v___x_767_, 1);
v___y_736_ = v_a_729_;
goto v___jp_735_;
}
else
{
lean_dec(v_rhs_727_);
lean_dec(v_lhs_726_);
return v___x_767_;
}
}
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v_mctx_738_; lean_object* v_cache_739_; lean_object* v_zetaDeltaFVarIds_740_; lean_object* v_postponed_741_; lean_object* v_diag_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_755_; 
v___x_737_ = lean_st_ref_take(v___y_736_);
v_mctx_738_ = lean_ctor_get(v___x_737_, 0);
v_cache_739_ = lean_ctor_get(v___x_737_, 1);
v_zetaDeltaFVarIds_740_ = lean_ctor_get(v___x_737_, 2);
v_postponed_741_ = lean_ctor_get(v___x_737_, 3);
v_diag_742_ = lean_ctor_get(v___x_737_, 4);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_755_ == 0)
{
v___x_744_ = v___x_737_;
v_isShared_745_ = v_isSharedCheck_755_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_diag_742_);
lean_inc(v_postponed_741_);
lean_inc(v_zetaDeltaFVarIds_740_);
lean_inc(v_cache_739_);
lean_inc(v_mctx_738_);
lean_dec(v___x_737_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_755_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_defEqCtx_x3f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v_defEqCtx_x3f_746_ = lean_ctor_get(v_a_728_, 4);
v___x_747_ = lean_box(0);
lean_inc(v_defEqCtx_x3f_746_);
lean_inc(v_ref_734_);
v___x_748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_748_, 0, v_ref_734_);
lean_ctor_set(v___x_748_, 1, v_lhs_726_);
lean_ctor_set(v___x_748_, 2, v_rhs_727_);
lean_ctor_set(v___x_748_, 3, v_defEqCtx_x3f_746_);
v___x_749_ = l_Lean_PersistentArray_push___redArg(v_postponed_741_, v___x_748_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 3, v___x_749_);
v___x_751_ = v___x_744_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_mctx_738_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_cache_739_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_zetaDeltaFVarIds_740_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_diag_742_);
v___x_751_ = v_reuseFailAlloc_754_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_st_ref_put(v___y_736_, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_747_);
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_726_ = stack[0].m_obj;
lean_object* v_rhs_727_ = stack[1].m_obj;
lean_object* v_a_728_ = stack[2].m_obj;
lean_object* v_a_729_ = stack[3].m_obj;
lean_object* v_a_730_ = stack[4].m_obj;
lean_object* v_a_731_ = stack[5].m_obj;
lean_object* v_res_768_;
v_res_768_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_726_, v_rhs_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_769_, lean_object* v_rhs_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_769_, v_rhs_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
return v_res_776_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_777_, lean_object* v_mvarId_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
if (lean_obj_tag(v_v_777_) == 5)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v_v_777_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v_v_777_, 1);
v___x_785_ = l_Lean_LMVarId_getLevel(v_a_784_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_LMVarId_getLevel(v_mvarId_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_797_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_797_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_797_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_797_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = lean_nat_dec_lt(v_a_788_, v_a_786_);
lean_dec(v_a_786_);
lean_dec(v_a_788_);
v___x_793_ = lean_box(v___x_792_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_a_786_);
v_a_798_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_787_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_787_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_mvarId_778_);
v_a_806_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_785_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_785_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v_mvarId_778_);
lean_dec(v_v_777_);
v___x_814_ = 0;
v___x_815_ = lean_box(v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_777_ = stack[0].m_obj;
lean_object* v_mvarId_778_ = stack[1].m_obj;
lean_object* v_a_779_ = stack[2].m_obj;
lean_object* v_a_780_ = stack[3].m_obj;
lean_object* v_a_781_ = stack[4].m_obj;
lean_object* v_a_782_ = stack[5].m_obj;
lean_object* v_res_817_;
v_res_817_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_777_, v_mvarId_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_818_, lean_object* v_mvarId_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_818_, v_mvarId_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_825_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_826_, lean_object* v_v_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___y_834_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_909_; lean_object* v___y_923_; 
switch(lean_obj_tag(v_u_826_))
{
case 5:
{
lean_object* v_a_936_; lean_object* v___x_937_; 
v_a_936_ = lean_ctor_get(v_u_826_, 0);
lean_inc(v_a_936_);
v___x_937_ = l_Lean_LMVarId_isReadOnly(v_a_936_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1034_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_1034_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1034_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_unbox(v_a_938_);
lean_dec(v_a_938_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_del_object(v___x_940_);
lean_inc(v_a_936_);
lean_inc(v_v_827_);
v___x_943_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_827_, v_a_936_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1020_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_1020_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1020_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v___x_954_; 
v___x_954_ = lean_unbox(v_a_944_);
lean_dec(v_a_944_);
if (v___x_954_ == 0)
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Level_occurs(v_u_826_, v_v_827_);
if (v___x_955_ == 0)
{
lean_object* v_toCold_956_; lean_object* v_options_957_; uint8_t v_hasTrace_958_; 
lean_del_object(v___x_946_);
v_toCold_956_ = lean_ctor_get(v_a_830_, 0);
v_options_957_ = lean_ctor_get(v_toCold_956_, 2);
v_hasTrace_958_ = lean_ctor_get_uint8(v_options_957_, sizeof(void*)*1);
if (v_hasTrace_958_ == 0)
{
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_a_828_);
v___y_909_ = v_a_829_;
goto v___jp_908_;
}
else
{
lean_object* v_inheritedTraceOptions_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_inheritedTraceOptions_959_ = lean_ctor_get(v_toCold_956_, 11);
v___x_960_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_959_, v_options_957_, v___x_961_);
if (v___x_962_ == 0)
{
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_a_828_);
v___y_909_ = v_a_829_;
goto v___jp_908_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_inc_ref(v_u_826_);
v___x_963_ = l_Lean_MessageData_ofLevel(v_u_826_);
v___x_964_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
lean_inc(v_v_827_);
v___x_966_ = l_Lean_MessageData_ofLevel(v_v_827_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_960_, v___x_967_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_a_828_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_dec_ref_known(v___x_968_, 1);
v___y_909_ = v_a_829_;
goto v___jp_908_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_829_);
lean_dec(v_v_827_);
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
v___x_977_ = l_Lean_Level_isMax(v_v_827_);
if (v___x_977_ == 0)
{
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
goto v___jp_948_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_826_, v_v_827_);
if (v___x_978_ == 0)
{
if (v___x_977_ == 0)
{
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
goto v___jp_948_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_del_object(v___x_946_);
v___x_979_ = l_Lean_Level_mvarId_x21(v_u_826_);
lean_dec_ref_known(v_u_826_, 1);
v___x_980_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_979_, v_v_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v___x_980_, 0);
lean_dec(v_unused_990_);
v___x_982_ = v___x_980_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_dec(v___x_980_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_984_ = 1;
v___x_985_ = lean_box(v___x_984_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_980_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_980_);
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
else
{
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
goto v___jp_948_;
}
}
}
}
else
{
lean_object* v_toCold_999_; lean_object* v_options_1000_; uint8_t v_hasTrace_1001_; 
lean_del_object(v___x_946_);
v_toCold_999_ = lean_ctor_get(v_a_830_, 0);
v_options_1000_ = lean_ctor_get(v_toCold_999_, 2);
v_hasTrace_1001_ = lean_ctor_get_uint8(v_options_1000_, sizeof(void*)*1);
if (v_hasTrace_1001_ == 0)
{
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_a_828_);
v___y_923_ = v_a_829_;
goto v___jp_922_;
}
else
{
lean_object* v_inheritedTraceOptions_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_inheritedTraceOptions_1002_ = lean_ctor_get(v_toCold_999_, 11);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_1005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1002_, v_options_1000_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_a_828_);
v___y_923_ = v_a_829_;
goto v___jp_922_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc(v_v_827_);
v___x_1006_ = l_Lean_MessageData_ofLevel(v_v_827_);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
lean_inc_ref(v_u_826_);
v___x_1009_ = l_Lean_MessageData_ofLevel(v_u_826_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1003_, v___x_1010_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_a_828_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_dec_ref_known(v___x_1011_, 1);
v___y_923_ = v_a_829_;
goto v___jp_922_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_829_);
lean_dec(v_v_827_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
v___jp_948_:
{
uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = 2;
v___x_950_ = lean_box(v___x_949_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_950_);
v___x_952_ = v___x_946_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
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
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
v_a_1021_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_943_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_943_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
v___x_1029_ = 2;
v___x_1030_ = lean_box(v___x_1029_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_1030_);
v___x_1032_ = v___x_940_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref_known(v_u_826_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
v_a_1035_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_937_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_937_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_827_))
{
case 5:
{
lean_dec_ref_known(v_v_827_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
goto v___jp_904_;
}
case 2:
{
lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1043_ = lean_ctor_get(v_v_827_, 0);
lean_inc(v_a_1043_);
v_a_1044_ = lean_ctor_get(v_v_827_, 1);
lean_inc(v_a_1044_);
lean_dec_ref_known(v_v_827_, 2);
lean_inc(v_a_831_);
lean_inc_ref(v_a_830_);
lean_inc(v_a_829_);
lean_inc_ref(v_a_828_);
v___x_1045_ = lean_is_level_def_eq(v_u_826_, v_a_1043_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; uint8_t v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v___x_1047_ = lean_unbox(v_a_1046_);
if (v___x_1047_ == 0)
{
lean_dec(v_a_1044_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
v___y_834_ = v___x_1045_;
goto v___jp_833_;
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref_known(v___x_1045_, 1);
v___x_1048_ = lean_is_level_def_eq(v_u_826_, v_a_1044_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
v___y_834_ = v___x_1048_;
goto v___jp_833_;
}
}
else
{
lean_dec(v_a_1044_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
v___y_834_ = v___x_1045_;
goto v___jp_833_;
}
}
case 3:
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v_v_827_, 1);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_v_827_, 2);
v___x_1050_ = lean_is_level_def_eq(v_u_826_, v_a_1049_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
uint8_t v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1055_ = lean_unbox(v_a_1051_);
lean_dec(v_a_1051_);
v___x_1056_ = l_Lean_Bool_toLBool(v___x_1055_);
v___x_1057_ = lean_box(v___x_1056_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1050_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1050_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
case 1:
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec_ref_known(v_v_827_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
v___x_1070_ = 0;
v___x_1071_ = lean_box(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
default: 
{
v___y_859_ = v_a_828_;
v___y_860_ = v_a_829_;
v___y_861_ = v_a_830_;
v___y_862_ = v_a_831_;
goto v___jp_858_;
}
}
}
case 1:
{
lean_object* v_a_1073_; uint8_t v___y_1075_; 
v_a_1073_ = lean_ctor_get(v_u_826_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v_u_826_, 1);
if (lean_obj_tag(v_v_827_) == 5)
{
lean_dec_ref_known(v_v_827_, 1);
lean_dec(v_a_1073_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
goto v___jp_904_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_Level_isParam(v_v_827_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; 
v___x_1120_ = l_Lean_Level_isMVar(v_a_1073_);
if (v___x_1120_ == 0)
{
v___y_1075_ = v___x_1119_;
goto v___jp_1074_;
}
else
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_Level_occurs(v_a_1073_, v_v_827_);
v___y_1075_ = v___x_1121_;
goto v___jp_1074_;
}
}
else
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec(v_a_1073_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
v___x_1122_ = 0;
v___x_1123_ = lean_box(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
v___jp_1074_:
{
if (v___y_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Meta_decLevel_x3f(v_v_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1107_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1107_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1107_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
if (lean_obj_tag(v_a_1077_) == 0)
{
uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec(v_a_1073_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
v___x_1081_ = 2;
v___x_1082_ = lean_box(v___x_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
else
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
lean_del_object(v___x_1079_);
v_val_1086_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_a_1077_, 1);
v___x_1087_ = lean_is_level_def_eq(v_a_1073_, v_val_1086_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint8_t v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1092_ = lean_unbox(v_a_1088_);
lean_dec(v_a_1088_);
v___x_1093_ = l_Lean_Bool_toLBool(v___x_1092_);
v___x_1094_ = lean_box(v___x_1093_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1094_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1087_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1087_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1073_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
v_a_1108_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1076_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1076_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_a_1073_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_v_827_);
v___x_1116_ = 2;
v___x_1117_ = lean_box(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_827_) == 5)
{
lean_dec_ref_known(v_v_827_, 1);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_u_826_);
goto v___jp_904_;
}
else
{
v___y_859_ = v_a_828_;
v___y_860_ = v_a_829_;
v___y_861_ = v_a_830_;
v___y_862_ = v_a_831_;
goto v___jp_858_;
}
}
}
v___jp_833_:
{
if (lean_obj_tag(v___y_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
v_a_835_ = lean_ctor_get(v___y_834_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___y_834_);
if (v_isSharedCheck_845_ == 0)
{
v___x_837_ = v___y_834_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___y_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_839_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
v___x_840_ = l_Lean_Bool_toLBool(v___x_839_);
v___x_841_ = lean_box(v___x_840_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_841_);
v___x_843_ = v___x_837_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___y_834_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___y_834_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___y_834_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___y_834_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
v___jp_854_:
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = 2;
v___x_856_ = lean_box(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
v___jp_858_:
{
uint8_t v_univApprox_863_; 
v_univApprox_863_ = lean_ctor_get_uint8(v___y_859_, sizeof(void*)*7 + 1);
if (v_univApprox_863_ == 0)
{
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v_v_827_);
lean_dec(v_u_826_);
goto v___jp_854_;
}
else
{
lean_object* v___x_864_; 
lean_inc(v_v_827_);
lean_inc(v_u_826_);
v___x_864_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_826_, v_v_827_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_895_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_895_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_895_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_895_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; 
v___x_869_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_del_object(v___x_867_);
v___x_870_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_826_, v_v_827_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_881_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_881_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_881_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_881_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_a_871_);
lean_dec(v_a_871_);
if (v___x_875_ == 0)
{
lean_del_object(v___x_873_);
goto v___jp_854_;
}
else
{
uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_876_ = 1;
v___x_877_ = lean_box(v___x_876_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_a_882_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_870_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_870_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v_v_827_);
lean_dec(v_u_826_);
v___x_890_ = 1;
v___x_891_ = lean_box(v___x_890_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_891_);
v___x_893_ = v___x_867_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
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
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v_v_827_);
lean_dec(v_u_826_);
v_a_896_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_864_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_864_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
v___jp_904_:
{
uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = 2;
v___x_906_ = lean_box(v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
v___jp_908_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_920_; 
v___x_910_ = l_Lean_Level_mvarId_x21(v_u_826_);
lean_dec(v_u_826_);
v___x_911_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_910_, v_v_827_, v___y_909_);
lean_dec(v___y_909_);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_921_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = 1;
v___x_916_ = lean_box(v___x_915_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
v___jp_922_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_934_; 
v___x_924_ = l_Lean_Level_mvarId_x21(v_v_827_);
lean_dec(v_v_827_);
v___x_925_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_924_, v_u_826_, v___y_923_);
lean_dec(v___y_923_);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_925_, 0);
lean_dec(v_unused_935_);
v___x_927_ = v___x_925_;
v_isShared_928_ = v_isSharedCheck_934_;
goto v_resetjp_926_;
}
else
{
lean_dec(v___x_925_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_934_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_929_ = 1;
v___x_930_ = lean_box(v___x_929_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_930_);
v___x_932_ = v___x_927_;
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
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_826_ = stack[0].m_obj;
lean_object* v_v_827_ = stack[1].m_obj;
lean_object* v_a_828_ = stack[2].m_obj;
lean_object* v_a_829_ = stack[3].m_obj;
lean_object* v_a_830_ = stack[4].m_obj;
lean_object* v_a_831_ = stack[5].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_826_, v_v_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1126_, lean_object* v_v_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1126_, v_v_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v_res_1133_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; lean_object* v_mctx_1138_; lean_object* v___x_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1142_; lean_object* v_cache_1143_; lean_object* v_zetaDeltaFVarIds_1144_; lean_object* v_postponed_1145_; lean_object* v_diag_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1155_; 
v___x_1137_ = lean_st_ref_get(v___y_1135_);
v_mctx_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_mctx_1138_);
lean_dec(v___x_1137_);
v___x_1139_ = lean_instantiate_level_mvars(v_mctx_1138_, v_l_1134_);
v_fst_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_fst_1140_);
v_snd_1141_ = lean_ctor_get(v___x_1139_, 1);
lean_inc(v_snd_1141_);
lean_dec_ref(v___x_1139_);
v___x_1142_ = lean_st_ref_take(v___y_1135_);
v_cache_1143_ = lean_ctor_get(v___x_1142_, 1);
v_zetaDeltaFVarIds_1144_ = lean_ctor_get(v___x_1142_, 2);
v_postponed_1145_ = lean_ctor_get(v___x_1142_, 3);
v_diag_1146_ = lean_ctor_get(v___x_1142_, 4);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v___x_1142_, 0);
lean_dec(v_unused_1156_);
v___x_1148_ = v___x_1142_;
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_diag_1146_);
lean_inc(v_postponed_1145_);
lean_inc(v_zetaDeltaFVarIds_1144_);
lean_inc(v_cache_1143_);
lean_dec(v___x_1142_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_fst_1140_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_cache_1143_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_zetaDeltaFVarIds_1144_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_postponed_1145_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_diag_1146_);
v___x_1151_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_st_ref_put(v___y_1135_, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_snd_1141_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_1134_ = stack[0].m_obj;
lean_object* v___y_1135_ = stack[1].m_obj;
lean_object* v_res_1157_;
v_res_1157_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1134_, v___y_1135_);
stack->m_obj
 = v_res_1157_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1158_, v___y_1159_);
lean_dec(v___y_1159_);
return v_res_1161_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1162_, v___y_1164_);
return v___x_1168_;
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_1162_ = stack[0].m_obj;
lean_object* v___y_1163_ = stack[1].m_obj;
lean_object* v___y_1164_ = stack[2].m_obj;
lean_object* v___y_1165_ = stack[3].m_obj;
lean_object* v___y_1166_ = stack[4].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
stack->m_obj
 = v_res_1169_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1176_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(32u);
v___x_1178_ = lean_mk_empty_array_with_capacity(v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1180_ = ((size_t)5ULL);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_unsigned_to_nat(32u);
v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1182_);
v___x_1184_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1185_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1183_);
lean_ctor_set(v___x_1185_, 2, v___x_1181_);
lean_ctor_set(v___x_1185_, 3, v___x_1181_);
lean_ctor_set_usize(v___x_1185_, 4, v___x_1180_);
return v___x_1185_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v_traceState_1189_; lean_object* v_traces_1190_; lean_object* v___x_1191_; lean_object* v_traceState_1192_; lean_object* v_env_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v_ngen_1195_; lean_object* v_auxDeclNGen_1196_; lean_object* v_cache_1197_; lean_object* v_recordedDeps_1198_; lean_object* v_messages_1199_; lean_object* v_infoState_1200_; lean_object* v_snapshotTasks_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1220_; 
v___x_1188_ = lean_st_ref_get(v___y_1186_);
v_traceState_1189_ = lean_ctor_get(v___x_1188_, 4);
lean_inc_ref(v_traceState_1189_);
lean_dec(v___x_1188_);
v_traces_1190_ = lean_ctor_get(v_traceState_1189_, 0);
lean_inc_ref(v_traces_1190_);
lean_dec_ref(v_traceState_1189_);
v___x_1191_ = lean_st_ref_take(v___y_1186_);
v_traceState_1192_ = lean_ctor_get(v___x_1191_, 4);
v_env_1193_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1195_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1196_ = lean_ctor_get(v___x_1191_, 3);
v_cache_1197_ = lean_ctor_get(v___x_1191_, 5);
v_recordedDeps_1198_ = lean_ctor_get(v___x_1191_, 6);
v_messages_1199_ = lean_ctor_get(v___x_1191_, 7);
v_infoState_1200_ = lean_ctor_get(v___x_1191_, 8);
v_snapshotTasks_1201_ = lean_ctor_get(v___x_1191_, 9);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1203_ = v___x_1191_;
v_isShared_1204_ = v_isSharedCheck_1220_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snapshotTasks_1201_);
lean_inc(v_infoState_1200_);
lean_inc(v_messages_1199_);
lean_inc(v_recordedDeps_1198_);
lean_inc(v_cache_1197_);
lean_inc(v_traceState_1192_);
lean_inc(v_auxDeclNGen_1196_);
lean_inc(v_ngen_1195_);
lean_inc(v_nextMacroScope_1194_);
lean_inc(v_env_1193_);
lean_dec(v___x_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1220_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint64_t v_tid_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1218_; 
v_tid_1205_ = lean_ctor_get_uint64(v_traceState_1192_, sizeof(void*)*1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_traceState_1192_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_traceState_1192_, 0);
lean_dec(v_unused_1219_);
v___x_1207_ = v_traceState_1192_;
v_isShared_1208_ = v_isSharedCheck_1218_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v_traceState_1192_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1218_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1209_);
lean_ctor_set_uint64(v_reuseFailAlloc_1217_, sizeof(void*)*1, v_tid_1205_);
v___x_1211_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v___x_1211_);
v___x_1213_ = v___x_1203_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_env_1193_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_nextMacroScope_1194_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_ngen_1195_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_auxDeclNGen_1196_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v_cache_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 6, v_recordedDeps_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 7, v_messages_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 8, v_infoState_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 9, v_snapshotTasks_1201_);
v___x_1213_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_st_ref_put(v___y_1186_, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v_traces_1190_);
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1186_ = stack[0].m_obj;
lean_object* v_res_1221_;
v_res_1221_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1186_);
stack->m_obj
 = v_res_1221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1222_);
lean_dec(v___y_1222_);
return v_res_1224_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1225_ = stack[0].m_obj;
lean_object* v___y_1226_ = stack[1].m_obj;
lean_object* v___y_1227_ = stack[2].m_obj;
lean_object* v___y_1228_ = stack[3].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1237_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1238_, lean_object* v_k_1239_, uint8_t v_v_1240_){
_start:
{
lean_object* v_map_1241_; uint8_t v_hasTrace_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1256_; 
v_map_1241_ = lean_ctor_get(v_o_1238_, 0);
v_hasTrace_1242_ = lean_ctor_get_uint8(v_o_1238_, sizeof(void*)*1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_o_1238_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1244_ = v_o_1238_;
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_map_1241_);
lean_dec(v_o_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1246_, 0, v_v_1240_);
lean_inc(v_k_1239_);
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1239_, v___x_1246_, v_map_1241_);
if (v_hasTrace_1242_ == 0)
{
lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1251_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1249_ = l_Lean_Name_isPrefixOf(v___x_1248_, v_k_1239_);
lean_dec(v_k_1239_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1247_);
v___x_1251_ = v___x_1244_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1247_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1249_);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_k_1239_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1247_);
v___x_1254_ = v___x_1244_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*1, v_hasTrace_1242_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1238_ = stack[0].m_obj;
lean_object* v_k_1239_ = stack[1].m_obj;
uint8_t v_v_1240_ = stack[2].m_num;
lean_object* v_res_1257_;
v_res_1257_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1238_, v_k_1239_, v_v_1240_);
stack->m_obj
 = v_res_1257_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1258_, lean_object* v_k_1259_, lean_object* v_v_1260_){
_start:
{
uint8_t v_v_boxed_1261_; lean_object* v_res_1262_; 
v_v_boxed_1261_ = lean_unbox(v_v_1260_);
v_res_1262_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1258_, v_k_1259_, v_v_boxed_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1263_, lean_object* v_opt_1264_){
_start:
{
lean_object* v_name_1265_; lean_object* v_defValue_1266_; lean_object* v_map_1267_; lean_object* v___x_1268_; 
v_name_1265_ = lean_ctor_get(v_opt_1264_, 0);
v_defValue_1266_ = lean_ctor_get(v_opt_1264_, 1);
v_map_1267_ = lean_ctor_get(v_opts_1263_, 0);
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1267_, v_name_1265_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_inc(v_defValue_1266_);
return v_defValue_1266_;
}
else
{
lean_object* v_val_1269_; 
v_val_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1268_, 1);
if (lean_obj_tag(v_val_1269_) == 3)
{
lean_object* v_v_1270_; 
v_v_1270_ = lean_ctor_get(v_val_1269_, 0);
lean_inc(v_v_1270_);
lean_dec_ref_known(v_val_1269_, 1);
return v_v_1270_;
}
else
{
lean_dec(v_val_1269_);
lean_inc(v_defValue_1266_);
return v_defValue_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1271_, lean_object* v_opt_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1271_, v_opt_1272_);
lean_dec_ref(v_opt_1272_);
lean_dec_ref(v_opts_1271_);
return v_res_1273_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1274_, lean_object* v_opt_1275_){
_start:
{
lean_object* v_name_1276_; lean_object* v_defValue_1277_; lean_object* v_map_1278_; lean_object* v___x_1279_; 
v_name_1276_ = lean_ctor_get(v_opt_1275_, 0);
v_defValue_1277_ = lean_ctor_get(v_opt_1275_, 1);
v_map_1278_ = lean_ctor_get(v_opts_1274_, 0);
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1278_, v_name_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_unbox(v_defValue_1277_);
return v___x_1280_;
}
else
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1279_, 1);
if (lean_obj_tag(v_val_1281_) == 1)
{
uint8_t v_v_1282_; 
v_v_1282_ = lean_ctor_get_uint8(v_val_1281_, 0);
lean_dec_ref_known(v_val_1281_, 0);
return v_v_1282_;
}
else
{
uint8_t v___x_1283_; 
lean_dec(v_val_1281_);
v___x_1283_ = lean_unbox(v_defValue_1277_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1274_ = stack[0].m_obj;
lean_object* v_opt_1275_ = stack[1].m_obj;
uint8_t v_res_1284_;
v_res_1284_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1274_, v_opt_1275_);
stack->m_num = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1285_, lean_object* v_opt_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1285_, v_opt_1286_);
lean_dec_ref(v_opt_1286_);
lean_dec_ref(v_opts_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1289_, lean_object* v___x_1290_, lean_object* v___x_1291_, lean_object* v_lhs_1292_, lean_object* v_rhs_1293_, uint8_t v___x_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___y_1328_; 
if (v___x_1289_ == 0)
{
lean_object* v___x_1365_; lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
lean_inc(v_lhs_1292_);
v___x_1365_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1292_, v___y_1296_);
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l_Lean_Level_normalize(v_a_1366_);
lean_dec(v_a_1366_);
lean_inc(v_rhs_1293_);
v___x_1368_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1293_, v___y_1296_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = l_Lean_Level_normalize(v_a_1369_);
lean_dec(v_a_1369_);
v___x_1371_ = lean_level_eq(v_lhs_1292_, v___x_1367_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
v___x_1372_ = lean_is_level_def_eq(v___x_1367_, v___x_1370_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v___x_1372_;
}
else
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_level_eq(v_rhs_1293_, v___x_1370_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
v___x_1374_ = lean_is_level_def_eq(v___x_1367_, v___x_1370_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; 
lean_dec(v___x_1370_);
lean_dec(v___x_1367_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v_rhs_1293_);
lean_inc(v_lhs_1292_);
v___x_1375_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1292_, v_rhs_1293_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1417_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1417_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1417_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; uint8_t v___x_1381_; uint8_t v___x_1382_; 
v___x_1380_ = 2;
v___x_1381_ = lean_unbox(v_a_1376_);
v___x_1382_ = l_Lean_instBEqLBool_beq(v___x_1381_, v___x_1380_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; uint8_t v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1383_ = 1;
v___x_1384_ = lean_unbox(v_a_1376_);
lean_dec(v_a_1376_);
v___x_1385_ = l_Lean_instBEqLBool_beq(v___x_1384_, v___x_1383_);
v___x_1386_ = lean_box(v___x_1385_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1386_);
v___x_1388_ = v___x_1378_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
lean_object* v___x_1390_; 
lean_del_object(v___x_1378_);
lean_dec(v_a_1376_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v_lhs_1292_);
lean_inc(v_rhs_1293_);
v___x_1390_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1293_, v_lhs_1292_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1408_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1408_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1408_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_unbox(v_a_1391_);
v___x_1396_ = l_Lean_instBEqLBool_beq(v___x_1395_, v___x_1380_);
if (v___x_1396_ == 0)
{
uint8_t v___x_1397_; uint8_t v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1397_ = 1;
v___x_1398_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
v___x_1399_ = l_Lean_instBEqLBool_beq(v___x_1398_, v___x_1397_);
v___x_1400_ = lean_box(v___x_1399_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1400_);
v___x_1402_ = v___x_1393_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1404_; 
lean_del_object(v___x_1393_);
lean_dec(v_a_1391_);
lean_inc(v_lhs_1292_);
v___x_1404_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1292_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; uint8_t v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v___x_1406_ = lean_unbox(v_a_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref_known(v___x_1404_, 1);
lean_inc(v_rhs_1293_);
v___x_1407_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1293_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
v___y_1328_ = v___x_1407_;
goto v___jp_1327_;
}
else
{
v___y_1328_ = v___x_1404_;
goto v___jp_1327_;
}
}
else
{
v___y_1328_ = v___x_1404_;
goto v___jp_1327_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v_a_1409_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1390_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1390_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v_a_1418_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1375_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1375_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1426_ = l_Lean_Level_getOffset(v_lhs_1292_);
lean_dec(v_lhs_1292_);
v___x_1427_ = l_Lean_Level_getOffset(v_rhs_1293_);
lean_dec(v_rhs_1293_);
v___x_1428_ = lean_nat_dec_eq(v___x_1426_, v___x_1427_);
lean_dec(v___x_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
v___jp_1300_:
{
lean_object* v_toCold_1301_; lean_object* v_options_1302_; uint8_t v_hasTrace_1303_; 
v_toCold_1301_ = lean_ctor_get(v___y_1297_, 0);
v_options_1302_ = lean_ctor_get(v_toCold_1301_, 2);
v_hasTrace_1303_ = lean_ctor_get_uint8(v_options_1302_, sizeof(void*)*1);
if (v_hasTrace_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1304_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1304_;
}
else
{
lean_object* v_inheritedTraceOptions_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_inheritedTraceOptions_1305_ = lean_ctor_get(v_toCold_1301_, 11);
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1307_ = l_Lean_Name_mkStr3(v___x_1290_, v___x_1291_, v___x_1306_);
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1307_);
v___x_1309_ = l_Lean_Name_append(v___x_1308_, v___x_1307_);
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1305_, v_options_1302_, v___x_1309_);
lean_dec(v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v___x_1307_);
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
v___x_1311_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1312_ = l_Lean_MessageData_ofLevel(v_lhs_1292_);
v___x_1313_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_MessageData_ofLevel(v_rhs_1293_);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1307_, v___x_1316_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref_known(v___x_1317_, 1);
v___x_1318_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1318_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1319_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1317_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1317_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
v___jp_1327_:
{
if (lean_obj_tag(v___y_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1364_; 
v_a_1329_ = lean_ctor_get(v___y_1328_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___y_1328_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1331_ = v___y_1328_;
v_isShared_1332_ = v_isSharedCheck_1364_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___y_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1364_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_unbox(v_a_1329_);
lean_dec(v_a_1329_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; uint8_t v_isDefEqStuckEx_1335_; 
v___x_1334_ = l_Lean_Meta_Context_config(v___y_1295_);
v_isDefEqStuckEx_1335_ = lean_ctor_get_uint8(v___x_1334_, 4);
lean_dec_ref(v___x_1334_);
if (v_isDefEqStuckEx_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1336_ = lean_box(v___x_1289_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1336_);
v___x_1338_ = v___x_1331_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_Level_isMVar(v_lhs_1292_);
if (v___x_1340_ == 0)
{
uint8_t v___x_1341_; 
v___x_1341_ = l_Lean_Level_isMVar(v_rhs_1293_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1342_ = lean_box(v___x_1341_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1342_);
v___x_1344_ = v___x_1331_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
lean_del_object(v___x_1331_);
goto v___jp_1300_;
}
}
else
{
lean_del_object(v___x_1331_);
goto v___jp_1300_;
}
}
}
else
{
lean_object* v___x_1346_; 
lean_del_object(v___x_1331_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
v___x_1346_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1292_, v_rhs_1293_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v___x_1346_, 0);
lean_dec(v_unused_1355_);
v___x_1348_ = v___x_1346_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v___x_1346_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_box(v___x_1294_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1346_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1346_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
else
{
lean_dec(v_rhs_1293_);
lean_dec(v_lhs_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v___x_1290_);
return v___y_1328_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isLevelDefEqAuxImpl___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1289_ = stack[0].m_num;
lean_object* v___x_1290_ = stack[1].m_obj;
lean_object* v___x_1291_ = stack[2].m_obj;
lean_object* v_lhs_1292_ = stack[3].m_obj;
lean_object* v_rhs_1293_ = stack[4].m_obj;
uint8_t v___x_1294_ = stack[5].m_num;
lean_object* v___y_1295_ = stack[6].m_obj;
lean_object* v___y_1296_ = stack[7].m_obj;
lean_object* v___y_1297_ = stack[8].m_obj;
lean_object* v___y_1298_ = stack[9].m_obj;
lean_object* v_res_1431_;
v_res_1431_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1289_, v___x_1290_, v___x_1291_, v_lhs_1292_, v_rhs_1293_, v___x_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
stack->m_obj
 = v_res_1431_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1432_, lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v_lhs_1435_, lean_object* v_rhs_1436_, lean_object* v___x_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v___x_13328__boxed_1443_; uint8_t v___x_13331__boxed_1444_; lean_object* v_res_1445_; 
v___x_13328__boxed_1443_ = lean_unbox(v___x_1432_);
v___x_13331__boxed_1444_ = lean_unbox(v___x_1437_);
v_res_1445_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13328__boxed_1443_, v___x_1433_, v___x_1434_, v_lhs_1435_, v_rhs_1436_, v___x_13331__boxed_1444_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1445_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1446_){
_start:
{
if (lean_obj_tag(v_e_1446_) == 0)
{
uint8_t v___x_1447_; 
v___x_1447_ = 2;
return v___x_1447_;
}
else
{
lean_object* v_a_1448_; uint8_t v___x_1449_; 
v_a_1448_ = lean_ctor_get(v_e_1446_, 0);
v___x_1449_ = lean_unbox(v_a_1448_);
if (v___x_1449_ == 0)
{
uint8_t v___x_1450_; 
v___x_1450_ = 1;
return v___x_1450_;
}
else
{
uint8_t v___x_1451_; 
v___x_1451_ = 0;
return v___x_1451_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1446_ = stack[0].m_obj;
uint8_t v_res_1452_;
v_res_1452_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1446_);
stack->m_num = v_res_1452_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1453_);
lean_dec_ref(v_e_1453_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1456_){
_start:
{
if (lean_obj_tag(v_x_1456_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v_x_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v_x_1456_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v_x_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 1);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v_x_1456_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_x_1456_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v_x_1456_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v_x_1456_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 0);
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1456_ = stack[0].m_obj;
lean_object* v_res_1474_;
v_res_1474_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1456_);
stack->m_obj
 = v_res_1474_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1475_);
return v_res_1477_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_bs_1480_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_usize_dec_lt(v_i_1479_, v_sz_1478_);
if (v___x_1481_ == 0)
{
return v_bs_1480_;
}
else
{
lean_object* v_v_1482_; lean_object* v_msg_1483_; lean_object* v___x_1484_; lean_object* v_bs_x27_1485_; size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v_v_1482_ = lean_array_uget_borrowed(v_bs_1480_, v_i_1479_);
v_msg_1483_ = lean_ctor_get(v_v_1482_, 1);
lean_inc_ref(v_msg_1483_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v_bs_x27_1485_ = lean_array_uset(v_bs_1480_, v_i_1479_, v___x_1484_);
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1479_, v___x_1486_);
v___x_1488_ = lean_array_uset(v_bs_x27_1485_, v_i_1479_, v_msg_1483_);
v_i_1479_ = v___x_1487_;
v_bs_1480_ = v___x_1488_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1478_ = stack[0].m_num;
size_t v_i_1479_ = stack[1].m_num;
lean_object* v_bs_1480_ = stack[2].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1478_, v_i_1479_, v_bs_1480_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1491_, lean_object* v_i_1492_, lean_object* v_bs_1493_){
_start:
{
size_t v_sz_boxed_1494_; size_t v_i_boxed_1495_; lean_object* v_res_1496_; 
v_sz_boxed_1494_ = lean_unbox_usize(v_sz_1491_);
lean_dec(v_sz_1491_);
v_i_boxed_1495_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_res_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1494_, v_i_boxed_1495_, v_bs_1493_);
return v_res_1496_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1497_, lean_object* v_data_1498_, lean_object* v_ref_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_toCold_1506_; lean_object* v_currRecDepth_1507_; lean_object* v_ref_1508_; uint16_t v_optionFlags_1509_; uint8_t v_suppressElabErrors_1510_; uint8_t v_isRecordingDeps_1511_; lean_object* v_ref_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_traceState_1515_; lean_object* v_traces_1516_; lean_object* v___x_1517_; size_t v_sz_1518_; size_t v___x_1519_; lean_object* v___x_1520_; lean_object* v_msg_1521_; lean_object* v___x_1522_; lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1561_; 
v_toCold_1506_ = lean_ctor_get(v___y_1503_, 0);
v_currRecDepth_1507_ = lean_ctor_get(v___y_1503_, 1);
v_ref_1508_ = lean_ctor_get(v___y_1503_, 2);
v_optionFlags_1509_ = lean_ctor_get_uint16(v___y_1503_, sizeof(void*)*3);
v_suppressElabErrors_1510_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1511_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*3 + 3);
v_ref_1512_ = l_Lean_replaceRef(v_ref_1499_, v_ref_1508_);
lean_inc(v_currRecDepth_1507_);
lean_inc_ref(v_toCold_1506_);
v___x_1513_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1513_, 0, v_toCold_1506_);
lean_ctor_set(v___x_1513_, 1, v_currRecDepth_1507_);
lean_ctor_set(v___x_1513_, 2, v_ref_1512_);
lean_ctor_set_uint16(v___x_1513_, sizeof(void*)*3, v_optionFlags_1509_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*3 + 2, v_suppressElabErrors_1510_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*3 + 3, v_isRecordingDeps_1511_);
v___x_1514_ = lean_st_ref_get(v___y_1504_);
v_traceState_1515_ = lean_ctor_get(v___x_1514_, 4);
lean_inc_ref(v_traceState_1515_);
lean_dec(v___x_1514_);
v_traces_1516_ = lean_ctor_get(v_traceState_1515_, 0);
lean_inc_ref(v_traces_1516_);
lean_dec_ref(v_traceState_1515_);
v___x_1517_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1516_);
lean_dec_ref(v_traces_1516_);
v_sz_1518_ = lean_array_size(v___x_1517_);
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1518_, v___x_1519_, v___x_1517_);
v_msg_1521_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1521_, 0, v_data_1498_);
lean_ctor_set(v_msg_1521_, 1, v_msg_1500_);
lean_ctor_set(v_msg_1521_, 2, v___x_1520_);
v___x_1522_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1521_, v___y_1501_, v___y_1502_, v___x_1513_, v___y_1504_);
lean_dec_ref_known(v___x_1513_, 3);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1561_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1561_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v_traceState_1528_; lean_object* v_env_1529_; lean_object* v_nextMacroScope_1530_; lean_object* v_ngen_1531_; lean_object* v_auxDeclNGen_1532_; lean_object* v_cache_1533_; lean_object* v_recordedDeps_1534_; lean_object* v_messages_1535_; lean_object* v_infoState_1536_; lean_object* v_snapshotTasks_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1560_; 
v___x_1527_ = lean_st_ref_take(v___y_1504_);
v_traceState_1528_ = lean_ctor_get(v___x_1527_, 4);
v_env_1529_ = lean_ctor_get(v___x_1527_, 0);
v_nextMacroScope_1530_ = lean_ctor_get(v___x_1527_, 1);
v_ngen_1531_ = lean_ctor_get(v___x_1527_, 2);
v_auxDeclNGen_1532_ = lean_ctor_get(v___x_1527_, 3);
v_cache_1533_ = lean_ctor_get(v___x_1527_, 5);
v_recordedDeps_1534_ = lean_ctor_get(v___x_1527_, 6);
v_messages_1535_ = lean_ctor_get(v___x_1527_, 7);
v_infoState_1536_ = lean_ctor_get(v___x_1527_, 8);
v_snapshotTasks_1537_ = lean_ctor_get(v___x_1527_, 9);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1539_ = v___x_1527_;
v_isShared_1540_ = v_isSharedCheck_1560_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_snapshotTasks_1537_);
lean_inc(v_infoState_1536_);
lean_inc(v_messages_1535_);
lean_inc(v_recordedDeps_1534_);
lean_inc(v_cache_1533_);
lean_inc(v_traceState_1528_);
lean_inc(v_auxDeclNGen_1532_);
lean_inc(v_ngen_1531_);
lean_inc(v_nextMacroScope_1530_);
lean_inc(v_env_1529_);
lean_dec(v___x_1527_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1560_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint64_t v_tid_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1558_; 
v_tid_1541_ = lean_ctor_get_uint64(v_traceState_1528_, sizeof(void*)*1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_traceState_1528_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_traceState_1528_, 0);
lean_dec(v_unused_1559_);
v___x_1543_ = v_traceState_1528_;
v_isShared_1544_ = v_isSharedCheck_1558_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v_traceState_1528_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1558_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_ref_1499_);
lean_ctor_set(v___x_1546_, 1, v_a_1523_);
v___x_1547_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1497_, v___x_1546_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1547_);
v___x_1549_ = v___x_1543_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1547_);
lean_ctor_set_uint64(v_reuseFailAlloc_1557_, sizeof(void*)*1, v_tid_1541_);
v___x_1549_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 4, v___x_1549_);
v___x_1551_ = v___x_1539_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_env_1529_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_nextMacroScope_1530_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_ngen_1531_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_auxDeclNGen_1532_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1556_, 5, v_cache_1533_);
lean_ctor_set(v_reuseFailAlloc_1556_, 6, v_recordedDeps_1534_);
lean_ctor_set(v_reuseFailAlloc_1556_, 7, v_messages_1535_);
lean_ctor_set(v_reuseFailAlloc_1556_, 8, v_infoState_1536_);
lean_ctor_set(v_reuseFailAlloc_1556_, 9, v_snapshotTasks_1537_);
v___x_1551_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_st_ref_put(v___y_1504_, v___x_1551_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1545_);
v___x_1554_ = v___x_1525_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1545_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1497_ = stack[0].m_obj;
lean_object* v_data_1498_ = stack[1].m_obj;
lean_object* v_ref_1499_ = stack[2].m_obj;
lean_object* v_msg_1500_ = stack[3].m_obj;
lean_object* v___y_1501_ = stack[4].m_obj;
lean_object* v___y_1502_ = stack[5].m_obj;
lean_object* v___y_1503_ = stack[6].m_obj;
lean_object* v___y_1504_ = stack[7].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1497_, v_data_1498_, v_ref_1499_, v_msg_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1563_, lean_object* v_data_1564_, lean_object* v_ref_1565_, lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1563_, v_data_1564_, v_ref_1565_, v_msg_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1572_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1573_; double v___x_1574_; 
v___x_1573_ = lean_unsigned_to_nat(1000u);
v___x_1574_ = lean_float_of_nat(v___x_1573_);
return v___x_1574_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1575_, uint8_t v_collapsed_1576_, lean_object* v_tag_1577_, lean_object* v_opts_1578_, uint8_t v_clsEnabled_1579_, lean_object* v_oldTraces_1580_, lean_object* v_ref_1581_, lean_object* v_msg_1582_, lean_object* v_resStartStop_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v_data_1592_; lean_object* v_fst_1603_; lean_object* v_snd_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; uint8_t v___y_1617_; double v___y_1649_; 
v_fst_1589_ = lean_ctor_get(v_resStartStop_1583_, 0);
lean_inc(v_fst_1589_);
v_snd_1590_ = lean_ctor_get(v_resStartStop_1583_, 1);
lean_inc(v_snd_1590_);
lean_dec_ref(v_resStartStop_1583_);
v_fst_1603_ = lean_ctor_get(v_snd_1590_, 0);
lean_inc(v_fst_1603_);
v_snd_1604_ = lean_ctor_get(v_snd_1590_, 1);
lean_inc(v_snd_1604_);
lean_dec(v_snd_1590_);
v___x_1605_ = l_Lean_trace_profiler;
v___x_1606_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1578_, v___x_1605_);
if (v___x_1606_ == 0)
{
v___y_1617_ = v___x_1606_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1655_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1578_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; double v___x_1658_; double v___x_1659_; double v___x_1660_; 
v___x_1656_ = l_Lean_trace_profiler_threshold;
v___x_1657_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1578_, v___x_1656_);
v___x_1658_ = lean_float_of_nat(v___x_1657_);
v___x_1659_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1660_ = lean_float_div(v___x_1658_, v___x_1659_);
v___y_1649_ = v___x_1660_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; double v___x_1663_; 
v___x_1661_ = l_Lean_trace_profiler_threshold;
v___x_1662_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1578_, v___x_1661_);
v___x_1663_ = lean_float_of_nat(v___x_1662_);
v___y_1649_ = v___x_1663_;
goto v___jp_1648_;
}
}
v___jp_1591_:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1580_, v_data_1592_, v_ref_1581_, v_msg_1582_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref_known(v___x_1593_, 1);
v___x_1594_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1589_);
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_fst_1589_);
v_a_1595_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1593_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
v___jp_1607_:
{
uint8_t v_result_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; double v___x_1611_; lean_object* v_data_1612_; 
v_result_1608_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1589_);
v___x_1609_ = lean_box(v_result_1608_);
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
v___x_1611_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1577_);
lean_inc_ref(v___x_1610_);
lean_inc(v_cls_1575_);
v_data_1612_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1612_, 0, v_cls_1575_);
lean_ctor_set(v_data_1612_, 1, v___x_1610_);
lean_ctor_set(v_data_1612_, 2, v_tag_1577_);
lean_ctor_set_float(v_data_1612_, sizeof(void*)*3, v___x_1611_);
lean_ctor_set_float(v_data_1612_, sizeof(void*)*3 + 8, v___x_1611_);
lean_ctor_set_uint8(v_data_1612_, sizeof(void*)*3 + 16, v_collapsed_1576_);
if (v___x_1606_ == 0)
{
lean_dec_ref_known(v___x_1610_, 1);
lean_dec(v_snd_1604_);
lean_dec(v_fst_1603_);
lean_dec_ref(v_tag_1577_);
lean_dec(v_cls_1575_);
v_data_1592_ = v_data_1612_;
goto v___jp_1591_;
}
else
{
lean_object* v_data_1613_; double v___x_1614_; double v___x_1615_; 
lean_dec_ref_known(v_data_1612_, 3);
v_data_1613_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1613_, 0, v_cls_1575_);
lean_ctor_set(v_data_1613_, 1, v___x_1610_);
lean_ctor_set(v_data_1613_, 2, v_tag_1577_);
v___x_1614_ = lean_unbox_float(v_fst_1603_);
lean_dec(v_fst_1603_);
lean_ctor_set_float(v_data_1613_, sizeof(void*)*3, v___x_1614_);
v___x_1615_ = lean_unbox_float(v_snd_1604_);
lean_dec(v_snd_1604_);
lean_ctor_set_float(v_data_1613_, sizeof(void*)*3 + 8, v___x_1615_);
lean_ctor_set_uint8(v_data_1613_, sizeof(void*)*3 + 16, v_collapsed_1576_);
v_data_1592_ = v_data_1613_;
goto v___jp_1591_;
}
}
v___jp_1616_:
{
if (v_clsEnabled_1579_ == 0)
{
if (v___y_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v_traceState_1619_; lean_object* v_env_1620_; lean_object* v_nextMacroScope_1621_; lean_object* v_ngen_1622_; lean_object* v_auxDeclNGen_1623_; lean_object* v_cache_1624_; lean_object* v_recordedDeps_1625_; lean_object* v_messages_1626_; lean_object* v_infoState_1627_; lean_object* v_snapshotTasks_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_snd_1604_);
lean_dec(v_fst_1603_);
lean_dec_ref(v_msg_1582_);
lean_dec(v_ref_1581_);
lean_dec_ref(v_tag_1577_);
lean_dec(v_cls_1575_);
v___x_1618_ = lean_st_ref_take(v___y_1587_);
v_traceState_1619_ = lean_ctor_get(v___x_1618_, 4);
v_env_1620_ = lean_ctor_get(v___x_1618_, 0);
v_nextMacroScope_1621_ = lean_ctor_get(v___x_1618_, 1);
v_ngen_1622_ = lean_ctor_get(v___x_1618_, 2);
v_auxDeclNGen_1623_ = lean_ctor_get(v___x_1618_, 3);
v_cache_1624_ = lean_ctor_get(v___x_1618_, 5);
v_recordedDeps_1625_ = lean_ctor_get(v___x_1618_, 6);
v_messages_1626_ = lean_ctor_get(v___x_1618_, 7);
v_infoState_1627_ = lean_ctor_get(v___x_1618_, 8);
v_snapshotTasks_1628_ = lean_ctor_get(v___x_1618_, 9);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1630_ = v___x_1618_;
v_isShared_1631_ = v_isSharedCheck_1647_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snapshotTasks_1628_);
lean_inc(v_infoState_1627_);
lean_inc(v_messages_1626_);
lean_inc(v_recordedDeps_1625_);
lean_inc(v_cache_1624_);
lean_inc(v_traceState_1619_);
lean_inc(v_auxDeclNGen_1623_);
lean_inc(v_ngen_1622_);
lean_inc(v_nextMacroScope_1621_);
lean_inc(v_env_1620_);
lean_dec(v___x_1618_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1647_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
uint64_t v_tid_1632_; lean_object* v_traces_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1646_; 
v_tid_1632_ = lean_ctor_get_uint64(v_traceState_1619_, sizeof(void*)*1);
v_traces_1633_ = lean_ctor_get(v_traceState_1619_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_traceState_1619_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1635_ = v_traceState_1619_;
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_traces_1633_);
lean_dec(v_traceState_1619_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1580_, v_traces_1633_);
lean_dec_ref(v_traces_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1637_);
lean_ctor_set_uint64(v_reuseFailAlloc_1645_, sizeof(void*)*1, v_tid_1632_);
v___x_1639_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 4, v___x_1639_);
v___x_1641_ = v___x_1630_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_env_1620_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_nextMacroScope_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_ngen_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_auxDeclNGen_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_cache_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v_recordedDeps_1625_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_messages_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_infoState_1627_);
lean_ctor_set(v_reuseFailAlloc_1644_, 9, v_snapshotTasks_1628_);
v___x_1641_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_put(v___y_1587_, v___x_1641_);
v___x_1643_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1589_);
return v___x_1643_;
}
}
}
}
}
else
{
goto v___jp_1607_;
}
}
else
{
goto v___jp_1607_;
}
}
v___jp_1648_:
{
double v___x_1650_; double v___x_1651_; double v___x_1652_; uint8_t v___x_1653_; 
v___x_1650_ = lean_unbox_float(v_snd_1604_);
v___x_1651_ = lean_unbox_float(v_fst_1603_);
v___x_1652_ = lean_float_sub(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_float_decLt(v___y_1649_, v___x_1652_);
v___y_1617_ = v___x_1653_;
goto v___jp_1616_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1575_ = stack[0].m_obj;
uint8_t v_collapsed_1576_ = stack[1].m_num;
lean_object* v_tag_1577_ = stack[2].m_obj;
lean_object* v_opts_1578_ = stack[3].m_obj;
uint8_t v_clsEnabled_1579_ = stack[4].m_num;
lean_object* v_oldTraces_1580_ = stack[5].m_obj;
lean_object* v_ref_1581_ = stack[6].m_obj;
lean_object* v_msg_1582_ = stack[7].m_obj;
lean_object* v_resStartStop_1583_ = stack[8].m_obj;
lean_object* v___y_1584_ = stack[9].m_obj;
lean_object* v___y_1585_ = stack[10].m_obj;
lean_object* v___y_1586_ = stack[11].m_obj;
lean_object* v___y_1587_ = stack[12].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1575_, v_collapsed_1576_, v_tag_1577_, v_opts_1578_, v_clsEnabled_1579_, v_oldTraces_1580_, v_ref_1581_, v_msg_1582_, v_resStartStop_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
stack->m_obj
 = v_res_1664_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1665_, lean_object* v_collapsed_1666_, lean_object* v_tag_1667_, lean_object* v_opts_1668_, lean_object* v_clsEnabled_1669_, lean_object* v_oldTraces_1670_, lean_object* v_ref_1671_, lean_object* v_msg_1672_, lean_object* v_resStartStop_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_collapsed_boxed_1679_; uint8_t v_clsEnabled_boxed_1680_; lean_object* v_res_1681_; 
v_collapsed_boxed_1679_ = lean_unbox(v_collapsed_1666_);
v_clsEnabled_boxed_1680_ = lean_unbox(v_clsEnabled_1669_);
v_res_1681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1665_, v_collapsed_boxed_1679_, v_tag_1667_, v_opts_1668_, v_clsEnabled_boxed_1680_, v_oldTraces_1670_, v_ref_1671_, v_msg_1672_, v_resStartStop_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v_opts_1668_);
return v_res_1681_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1682_; double v___x_1683_; 
v___x_1682_ = lean_unsigned_to_nat(1000000000u);
v___x_1683_ = lean_float_of_nat(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1698_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1699_ = l_Lean_Name_append(v___x_1698_, v___x_1697_);
return v___x_1699_;
}
}
lean_object* lean_is_level_def_eq(lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v_a_1721_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; uint8_t v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; uint8_t v___y_1742_; lean_object* v___y_1743_; lean_object* v_a_1744_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; uint8_t v___y_1765_; lean_object* v___y_1766_; uint16_t v___y_1767_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v_toCold_1773_; lean_object* v_currRecDepth_1774_; lean_object* v_ref_1775_; uint8_t v_suppressElabErrors_1776_; uint8_t v_isRecordingDeps_1777_; lean_object* v___y_1778_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1853_; uint16_t v___y_1854_; lean_object* v___y_1855_; uint8_t v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; uint8_t v___y_1877_; lean_object* v___y_1878_; uint16_t v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; uint8_t v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1916_; lean_object* v___y_1917_; uint16_t v___y_1918_; lean_object* v___y_1919_; uint8_t v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1924_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1939_; lean_object* v___y_1940_; uint16_t v___y_1941_; uint8_t v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v_lhs_1966_; lean_object* v_rhs_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; 
if (lean_obj_tag(v_x_1700_) == 1)
{
if (lean_obj_tag(v_x_1701_) == 1)
{
lean_object* v_a_1998_; lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1998_ = lean_ctor_get(v_x_1700_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v_x_1700_, 1);
v_a_1999_ = lean_ctor_get(v_x_1701_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v_x_1701_, 1);
v___x_2000_ = lean_is_level_def_eq(v_a_1998_, v_a_1999_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
return v___x_2000_;
}
else
{
v_lhs_1966_ = v_x_1700_;
v_rhs_1967_ = v_x_1701_;
v___y_1968_ = v_a_1702_;
v___y_1969_ = v_a_1703_;
v___y_1970_ = v_a_1704_;
v___y_1971_ = v_a_1705_;
goto v___jp_1965_;
}
}
else
{
v_lhs_1966_ = v_x_1700_;
v_rhs_1967_ = v_x_1701_;
v___y_1968_ = v_a_1702_;
v___y_1969_ = v_a_1703_;
v___y_1970_ = v_a_1704_;
v___y_1971_ = v_a_1705_;
goto v___jp_1965_;
}
v___jp_1707_:
{
lean_object* v___x_1722_; double v___x_1723_; double v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1722_ = lean_io_get_num_heartbeats();
v___x_1723_ = lean_float_of_nat(v___y_1716_);
v___x_1724_ = lean_float_of_nat(v___x_1722_);
v___x_1725_ = lean_box_float(v___x_1723_);
v___x_1726_ = lean_box_float(v___x_1724_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_a_1721_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
v___x_1729_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1708_, v___y_1719_, v___y_1709_, v___y_1720_, v___y_1714_, v___y_1717_, v___y_1711_, v___y_1713_, v___x_1728_, v___y_1715_, v___y_1712_, v___y_1710_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v___y_1720_);
return v___x_1729_;
}
v___jp_1730_:
{
lean_object* v___x_1745_; double v___x_1746_; double v___x_1747_; double v___x_1748_; double v___x_1749_; double v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1745_ = lean_io_mono_nanos_now();
v___x_1746_ = lean_float_of_nat(v___y_1741_);
v___x_1747_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1748_ = lean_float_div(v___x_1746_, v___x_1747_);
v___x_1749_ = lean_float_of_nat(v___x_1745_);
v___x_1750_ = lean_float_div(v___x_1749_, v___x_1747_);
v___x_1751_ = lean_box_float(v___x_1748_);
v___x_1752_ = lean_box_float(v___x_1750_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_a_1744_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
v___x_1755_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1731_, v___y_1742_, v___y_1732_, v___y_1743_, v___y_1737_, v___y_1739_, v___y_1734_, v___y_1736_, v___x_1754_, v___y_1738_, v___y_1735_, v___y_1733_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v___y_1743_);
return v___x_1755_;
}
v___jp_1756_:
{
lean_object* v_fileName_1779_; lean_object* v_fileMap_1780_; lean_object* v_currNamespace_1781_; lean_object* v_openDecls_1782_; lean_object* v_initHeartbeats_1783_; lean_object* v_maxHeartbeats_1784_; lean_object* v_quotContext_1785_; lean_object* v_currMacroScope_1786_; lean_object* v_cancelTk_x3f_1787_; lean_object* v_inheritedTraceOptions_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1840_; 
v_fileName_1779_ = lean_ctor_get(v_toCold_1773_, 0);
v_fileMap_1780_ = lean_ctor_get(v_toCold_1773_, 1);
v_currNamespace_1781_ = lean_ctor_get(v_toCold_1773_, 4);
v_openDecls_1782_ = lean_ctor_get(v_toCold_1773_, 5);
v_initHeartbeats_1783_ = lean_ctor_get(v_toCold_1773_, 6);
v_maxHeartbeats_1784_ = lean_ctor_get(v_toCold_1773_, 7);
v_quotContext_1785_ = lean_ctor_get(v_toCold_1773_, 8);
v_currMacroScope_1786_ = lean_ctor_get(v_toCold_1773_, 9);
v_cancelTk_x3f_1787_ = lean_ctor_get(v_toCold_1773_, 10);
v_inheritedTraceOptions_1788_ = lean_ctor_get(v_toCold_1773_, 11);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_toCold_1773_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; lean_object* v_unused_1842_; 
v_unused_1841_ = lean_ctor_get(v_toCold_1773_, 3);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_toCold_1773_, 2);
lean_dec(v_unused_1842_);
v___x_1790_ = v_toCold_1773_;
v_isShared_1791_ = v_isSharedCheck_1840_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_inheritedTraceOptions_1788_);
lean_inc(v_cancelTk_x3f_1787_);
lean_inc(v_currMacroScope_1786_);
lean_inc(v_quotContext_1785_);
lean_inc(v_maxHeartbeats_1784_);
lean_inc(v_initHeartbeats_1783_);
lean_inc(v_openDecls_1782_);
lean_inc(v_currNamespace_1781_);
lean_inc(v_fileMap_1780_);
lean_inc(v_fileName_1779_);
lean_dec(v_toCold_1773_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1840_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = l_Lean_maxRecDepth;
v___x_1793_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1760_, v___x_1792_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 3, v___x_1793_);
lean_ctor_set(v___x_1790_, 2, v___y_1760_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_fileName_1779_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_fileMap_1780_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v___y_1760_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v_currNamespace_1781_);
lean_ctor_set(v_reuseFailAlloc_1839_, 5, v_openDecls_1782_);
lean_ctor_set(v_reuseFailAlloc_1839_, 6, v_initHeartbeats_1783_);
lean_ctor_set(v_reuseFailAlloc_1839_, 7, v_maxHeartbeats_1784_);
lean_ctor_set(v_reuseFailAlloc_1839_, 8, v_quotContext_1785_);
lean_ctor_set(v_reuseFailAlloc_1839_, 9, v_currMacroScope_1786_);
lean_ctor_set(v_reuseFailAlloc_1839_, 10, v_cancelTk_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1839_, 11, v_inheritedTraceOptions_1788_);
v___x_1795_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_a_1798_; lean_object* v___x_1799_; lean_object* v_a_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1796_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v_currRecDepth_1774_);
lean_ctor_set(v___x_1796_, 2, v_ref_1775_);
lean_ctor_set_uint16(v___x_1796_, sizeof(void*)*3, v___y_1767_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3 + 2, v_suppressElabErrors_1776_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3 + 3, v_isRecordingDeps_1777_);
v___x_1797_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1763_, v___y_1764_, v___y_1762_, v___x_1796_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref_known(v___x_1796_, 3);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1798_, v___y_1764_, v___y_1762_, v___y_1771_, v___y_1768_);
lean_dec_ref(v___y_1771_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1802_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1772_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_io_mono_nanos_now();
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1764_);
v___x_1804_ = lean_apply_5(v___y_1770_, v___y_1764_, v___y_1762_, v___y_1759_, v___y_1768_, lean_box(0));
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
v___y_1731_ = v___y_1757_;
v___y_1732_ = v___y_1758_;
v___y_1733_ = v___y_1759_;
v___y_1734_ = v___y_1761_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v_a_1800_;
v___y_1737_ = v___y_1765_;
v___y_1738_ = v___y_1764_;
v___y_1739_ = v___y_1766_;
v___y_1740_ = v___y_1768_;
v___y_1741_ = v___x_1803_;
v___y_1742_ = v___y_1769_;
v___y_1743_ = v___y_1772_;
v_a_1744_ = v___x_1810_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1804_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1804_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 0);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v___y_1731_ = v___y_1757_;
v___y_1732_ = v___y_1758_;
v___y_1733_ = v___y_1759_;
v___y_1734_ = v___y_1761_;
v___y_1735_ = v___y_1762_;
v___y_1736_ = v_a_1800_;
v___y_1737_ = v___y_1765_;
v___y_1738_ = v___y_1764_;
v___y_1739_ = v___y_1766_;
v___y_1740_ = v___y_1768_;
v___y_1741_ = v___x_1803_;
v___y_1742_ = v___y_1769_;
v___y_1743_ = v___y_1772_;
v_a_1744_ = v___x_1818_;
goto v___jp_1730_;
}
}
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1764_);
v___x_1822_ = lean_apply_5(v___y_1770_, v___y_1764_, v___y_1762_, v___y_1759_, v___y_1768_, lean_box(0));
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 1);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v___y_1708_ = v___y_1757_;
v___y_1709_ = v___y_1758_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1761_;
v___y_1712_ = v___y_1762_;
v___y_1713_ = v_a_1800_;
v___y_1714_ = v___y_1765_;
v___y_1715_ = v___y_1764_;
v___y_1716_ = v___x_1821_;
v___y_1717_ = v___y_1766_;
v___y_1718_ = v___y_1768_;
v___y_1719_ = v___y_1769_;
v___y_1720_ = v___y_1772_;
v_a_1721_ = v___x_1828_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1831_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1822_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1822_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 0);
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
v___y_1708_ = v___y_1757_;
v___y_1709_ = v___y_1758_;
v___y_1710_ = v___y_1759_;
v___y_1711_ = v___y_1761_;
v___y_1712_ = v___y_1762_;
v___y_1713_ = v_a_1800_;
v___y_1714_ = v___y_1765_;
v___y_1715_ = v___y_1764_;
v___y_1716_ = v___x_1821_;
v___y_1717_ = v___y_1766_;
v___y_1718_ = v___y_1768_;
v___y_1719_ = v___y_1769_;
v___y_1720_ = v___y_1772_;
v_a_1721_ = v___x_1836_;
goto v___jp_1707_;
}
}
}
}
}
}
}
v___jp_1843_:
{
lean_object* v_toCold_1862_; lean_object* v_currRecDepth_1863_; lean_object* v_ref_1864_; uint8_t v_suppressElabErrors_1865_; uint8_t v_isRecordingDeps_1866_; 
v_toCold_1862_ = lean_ctor_get(v___y_1860_, 0);
lean_inc_ref(v_toCold_1862_);
v_currRecDepth_1863_ = lean_ctor_get(v___y_1860_, 1);
lean_inc(v_currRecDepth_1863_);
v_ref_1864_ = lean_ctor_get(v___y_1860_, 2);
lean_inc(v_ref_1864_);
v_suppressElabErrors_1865_ = lean_ctor_get_uint8(v___y_1860_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1866_ = lean_ctor_get_uint8(v___y_1860_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_1860_);
v___y_1757_ = v___y_1844_;
v___y_1758_ = v___y_1845_;
v___y_1759_ = v___y_1846_;
v___y_1760_ = v___y_1847_;
v___y_1761_ = v___y_1848_;
v___y_1762_ = v___y_1849_;
v___y_1763_ = v___y_1850_;
v___y_1764_ = v___y_1851_;
v___y_1765_ = v___y_1852_;
v___y_1766_ = v___y_1853_;
v___y_1767_ = v___y_1854_;
v___y_1768_ = v___y_1855_;
v___y_1769_ = v___y_1856_;
v___y_1770_ = v___y_1857_;
v___y_1771_ = v___y_1858_;
v___y_1772_ = v___y_1859_;
v_toCold_1773_ = v_toCold_1862_;
v_currRecDepth_1774_ = v_currRecDepth_1863_;
v_ref_1775_ = v_ref_1864_;
v_suppressElabErrors_1776_ = v_suppressElabErrors_1865_;
v_isRecordingDeps_1777_ = v_isRecordingDeps_1866_;
v___y_1778_ = v___y_1861_;
goto v___jp_1756_;
}
v___jp_1867_:
{
lean_object* v___x_1885_; lean_object* v_env_1886_; lean_object* v_nextMacroScope_1887_; lean_object* v_ngen_1888_; lean_object* v_auxDeclNGen_1889_; lean_object* v_traceState_1890_; lean_object* v_recordedDeps_1891_; lean_object* v_messages_1892_; lean_object* v_infoState_1893_; lean_object* v_snapshotTasks_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1904_; 
v___x_1885_ = lean_st_ref_take(v___y_1880_);
v_env_1886_ = lean_ctor_get(v___x_1885_, 0);
v_nextMacroScope_1887_ = lean_ctor_get(v___x_1885_, 1);
v_ngen_1888_ = lean_ctor_get(v___x_1885_, 2);
v_auxDeclNGen_1889_ = lean_ctor_get(v___x_1885_, 3);
v_traceState_1890_ = lean_ctor_get(v___x_1885_, 4);
v_recordedDeps_1891_ = lean_ctor_get(v___x_1885_, 6);
v_messages_1892_ = lean_ctor_get(v___x_1885_, 7);
v_infoState_1893_ = lean_ctor_get(v___x_1885_, 8);
v_snapshotTasks_1894_ = lean_ctor_get(v___x_1885_, 9);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v___x_1885_, 5);
lean_dec(v_unused_1905_);
v___x_1896_ = v___x_1885_;
v_isShared_1897_ = v_isSharedCheck_1904_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snapshotTasks_1894_);
lean_inc(v_infoState_1893_);
lean_inc(v_messages_1892_);
lean_inc(v_recordedDeps_1891_);
lean_inc(v_traceState_1890_);
lean_inc(v_auxDeclNGen_1889_);
lean_inc(v_ngen_1888_);
lean_inc(v_nextMacroScope_1887_);
lean_inc(v_env_1886_);
lean_dec(v___x_1885_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1904_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = l_Lean_Kernel_enableDiag(v_env_1886_, v___y_1868_);
v___x_1899_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 5, v___x_1899_);
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1901_ = v___x_1896_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_nextMacroScope_1887_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_ngen_1888_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_auxDeclNGen_1889_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_traceState_1890_);
lean_ctor_set(v_reuseFailAlloc_1903_, 5, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1903_, 6, v_recordedDeps_1891_);
lean_ctor_set(v_reuseFailAlloc_1903_, 7, v_messages_1892_);
lean_ctor_set(v_reuseFailAlloc_1903_, 8, v_infoState_1893_);
lean_ctor_set(v_reuseFailAlloc_1903_, 9, v_snapshotTasks_1894_);
v___x_1901_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_st_ref_put(v___y_1880_, v___x_1901_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1880_);
v___y_1844_ = v___y_1869_;
v___y_1845_ = v___y_1870_;
v___y_1846_ = v___y_1871_;
v___y_1847_ = v___y_1872_;
v___y_1848_ = v___y_1873_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1877_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1881_;
v___y_1857_ = v___y_1883_;
v___y_1858_ = v___y_1884_;
v___y_1859_ = v___y_1882_;
v___y_1860_ = v___y_1884_;
v___y_1861_ = v___y_1880_;
goto v___jp_1843_;
}
}
}
v___jp_1906_:
{
if (v___y_1914_ == 0)
{
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1919_);
v___y_1844_ = v___y_1907_;
v___y_1845_ = v___y_1908_;
v___y_1846_ = v___y_1909_;
v___y_1847_ = v___y_1910_;
v___y_1848_ = v___y_1911_;
v___y_1849_ = v___y_1912_;
v___y_1850_ = v___y_1913_;
v___y_1851_ = v___y_1915_;
v___y_1852_ = v___y_1916_;
v___y_1853_ = v___y_1917_;
v___y_1854_ = v___y_1918_;
v___y_1855_ = v___y_1919_;
v___y_1856_ = v___y_1920_;
v___y_1857_ = v___y_1922_;
v___y_1858_ = v___y_1921_;
v___y_1859_ = v___y_1923_;
v___y_1860_ = v___y_1921_;
v___y_1861_ = v___y_1919_;
goto v___jp_1843_;
}
else
{
v___y_1868_ = v___y_1924_;
v___y_1869_ = v___y_1907_;
v___y_1870_ = v___y_1908_;
v___y_1871_ = v___y_1909_;
v___y_1872_ = v___y_1910_;
v___y_1873_ = v___y_1911_;
v___y_1874_ = v___y_1912_;
v___y_1875_ = v___y_1913_;
v___y_1876_ = v___y_1915_;
v___y_1877_ = v___y_1916_;
v___y_1878_ = v___y_1917_;
v___y_1879_ = v___y_1918_;
v___y_1880_ = v___y_1919_;
v___y_1881_ = v___y_1920_;
v___y_1882_ = v___y_1923_;
v___y_1883_ = v___y_1922_;
v___y_1884_ = v___y_1921_;
goto v___jp_1867_;
}
}
v___jp_1925_:
{
lean_object* v___x_1945_; lean_object* v_a_1946_; lean_object* v_ref_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint16_t v___x_1957_; lean_object* v___x_1958_; lean_object* v_env_1959_; uint8_t v___x_1960_; uint16_t v___x_1961_; uint16_t v___x_1962_; uint16_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1945_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1940_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v_ref_1947_ = l_Lean_replaceRef(v___y_1931_, v___y_1931_);
lean_inc(v_ref_1947_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1936_);
v___x_1948_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1948_, 0, v___y_1936_);
lean_ctor_set(v___x_1948_, 1, v___y_1933_);
lean_ctor_set(v___x_1948_, 2, v_ref_1947_);
lean_ctor_set_uint16(v___x_1948_, sizeof(void*)*3, v___y_1941_);
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*3 + 2, v___y_1939_);
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*3 + 3, v___y_1930_);
v___x_1949_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1950_ = 0;
v___x_1951_ = l_Lean_MessageData_ofLevel(v___y_1932_);
v___x_1952_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_MessageData_ofLevel(v___y_1929_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
lean_inc_ref(v___y_1944_);
v___x_1956_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1944_, v___x_1949_, v___x_1950_);
v___x_1957_ = l_Lean_OptionFlags_ofOptions(v___x_1956_);
v___x_1958_ = lean_st_ref_get(v___y_1940_);
v_env_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_env_1959_);
lean_dec(v___x_1958_);
v___x_1960_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1959_);
lean_dec_ref(v_env_1959_);
v___x_1961_ = 512;
v___x_1962_ = lean_uint16_land(v___x_1957_, v___x_1961_);
v___x_1963_ = 0;
v___x_1964_ = lean_uint16_dec_eq(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
if (v___y_1935_ == 0)
{
lean_dec(v_ref_1947_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1933_);
v___y_1907_ = v___y_1927_;
v___y_1908_ = v___y_1926_;
v___y_1909_ = v___y_1928_;
v___y_1910_ = v___x_1956_;
v___y_1911_ = v___y_1931_;
v___y_1912_ = v___y_1934_;
v___y_1913_ = v___x_1955_;
v___y_1914_ = v___x_1960_;
v___y_1915_ = v___y_1938_;
v___y_1916_ = v___y_1937_;
v___y_1917_ = v_a_1946_;
v___y_1918_ = v___x_1957_;
v___y_1919_ = v___y_1940_;
v___y_1920_ = v___y_1942_;
v___y_1921_ = v___x_1948_;
v___y_1922_ = v___y_1943_;
v___y_1923_ = v___y_1944_;
v___y_1924_ = v___y_1935_;
goto v___jp_1906_;
}
else
{
if (v___x_1960_ == 0)
{
lean_dec(v_ref_1947_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1933_);
v___y_1868_ = v___y_1935_;
v___y_1869_ = v___y_1927_;
v___y_1870_ = v___y_1926_;
v___y_1871_ = v___y_1928_;
v___y_1872_ = v___x_1956_;
v___y_1873_ = v___y_1931_;
v___y_1874_ = v___y_1934_;
v___y_1875_ = v___x_1955_;
v___y_1876_ = v___y_1938_;
v___y_1877_ = v___y_1937_;
v___y_1878_ = v_a_1946_;
v___y_1879_ = v___x_1957_;
v___y_1880_ = v___y_1940_;
v___y_1881_ = v___y_1942_;
v___y_1882_ = v___y_1944_;
v___y_1883_ = v___y_1943_;
v___y_1884_ = v___x_1948_;
goto v___jp_1867_;
}
else
{
lean_inc(v___y_1940_);
v___y_1757_ = v___y_1927_;
v___y_1758_ = v___y_1926_;
v___y_1759_ = v___y_1928_;
v___y_1760_ = v___x_1956_;
v___y_1761_ = v___y_1931_;
v___y_1762_ = v___y_1934_;
v___y_1763_ = v___x_1955_;
v___y_1764_ = v___y_1938_;
v___y_1765_ = v___y_1937_;
v___y_1766_ = v_a_1946_;
v___y_1767_ = v___x_1957_;
v___y_1768_ = v___y_1940_;
v___y_1769_ = v___y_1942_;
v___y_1770_ = v___y_1943_;
v___y_1771_ = v___x_1948_;
v___y_1772_ = v___y_1944_;
v_toCold_1773_ = v___y_1936_;
v_currRecDepth_1774_ = v___y_1933_;
v_ref_1775_ = v_ref_1947_;
v_suppressElabErrors_1776_ = v___y_1939_;
v_isRecordingDeps_1777_ = v___y_1930_;
v___y_1778_ = v___y_1940_;
goto v___jp_1756_;
}
}
}
else
{
lean_dec(v_ref_1947_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1933_);
v___y_1907_ = v___y_1927_;
v___y_1908_ = v___y_1926_;
v___y_1909_ = v___y_1928_;
v___y_1910_ = v___x_1956_;
v___y_1911_ = v___y_1931_;
v___y_1912_ = v___y_1934_;
v___y_1913_ = v___x_1955_;
v___y_1914_ = v___x_1960_;
v___y_1915_ = v___y_1938_;
v___y_1916_ = v___y_1937_;
v___y_1917_ = v_a_1946_;
v___y_1918_ = v___x_1957_;
v___y_1919_ = v___y_1940_;
v___y_1920_ = v___y_1942_;
v___y_1921_ = v___x_1948_;
v___y_1922_ = v___y_1943_;
v___y_1923_ = v___y_1944_;
v___y_1924_ = v___x_1950_;
goto v___jp_1906_;
}
}
v___jp_1965_:
{
lean_object* v_toCold_1972_; lean_object* v_options_1973_; lean_object* v_currRecDepth_1974_; lean_object* v_ref_1975_; uint16_t v_optionFlags_1976_; uint8_t v_suppressElabErrors_1977_; uint8_t v_isRecordingDeps_1978_; lean_object* v_inheritedTraceOptions_1979_; uint8_t v_hasTrace_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___y_1989_; 
v_toCold_1972_ = lean_ctor_get(v___y_1970_, 0);
v_options_1973_ = lean_ctor_get(v_toCold_1972_, 2);
v_currRecDepth_1974_ = lean_ctor_get(v___y_1970_, 1);
v_ref_1975_ = lean_ctor_get(v___y_1970_, 2);
v_optionFlags_1976_ = lean_ctor_get_uint16(v___y_1970_, sizeof(void*)*3);
v_suppressElabErrors_1977_ = lean_ctor_get_uint8(v___y_1970_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1978_ = lean_ctor_get_uint8(v___y_1970_, sizeof(void*)*3 + 3);
v_inheritedTraceOptions_1979_ = lean_ctor_get(v_toCold_1972_, 11);
v_hasTrace_1980_ = lean_ctor_get_uint8(v_options_1973_, sizeof(void*)*1);
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1982_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1983_ = l_Lean_Level_getLevelOffset(v_lhs_1966_);
v___x_1984_ = l_Lean_Level_getLevelOffset(v_rhs_1967_);
v___x_1985_ = lean_level_eq(v___x_1983_, v___x_1984_);
lean_dec(v___x_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = 1;
v___x_1987_ = lean_box(v___x_1985_);
v___x_1988_ = lean_box(v___x_1986_);
lean_inc(v_rhs_1967_);
lean_inc(v_lhs_1966_);
v___y_1989_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1989_, 0, v___x_1987_);
lean_closure_set(v___y_1989_, 1, v___x_1981_);
lean_closure_set(v___y_1989_, 2, v___x_1982_);
lean_closure_set(v___y_1989_, 3, v_lhs_1966_);
lean_closure_set(v___y_1989_, 4, v_rhs_1967_);
lean_closure_set(v___y_1989_, 5, v___x_1988_);
if (v_hasTrace_1980_ == 0)
{
lean_object* v___x_1990_; 
lean_dec_ref(v___y_1989_);
v___x_1990_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1985_, v___x_1981_, v___x_1982_, v_lhs_1966_, v_rhs_1967_, v___x_1986_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1991_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1992_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1993_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1979_, v_options_1973_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = l_Lean_trace_profiler;
v___x_1996_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_options_1973_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v___y_1989_);
v___x_1997_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1985_, v___x_1981_, v___x_1982_, v_lhs_1966_, v_rhs_1967_, v___x_1986_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v___x_1997_;
}
else
{
lean_inc(v_ref_1975_);
lean_inc(v_currRecDepth_1974_);
lean_inc_ref(v_options_1973_);
lean_inc_ref(v_toCold_1972_);
v___y_1926_ = v___x_1992_;
v___y_1927_ = v___x_1991_;
v___y_1928_ = v___y_1970_;
v___y_1929_ = v_rhs_1967_;
v___y_1930_ = v_isRecordingDeps_1978_;
v___y_1931_ = v_ref_1975_;
v___y_1932_ = v_lhs_1966_;
v___y_1933_ = v_currRecDepth_1974_;
v___y_1934_ = v___y_1969_;
v___y_1935_ = v_hasTrace_1980_;
v___y_1936_ = v_toCold_1972_;
v___y_1937_ = v___x_1994_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v_suppressElabErrors_1977_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v_optionFlags_1976_;
v___y_1942_ = v___x_1986_;
v___y_1943_ = v___y_1989_;
v___y_1944_ = v_options_1973_;
goto v___jp_1925_;
}
}
else
{
lean_inc(v_ref_1975_);
lean_inc(v_currRecDepth_1974_);
lean_inc_ref(v_options_1973_);
lean_inc_ref(v_toCold_1972_);
v___y_1926_ = v___x_1992_;
v___y_1927_ = v___x_1991_;
v___y_1928_ = v___y_1970_;
v___y_1929_ = v_rhs_1967_;
v___y_1930_ = v_isRecordingDeps_1978_;
v___y_1931_ = v_ref_1975_;
v___y_1932_ = v_lhs_1966_;
v___y_1933_ = v_currRecDepth_1974_;
v___y_1934_ = v___y_1969_;
v___y_1935_ = v_hasTrace_1980_;
v___y_1936_ = v_toCold_1972_;
v___y_1937_ = v___x_1994_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v_suppressElabErrors_1977_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v_optionFlags_1976_;
v___y_1942_ = v___x_1986_;
v___y_1943_ = v___y_1989_;
v___y_1944_ = v_options_1973_;
goto v___jp_1925_;
}
}
}
}
}
LEAN_EXPORT void lean_is_level_def_eq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1700_ = stack[0].m_obj;
lean_object* v_x_1701_ = stack[1].m_obj;
lean_object* v_a_1702_ = stack[2].m_obj;
lean_object* v_a_1703_ = stack[3].m_obj;
lean_object* v_a_1704_ = stack[4].m_obj;
lean_object* v_a_1705_ = stack[5].m_obj;
lean_object* v_res_2001_;
v_res_2001_ = lean_is_level_def_eq(v_x_1700_, v_x_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
stack->m_obj
 = v_res_2001_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = lean_is_level_def_eq(v_x_2002_, v_x_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
return v_res_2009_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_2010_, lean_object* v_x_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_2011_);
return v___x_2017_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2011_ = stack[1].m_obj;
lean_object* v___y_2012_ = stack[2].m_obj;
lean_object* v___y_2013_ = stack[3].m_obj;
lean_object* v___y_2014_ = stack[4].m_obj;
lean_object* v___y_2015_ = stack[5].m_obj;
lean_object* v_res_2018_;
v_res_2018_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_box(0), v_x_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
stack->m_obj
 = v_res_2018_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_x_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_2019_, v_x_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2083_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2084_ = 0;
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2086_ = l_Lean_registerTraceClass(v___x_2083_, v___x_2084_, v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2086_, 1);
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2088_ = 1;
v___x_2089_ = l_Lean_registerTraceClass(v___x_2087_, v___x_2088_, v___x_2085_);
return v___x_2089_;
}
else
{
return v___x_2086_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2090_;
v_res_2090_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2092_;
}
}
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasAssignableMVar(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LevelDefEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
