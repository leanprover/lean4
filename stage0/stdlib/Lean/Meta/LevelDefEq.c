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
lean_dec_ref_known(v_x_26_, 2);
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
lean_dec_ref_known(v_x_26_, 1);
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
lean_object* v___f_47_; lean_object* v___x_952__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_952__overap_48_ = lean_panic_fn_borrowed(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_952__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(lean_object* v_x_93_, size_t v_x_94_, size_t v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_es_98_; size_t v___x_99_; size_t v___x_100_; lean_object* v_j_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_es_98_ = lean_ctor_get(v_x_93_, 0);
v___x_99_ = ((size_t)31ULL);
v___x_100_ = lean_usize_land(v_x_94_, v___x_99_);
v_j_101_ = lean_usize_to_nat(v___x_100_);
v___x_102_ = lean_array_get_size(v_es_98_);
v___x_103_ = lean_nat_dec_lt(v_j_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec(v_j_101_);
lean_dec(v_x_97_);
lean_dec(v_x_96_);
return v_x_93_;
}
else
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_142_; 
lean_inc_ref(v_es_98_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_x_93_, 0);
lean_dec(v_unused_143_);
v___x_105_ = v_x_93_;
v_isShared_106_ = v_isSharedCheck_142_;
goto v_resetjp_104_;
}
else
{
lean_dec(v_x_93_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_142_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_v_107_; lean_object* v___x_108_; lean_object* v_xs_x27_109_; lean_object* v___y_111_; 
v_v_107_ = lean_array_fget(v_es_98_, v_j_101_);
v___x_108_ = lean_box(0);
v_xs_x27_109_ = lean_array_fset(v_es_98_, v_j_101_, v___x_108_);
switch(lean_obj_tag(v_v_107_))
{
case 0:
{
lean_object* v_key_116_; lean_object* v_val_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_127_; 
v_key_116_ = lean_ctor_get(v_v_107_, 0);
v_val_117_ = lean_ctor_get(v_v_107_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_v_107_);
if (v_isSharedCheck_127_ == 0)
{
v___x_119_ = v_v_107_;
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_val_117_);
lean_inc(v_key_116_);
lean_dec(v_v_107_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint8_t v___x_121_; 
v___x_121_ = l_Lean_instBEqLevelMVarId_beq(v_x_96_, v_key_116_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_del_object(v___x_119_);
v___x_122_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_116_, v_val_117_, v_x_96_, v_x_97_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
v___y_111_ = v___x_123_;
goto v___jp_110_;
}
else
{
lean_object* v___x_125_; 
lean_dec(v_val_117_);
lean_dec(v_key_116_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v_x_97_);
lean_ctor_set(v___x_119_, 0, v_x_96_);
v___x_125_ = v___x_119_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_x_96_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_x_97_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
v___y_111_ = v___x_125_;
goto v___jp_110_;
}
}
}
}
case 1:
{
lean_object* v_node_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_140_; 
v_node_128_ = lean_ctor_get(v_v_107_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_v_107_);
if (v_isSharedCheck_140_ == 0)
{
v___x_130_ = v_v_107_;
v_isShared_131_ = v_isSharedCheck_140_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_node_128_);
lean_dec(v_v_107_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_140_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_132_ = ((size_t)5ULL);
v___x_133_ = lean_usize_shift_right(v_x_94_, v___x_132_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_add(v_x_95_, v___x_134_);
v___x_136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_node_128_, v___x_133_, v___x_135_, v_x_96_, v_x_97_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_136_);
v___x_138_ = v___x_130_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v___y_111_ = v___x_138_;
goto v___jp_110_;
}
}
}
default: 
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_x_96_);
lean_ctor_set(v___x_141_, 1, v_x_97_);
v___y_111_ = v___x_141_;
goto v___jp_110_;
}
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_array_fset(v_xs_x27_109_, v_j_101_, v___y_111_);
lean_dec(v_j_101_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_112_);
v___x_114_ = v___x_105_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
else
{
lean_object* v_ks_144_; lean_object* v_vs_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_163_; 
v_ks_144_ = lean_ctor_get(v_x_93_, 0);
v_vs_145_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_163_ == 0)
{
v___x_147_ = v_x_93_;
v_isShared_148_ = v_isSharedCheck_163_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_vs_145_);
lean_inc(v_ks_144_);
lean_dec(v_x_93_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_163_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_ks_144_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_vs_145_);
v___x_150_ = v_reuseFailAlloc_162_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v_newNode_151_; size_t v___x_152_; uint8_t v___x_153_; 
v_newNode_151_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v___x_150_, v_x_96_, v_x_97_);
v___x_152_ = ((size_t)7ULL);
v___x_153_ = lean_usize_dec_le(v___x_152_, v_x_95_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_151_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v_ks_157_; lean_object* v_vs_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_ks_157_ = lean_ctor_get(v_newNode_151_, 0);
lean_inc_ref(v_ks_157_);
v_vs_158_ = lean_ctor_get(v_newNode_151_, 1);
lean_inc_ref(v_vs_158_);
lean_dec_ref(v_newNode_151_);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_x_95_, v_ks_157_, v_vs_158_, v___x_159_, v___x_160_);
lean_dec_ref(v_vs_158_);
lean_dec_ref(v_ks_157_);
return v___x_161_;
}
else
{
return v_newNode_151_;
}
}
else
{
return v_newNode_151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(size_t v_depth_164_, lean_object* v_keys_165_, lean_object* v_vals_166_, lean_object* v_i_167_, lean_object* v_entries_168_){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_array_get_size(v_keys_165_);
v___x_170_ = lean_nat_dec_lt(v_i_167_, v___x_169_);
if (v___x_170_ == 0)
{
lean_dec(v_i_167_);
return v_entries_168_;
}
else
{
lean_object* v_k_171_; lean_object* v_v_172_; uint64_t v___x_173_; size_t v_h_174_; size_t v___x_175_; lean_object* v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v_h_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_k_171_ = lean_array_fget_borrowed(v_keys_165_, v_i_167_);
v_v_172_ = lean_array_fget_borrowed(v_vals_166_, v_i_167_);
v___x_173_ = l_Lean_instHashableLevelMVarId_hash(v_k_171_);
v_h_174_ = lean_uint64_to_usize(v___x_173_);
v___x_175_ = ((size_t)5ULL);
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_sub(v_depth_164_, v___x_177_);
v___x_179_ = lean_usize_mul(v___x_175_, v___x_178_);
v_h_180_ = lean_usize_shift_right(v_h_174_, v___x_179_);
v___x_181_ = lean_nat_add(v_i_167_, v___x_176_);
lean_dec(v_i_167_);
lean_inc(v_v_172_);
lean_inc(v_k_171_);
v___x_182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_entries_168_, v_h_180_, v_depth_164_, v_k_171_, v_v_172_);
v_i_167_ = v___x_181_;
v_entries_168_ = v___x_182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_184_, lean_object* v_keys_185_, lean_object* v_vals_186_, lean_object* v_i_187_, lean_object* v_entries_188_){
_start:
{
size_t v_depth_boxed_189_; lean_object* v_res_190_; 
v_depth_boxed_189_ = lean_unbox_usize(v_depth_184_);
lean_dec(v_depth_184_);
v_res_190_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_boxed_189_, v_keys_185_, v_vals_186_, v_i_187_, v_entries_188_);
lean_dec_ref(v_vals_186_);
lean_dec_ref(v_keys_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
size_t v_x_2701__boxed_196_; size_t v_x_2702__boxed_197_; lean_object* v_res_198_; 
v_x_2701__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_x_2702__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_191_, v_x_2701__boxed_196_, v_x_2702__boxed_197_, v_x_194_, v_x_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint64_t v___x_202_; size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; 
v___x_202_ = l_Lean_instHashableLevelMVarId_hash(v_x_200_);
v___x_203_ = lean_uint64_to_usize(v___x_202_);
v___x_204_ = ((size_t)1ULL);
v___x_205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_199_, v___x_203_, v___x_204_, v_x_200_, v_x_201_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object* v_mvarId_206_, lean_object* v_val_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v_mctx_211_; lean_object* v_cache_212_; lean_object* v_zetaDeltaFVarIds_213_; lean_object* v_postponed_214_; lean_object* v_diag_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_245_; 
v___x_210_ = lean_st_ref_take(v___y_208_);
v_mctx_211_ = lean_ctor_get(v___x_210_, 0);
v_cache_212_ = lean_ctor_get(v___x_210_, 1);
v_zetaDeltaFVarIds_213_ = lean_ctor_get(v___x_210_, 2);
v_postponed_214_ = lean_ctor_get(v___x_210_, 3);
v_diag_215_ = lean_ctor_get(v___x_210_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_245_ == 0)
{
v___x_217_ = v___x_210_;
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_diag_215_);
lean_inc(v_postponed_214_);
lean_inc(v_zetaDeltaFVarIds_213_);
lean_inc(v_cache_212_);
lean_inc(v_mctx_211_);
lean_dec(v___x_210_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_depth_219_; lean_object* v_levelAssignDepth_220_; lean_object* v_lmvarCounter_221_; lean_object* v_mvarCounter_222_; lean_object* v_lDecls_223_; lean_object* v_decls_224_; lean_object* v_userNames_225_; lean_object* v_lAssignment_226_; lean_object* v_eAssignment_227_; lean_object* v_dAssignment_228_; lean_object* v_instanceTypedMVars_229_; lean_object* v_synthNormMemo_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_depth_219_ = lean_ctor_get(v_mctx_211_, 0);
v_levelAssignDepth_220_ = lean_ctor_get(v_mctx_211_, 1);
v_lmvarCounter_221_ = lean_ctor_get(v_mctx_211_, 2);
v_mvarCounter_222_ = lean_ctor_get(v_mctx_211_, 3);
v_lDecls_223_ = lean_ctor_get(v_mctx_211_, 4);
v_decls_224_ = lean_ctor_get(v_mctx_211_, 5);
v_userNames_225_ = lean_ctor_get(v_mctx_211_, 6);
v_lAssignment_226_ = lean_ctor_get(v_mctx_211_, 7);
v_eAssignment_227_ = lean_ctor_get(v_mctx_211_, 8);
v_dAssignment_228_ = lean_ctor_get(v_mctx_211_, 9);
v_instanceTypedMVars_229_ = lean_ctor_get(v_mctx_211_, 10);
v_synthNormMemo_230_ = lean_ctor_get(v_mctx_211_, 11);
v_isSharedCheck_244_ = !lean_is_exclusive(v_mctx_211_);
if (v_isSharedCheck_244_ == 0)
{
v___x_232_ = v_mctx_211_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_synthNormMemo_230_);
lean_inc(v_instanceTypedMVars_229_);
lean_inc(v_dAssignment_228_);
lean_inc(v_eAssignment_227_);
lean_inc(v_lAssignment_226_);
lean_inc(v_userNames_225_);
lean_inc(v_decls_224_);
lean_inc(v_lDecls_223_);
lean_inc(v_mvarCounter_222_);
lean_inc(v_lmvarCounter_221_);
lean_inc(v_levelAssignDepth_220_);
lean_inc(v_depth_219_);
lean_dec(v_mctx_211_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = lean_box(0);
v___x_235_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_226_, v_mvarId_206_, v_val_207_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 7, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_depth_219_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_levelAssignDepth_220_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_lmvarCounter_221_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_mvarCounter_222_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_lDecls_223_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_decls_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_userNames_225_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v_eAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 9, v_dAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 10, v_instanceTypedMVars_229_);
lean_ctor_set(v_reuseFailAlloc_243_, 11, v_synthNormMemo_230_);
v___x_237_ = v_reuseFailAlloc_243_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_237_);
v___x_239_ = v___x_217_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_zetaDeltaFVarIds_213_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_postponed_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_diag_215_);
v___x_239_ = v_reuseFailAlloc_242_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_st_ref_put(v___y_208_, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_234_);
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_246_, v_val_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object* v_msgData_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_env_258_; uint8_t v___x_259_; lean_object* v_env_260_; lean_object* v___x_261_; lean_object* v_toCold_262_; lean_object* v_mctx_263_; lean_object* v_lctx_264_; lean_object* v_options_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_257_ = lean_st_ref_get(v___y_255_);
v_env_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_env_258_);
lean_dec(v___x_257_);
v___x_259_ = 0;
v_env_260_ = l_Lean_Environment_setRecordingDeps(v_env_258_, v___x_259_);
v___x_261_ = lean_st_ref_get(v___y_253_);
v_toCold_262_ = lean_ctor_get(v___y_254_, 0);
v_mctx_263_ = lean_ctor_get(v___x_261_, 0);
lean_inc_ref(v_mctx_263_);
lean_dec(v___x_261_);
v_lctx_264_ = lean_ctor_get(v___y_252_, 2);
v_options_265_ = lean_ctor_get(v_toCold_262_, 2);
lean_inc_ref(v_options_265_);
lean_inc_ref(v_lctx_264_);
v___x_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_266_, 0, v_env_260_);
lean_ctor_set(v___x_266_, 1, v_mctx_263_);
lean_ctor_set(v___x_266_, 2, v_lctx_264_);
lean_ctor_set(v___x_266_, 3, v_options_265_);
v___x_267_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_msgData_251_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_276_; double v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_float_of_nat(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_281_, lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_ref_288_; lean_object* v___x_289_; lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_335_; 
v_ref_288_ = lean_ctor_get(v___y_285_, 2);
v___x_289_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_335_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_335_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_335_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v_traceState_295_; lean_object* v_env_296_; lean_object* v_nextMacroScope_297_; lean_object* v_ngen_298_; lean_object* v_auxDeclNGen_299_; lean_object* v_cache_300_; lean_object* v_recordedDeps_301_; lean_object* v_messages_302_; lean_object* v_infoState_303_; lean_object* v_snapshotTasks_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_334_; 
v___x_294_ = lean_st_ref_take(v___y_286_);
v_traceState_295_ = lean_ctor_get(v___x_294_, 4);
v_env_296_ = lean_ctor_get(v___x_294_, 0);
v_nextMacroScope_297_ = lean_ctor_get(v___x_294_, 1);
v_ngen_298_ = lean_ctor_get(v___x_294_, 2);
v_auxDeclNGen_299_ = lean_ctor_get(v___x_294_, 3);
v_cache_300_ = lean_ctor_get(v___x_294_, 5);
v_recordedDeps_301_ = lean_ctor_get(v___x_294_, 6);
v_messages_302_ = lean_ctor_get(v___x_294_, 7);
v_infoState_303_ = lean_ctor_get(v___x_294_, 8);
v_snapshotTasks_304_ = lean_ctor_get(v___x_294_, 9);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_334_ == 0)
{
v___x_306_ = v___x_294_;
v_isShared_307_ = v_isSharedCheck_334_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_snapshotTasks_304_);
lean_inc(v_infoState_303_);
lean_inc(v_messages_302_);
lean_inc(v_recordedDeps_301_);
lean_inc(v_cache_300_);
lean_inc(v_traceState_295_);
lean_inc(v_auxDeclNGen_299_);
lean_inc(v_ngen_298_);
lean_inc(v_nextMacroScope_297_);
lean_inc(v_env_296_);
lean_dec(v___x_294_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_334_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint64_t v_tid_308_; lean_object* v_traces_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_333_; 
v_tid_308_ = lean_ctor_get_uint64(v_traceState_295_, sizeof(void*)*1);
v_traces_309_ = lean_ctor_get(v_traceState_295_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_traceState_295_);
if (v_isSharedCheck_333_ == 0)
{
v___x_311_ = v_traceState_295_;
v_isShared_312_ = v_isSharedCheck_333_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_traces_309_);
lean_dec(v_traceState_295_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_333_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; double v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_313_ = lean_box(0);
v___x_314_ = lean_box(0);
v___x_315_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_316_ = 0;
v___x_317_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_318_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_318_, 0, v_cls_281_);
lean_ctor_set(v___x_318_, 1, v___x_314_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set_float(v___x_318_, sizeof(void*)*3, v___x_315_);
lean_ctor_set_float(v___x_318_, sizeof(void*)*3 + 8, v___x_315_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*3 + 16, v___x_316_);
v___x_319_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_320_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v_a_290_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
lean_inc(v_ref_288_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_ref_288_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_PersistentArray_push___redArg(v_traces_309_, v___x_321_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_322_);
v___x_324_ = v___x_311_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_322_);
lean_ctor_set_uint64(v_reuseFailAlloc_332_, sizeof(void*)*1, v_tid_308_);
v___x_324_ = v_reuseFailAlloc_332_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 4, v___x_324_);
v___x_326_ = v___x_306_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_env_296_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_nextMacroScope_297_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_ngen_298_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_auxDeclNGen_299_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_cache_300_);
lean_ctor_set(v_reuseFailAlloc_331_, 6, v_recordedDeps_301_);
lean_ctor_set(v_reuseFailAlloc_331_, 7, v_messages_302_);
lean_ctor_set(v_reuseFailAlloc_331_, 8, v_infoState_303_);
lean_ctor_set(v_reuseFailAlloc_331_, 9, v_snapshotTasks_304_);
v___x_326_ = v_reuseFailAlloc_331_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_st_ref_put(v___y_286_, v___x_326_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_313_);
v___x_329_ = v___x_292_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_313_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_336_, v_msg_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_343_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_348_ = lean_unsigned_to_nat(2u);
v___x_349_ = lean_unsigned_to_nat(39u);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_352_ = l_mkPanicMessageWithDecl(v___x_351_, v___x_350_, v___x_349_, v___x_348_, v___x_347_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_365_ = l_Lean_Name_append(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_372_, lean_object* v_v_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = l_Lean_Level_isMax(v_v_373_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_v_373_);
lean_dec(v_mvarId_372_);
v___x_380_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_381_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_380_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_mkFreshLevelMVar(v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_toCold_383_; lean_object* v_options_384_; lean_object* v_a_385_; lean_object* v_inheritedTraceOptions_386_; uint8_t v_hasTrace_387_; lean_object* v___x_388_; 
v_toCold_383_ = lean_ctor_get(v_a_376_, 0);
v_options_384_ = lean_ctor_get(v_toCold_383_, 2);
v_a_385_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_382_, 1);
v_inheritedTraceOptions_386_ = lean_ctor_get(v_toCold_383_, 11);
v_hasTrace_387_ = lean_ctor_get_uint8(v_options_384_, sizeof(void*)*1);
v___x_388_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_372_, v_v_373_, v_a_385_);
if (v_hasTrace_387_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_372_, v___x_388_, v_a_375_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_386_, v_options_384_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_372_, v___x_388_, v_a_375_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_372_);
v___x_395_ = l_Lean_mkLevelMVar(v_mvarId_372_);
v___x_396_ = l_Lean_MessageData_ofLevel(v___x_395_);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_394_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_inc(v___x_388_);
v___x_400_ = l_Lean_MessageData_ofLevel(v___x_388_);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_390_, v___x_401_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_403_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_372_, v___x_388_, v_a_375_);
return v___x_403_;
}
else
{
lean_dec(v___x_388_);
lean_dec(v_mvarId_372_);
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_v_373_);
lean_dec(v_mvarId_372_);
v_a_404_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_382_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_382_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_412_, lean_object* v_v_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_412_, v_v_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_420_, lean_object* v_val_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_420_, v_val_421_, v___y_423_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_428_, lean_object* v_val_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_428_, v_val_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_437_, v_x_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_441_, lean_object* v_x_442_, size_t v_x_443_, size_t v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_442_, v_x_443_, v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
size_t v_x_3211__boxed_454_; size_t v_x_3212__boxed_455_; lean_object* v_res_456_; 
v_x_3211__boxed_454_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_x_3212__boxed_455_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_res_456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_448_, v_x_449_, v_x_3211__boxed_454_, v_x_3212__boxed_455_, v_x_452_, v_x_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_457_, lean_object* v_n_458_, lean_object* v_k_459_, lean_object* v_v_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_458_, v_k_459_, v_v_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_462_, size_t v_depth_463_, lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_heq_466_, lean_object* v_i_467_, lean_object* v_entries_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_463_, v_keys_464_, v_vals_465_, v_i_467_, v_entries_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_470_, lean_object* v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_heq_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
size_t v_depth_boxed_477_; lean_object* v_res_478_; 
v_depth_boxed_477_ = lean_unbox_usize(v_depth_471_);
lean_dec(v_depth_471_);
v_res_478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_470_, v_depth_boxed_477_, v_keys_472_, v_vals_473_, v_heq_474_, v_i_475_, v_entries_476_);
lean_dec_ref(v_vals_473_);
lean_dec_ref(v_keys_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_480_, v_x_481_, v_x_482_, v_x_483_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_488_, lean_object* v_v_x27_489_, lean_object* v_mvarId_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
uint8_t v___x_496_; lean_object* v___y_498_; 
v___x_496_ = lean_level_eq(v_u_488_, v_v_x27_489_);
if (v___x_496_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_mvarId_490_);
lean_dec(v_u_488_);
v___x_509_ = lean_box(v___x_496_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_toCold_511_; lean_object* v_options_512_; uint8_t v_hasTrace_513_; 
v_toCold_511_ = lean_ctor_get(v_a_493_, 0);
v_options_512_ = lean_ctor_get(v_toCold_511_, 2);
v_hasTrace_513_ = lean_ctor_get_uint8(v_options_512_, sizeof(void*)*1);
if (v_hasTrace_513_ == 0)
{
v___y_498_ = v_a_492_;
goto v___jp_497_;
}
else
{
lean_object* v_inheritedTraceOptions_514_; lean_object* v_cls_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_inheritedTraceOptions_514_ = lean_ctor_get(v_toCold_511_, 11);
v_cls_515_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_516_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_514_, v_options_512_, v___x_516_);
if (v___x_517_ == 0)
{
v___y_498_ = v_a_492_;
goto v___jp_497_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_518_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_490_);
v___x_519_ = l_Lean_mkLevelMVar(v_mvarId_490_);
v___x_520_ = l_Lean_MessageData_ofLevel(v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_inc(v_u_488_);
v___x_524_ = l_Lean_MessageData_ofLevel(v_u_488_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_515_, v___x_525_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_dec_ref_known(v___x_526_, 1);
v___y_498_ = v_a_492_;
goto v___jp_497_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_mvarId_490_);
lean_dec(v_u_488_);
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
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v___x_499_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_490_, v_u_488_, v___y_498_);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_499_, 0);
lean_dec(v_unused_508_);
v___x_501_ = v___x_499_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_dec(v___x_499_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_box(v___x_496_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
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
lean_dec_ref_known(v_v_545_, 2);
v_a_557_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v_a_555_, 1);
v___x_558_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_544_, v_a_556_, v_a_557_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_556_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v_v_545_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v_v_545_, 2);
if (lean_obj_tag(v_a_559_) == 5)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v_a_559_, 1);
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
lean_object* v_toCold_611_; lean_object* v_options_612_; uint8_t v_hasTrace_613_; 
v_toCold_611_ = lean_ctor_get(v_a_579_, 0);
v_options_612_ = lean_ctor_get(v_toCold_611_, 2);
v_hasTrace_613_ = lean_ctor_get_uint8(v_options_612_, sizeof(void*)*1);
if (v_hasTrace_613_ == 0)
{
v___y_597_ = v_a_578_;
goto v___jp_596_;
}
else
{
lean_object* v_inheritedTraceOptions_614_; lean_object* v_cls_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_inheritedTraceOptions_614_ = lean_ctor_get(v_toCold_611_, 11);
v_cls_615_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_614_, v_options_612_, v___x_616_);
if (v___x_617_ == 0)
{
v___y_597_ = v_a_578_;
goto v___jp_596_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_618_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_576_);
v___x_619_ = l_Lean_mkLevelMVar(v_mvarId_576_);
v___x_620_ = l_Lean_MessageData_ofLevel(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
lean_inc(v_u_u2081_573_);
v___x_624_ = l_Lean_MessageData_ofLevel(v_u_u2081_573_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_615_, v___x_625_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref_known(v___x_626_, 1);
v___y_597_ = v_a_578_;
goto v___jp_596_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_mvarId_576_);
lean_dec(v_u_u2081_573_);
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
lean_object* v_toCold_635_; lean_object* v_options_636_; uint8_t v_hasTrace_637_; 
lean_dec(v_u_u2081_573_);
v_toCold_635_ = lean_ctor_get(v_a_579_, 0);
v_options_636_ = lean_ctor_get(v_toCold_635_, 2);
v_hasTrace_637_ = lean_ctor_get_uint8(v_options_636_, sizeof(void*)*1);
if (v_hasTrace_637_ == 0)
{
v___y_585_ = v_a_578_;
goto v___jp_584_;
}
else
{
lean_object* v_inheritedTraceOptions_638_; lean_object* v_cls_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_inheritedTraceOptions_638_ = lean_ctor_get(v_toCold_635_, 11);
v_cls_639_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_640_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_641_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_638_, v_options_636_, v___x_640_);
if (v___x_641_ == 0)
{
v___y_585_ = v_a_578_;
goto v___jp_584_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_642_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_576_);
v___x_643_ = l_Lean_mkLevelMVar(v_mvarId_576_);
v___x_644_ = l_Lean_MessageData_ofLevel(v___x_643_);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_642_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_inc(v_u_u2082_574_);
v___x_648_ = l_Lean_MessageData_ofLevel(v_u_u2082_574_);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_639_, v___x_649_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_dec_ref_known(v___x_650_, 1);
v___y_585_ = v_a_578_;
goto v___jp_584_;
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_mvarId_576_);
lean_dec(v_u_u2082_574_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_659_, lean_object* v_u_u2082_660_, lean_object* v_v_x27_661_, lean_object* v_mvarId_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_659_, v_u_u2082_660_, v_v_x27_661_, v_mvarId_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_v_x27_661_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_669_, lean_object* v_v_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
if (lean_obj_tag(v_u_669_) == 2)
{
if (lean_obj_tag(v_v_670_) == 2)
{
lean_object* v_a_680_; 
v_a_680_ = lean_ctor_get(v_v_670_, 1);
lean_inc(v_a_680_);
if (lean_obj_tag(v_a_680_) == 5)
{
lean_object* v_a_681_; lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_685_; 
v_a_681_ = lean_ctor_get(v_u_669_, 0);
lean_inc(v_a_681_);
v_a_682_ = lean_ctor_get(v_u_669_, 1);
lean_inc(v_a_682_);
lean_dec_ref_known(v_u_669_, 2);
v_a_683_ = lean_ctor_get(v_v_670_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v_v_670_, 2);
v_a_684_ = lean_ctor_get(v_a_680_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v_a_680_, 1);
v___x_685_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_683_);
return v___x_685_;
}
else
{
lean_object* v_a_686_; 
v_a_686_ = lean_ctor_get(v_v_670_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v_v_670_, 2);
if (lean_obj_tag(v_a_686_) == 5)
{
lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_687_ = lean_ctor_get(v_u_669_, 0);
lean_inc(v_a_687_);
v_a_688_ = lean_ctor_get(v_u_669_, 1);
lean_inc(v_a_688_);
lean_dec_ref_known(v_u_669_, 2);
v_a_689_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v_a_686_, 1);
v___x_690_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_687_, v_a_688_, v_a_680_, v_a_689_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_680_);
return v___x_690_;
}
else
{
lean_dec(v_a_686_);
lean_dec(v_a_680_);
lean_dec_ref_known(v_u_669_, 2);
goto v___jp_676_;
}
}
}
else
{
lean_dec_ref_known(v_u_669_, 2);
lean_dec(v_v_670_);
goto v___jp_676_;
}
}
else
{
lean_dec(v_v_670_);
lean_dec(v_u_669_);
goto v___jp_676_;
}
v___jp_676_:
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = 0;
v___x_678_ = lean_box(v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_691_, lean_object* v_v_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_691_, v_v_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_698_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_706_ = l_Lean_Name_append(v___x_705_, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_710_, lean_object* v_rhs_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_toCold_717_; lean_object* v_ref_718_; lean_object* v___y_720_; lean_object* v_options_740_; uint8_t v_hasTrace_741_; 
v_toCold_717_ = lean_ctor_get(v_a_714_, 0);
v_ref_718_ = lean_ctor_get(v_a_714_, 2);
v_options_740_ = lean_ctor_get(v_toCold_717_, 2);
v_hasTrace_741_ = lean_ctor_get_uint8(v_options_740_, sizeof(void*)*1);
if (v_hasTrace_741_ == 0)
{
v___y_720_ = v_a_713_;
goto v___jp_719_;
}
else
{
lean_object* v_inheritedTraceOptions_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_inheritedTraceOptions_742_ = lean_ctor_get(v_toCold_717_, 11);
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_745_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_742_, v_options_740_, v___x_744_);
if (v___x_745_ == 0)
{
v___y_720_ = v_a_713_;
goto v___jp_719_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc(v_lhs_710_);
v___x_746_ = l_Lean_MessageData_ofLevel(v_lhs_710_);
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
lean_inc(v_rhs_711_);
v___x_749_ = l_Lean_MessageData_ofLevel(v_rhs_711_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_743_, v___x_750_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_dec_ref_known(v___x_751_, 1);
v___y_720_ = v_a_713_;
goto v___jp_719_;
}
else
{
lean_dec(v_rhs_711_);
lean_dec(v_lhs_710_);
return v___x_751_;
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
lean_object* v_defEqCtx_x3f_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v_defEqCtx_x3f_730_ = lean_ctor_get(v_a_712_, 4);
v___x_731_ = lean_box(0);
lean_inc(v_defEqCtx_x3f_730_);
lean_inc(v_ref_718_);
v___x_732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_732_, 0, v_ref_718_);
lean_ctor_set(v___x_732_, 1, v_lhs_710_);
lean_ctor_set(v___x_732_, 2, v_rhs_711_);
lean_ctor_set(v___x_732_, 3, v_defEqCtx_x3f_730_);
v___x_733_ = l_Lean_PersistentArray_push___redArg(v_postponed_725_, v___x_732_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v___x_733_);
v___x_735_ = v___x_728_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_mctx_722_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_cache_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_zetaDeltaFVarIds_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_diag_726_);
v___x_735_ = v_reuseFailAlloc_738_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_st_ref_put(v___y_720_, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_731_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_752_, lean_object* v_rhs_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_752_, v_rhs_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_760_, lean_object* v_mvarId_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
if (lean_obj_tag(v_v_760_) == 5)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v_v_760_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v_v_760_, 1);
v___x_768_ = l_Lean_LMVarId_getLevel(v_a_767_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_LMVarId_getLevel(v_mvarId_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_780_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_780_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_780_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_780_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_775_ = lean_nat_dec_lt(v_a_771_, v_a_769_);
lean_dec(v_a_769_);
lean_dec(v_a_771_);
v___x_776_ = lean_box(v___x_775_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_776_);
v___x_778_ = v___x_773_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_a_769_);
v_a_781_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_770_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_770_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_mvarId_761_);
v_a_789_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_768_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_768_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
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
uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v_mvarId_761_);
lean_dec(v_v_760_);
v___x_797_ = 0;
v___x_798_ = lean_box(v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_800_, lean_object* v_mvarId_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_800_, v_mvarId_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_808_, lean_object* v_v_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___y_816_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_891_; lean_object* v___y_905_; 
switch(lean_obj_tag(v_u_808_))
{
case 5:
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v_u_808_, 0);
lean_inc(v_a_918_);
v___x_919_ = l_Lean_LMVarId_isReadOnly(v_a_918_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_1016_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_1016_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_1016_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint8_t v___x_924_; 
v___x_924_ = lean_unbox(v_a_920_);
lean_dec(v_a_920_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
lean_del_object(v___x_922_);
lean_inc(v_a_918_);
lean_inc(v_v_809_);
v___x_925_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_809_, v_a_918_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_1002_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_1002_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_1002_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
uint8_t v___x_936_; 
v___x_936_ = lean_unbox(v_a_926_);
lean_dec(v_a_926_);
if (v___x_936_ == 0)
{
uint8_t v___x_937_; 
v___x_937_ = l_Lean_Level_occurs(v_u_808_, v_v_809_);
if (v___x_937_ == 0)
{
lean_object* v_toCold_938_; lean_object* v_options_939_; uint8_t v_hasTrace_940_; 
lean_del_object(v___x_928_);
v_toCold_938_ = lean_ctor_get(v_a_812_, 0);
v_options_939_ = lean_ctor_get(v_toCold_938_, 2);
v_hasTrace_940_ = lean_ctor_get_uint8(v_options_939_, sizeof(void*)*1);
if (v_hasTrace_940_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_891_ = v_a_811_;
goto v___jp_890_;
}
else
{
lean_object* v_inheritedTraceOptions_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_inheritedTraceOptions_941_ = lean_ctor_get(v_toCold_938_, 11);
v___x_942_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_941_, v_options_939_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_891_ = v_a_811_;
goto v___jp_890_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc_ref(v_u_808_);
v___x_945_ = l_Lean_MessageData_ofLevel(v_u_808_);
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_inc(v_v_809_);
v___x_948_ = l_Lean_MessageData_ofLevel(v_v_809_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_942_, v___x_949_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_dec_ref_known(v___x_950_, 1);
v___y_891_ = v_a_811_;
goto v___jp_890_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_811_);
lean_dec(v_v_809_);
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
else
{
uint8_t v___x_959_; 
v___x_959_ = l_Lean_Level_isMax(v_v_809_);
if (v___x_959_ == 0)
{
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
goto v___jp_930_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_808_, v_v_809_);
if (v___x_960_ == 0)
{
if (v___x_959_ == 0)
{
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
goto v___jp_930_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_del_object(v___x_928_);
v___x_961_ = l_Lean_Level_mvarId_x21(v_u_808_);
lean_dec_ref_known(v_u_808_, 1);
v___x_962_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_961_, v_v_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_972_);
v___x_964_ = v___x_962_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_dec(v___x_962_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = 1;
v___x_967_ = lean_box(v___x_966_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_962_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_962_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
goto v___jp_930_;
}
}
}
}
else
{
lean_object* v_toCold_981_; lean_object* v_options_982_; uint8_t v_hasTrace_983_; 
lean_del_object(v___x_928_);
v_toCold_981_ = lean_ctor_get(v_a_812_, 0);
v_options_982_ = lean_ctor_get(v_toCold_981_, 2);
v_hasTrace_983_ = lean_ctor_get_uint8(v_options_982_, sizeof(void*)*1);
if (v_hasTrace_983_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_905_ = v_a_811_;
goto v___jp_904_;
}
else
{
lean_object* v_inheritedTraceOptions_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_inheritedTraceOptions_984_ = lean_ctor_get(v_toCold_981_, 11);
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_987_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_984_, v_options_982_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_905_ = v_a_811_;
goto v___jp_904_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc(v_v_809_);
v___x_988_ = l_Lean_MessageData_ofLevel(v_v_809_);
v___x_989_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_inc_ref(v_u_808_);
v___x_991_ = l_Lean_MessageData_ofLevel(v_u_808_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_985_, v___x_992_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_dec_ref_known(v___x_993_, 1);
v___y_905_ = v_a_811_;
goto v___jp_904_;
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_811_);
lean_dec(v_v_809_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
v___jp_930_:
{
uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = 2;
v___x_932_ = lean_box(v___x_931_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_932_);
v___x_934_ = v___x_928_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
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
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v_a_1003_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_925_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_925_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v___x_1011_ = 2;
v___x_1012_ = lean_box(v___x_1011_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_1012_);
v___x_1014_ = v___x_922_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v_a_1017_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_919_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_919_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_809_))
{
case 5:
{
lean_dec_ref_known(v_v_809_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
goto v___jp_886_;
}
case 2:
{
lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v_v_809_, 0);
lean_inc(v_a_1025_);
v_a_1026_ = lean_ctor_get(v_v_809_, 1);
lean_inc(v_a_1026_);
lean_dec_ref_known(v_v_809_, 2);
lean_inc(v_a_813_);
lean_inc_ref(v_a_812_);
lean_inc(v_a_811_);
lean_inc_ref(v_a_810_);
v___x_1027_ = lean_is_level_def_eq(v_u_808_, v_a_1025_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; uint8_t v___x_1029_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v___x_1029_ = lean_unbox(v_a_1028_);
if (v___x_1029_ == 0)
{
lean_dec(v_a_1026_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___y_816_ = v___x_1027_;
goto v___jp_815_;
}
else
{
lean_object* v___x_1030_; 
lean_dec_ref_known(v___x_1027_, 1);
v___x_1030_ = lean_is_level_def_eq(v_u_808_, v_a_1026_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
v___y_816_ = v___x_1030_;
goto v___jp_815_;
}
}
else
{
lean_dec(v_a_1026_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___y_816_ = v___x_1027_;
goto v___jp_815_;
}
}
case 3:
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
v_a_1031_ = lean_ctor_get(v_v_809_, 1);
lean_inc(v_a_1031_);
lean_dec_ref_known(v_v_809_, 2);
v___x_1032_ = lean_is_level_def_eq(v_u_808_, v_a_1031_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1043_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
uint8_t v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1037_ = lean_unbox(v_a_1033_);
lean_dec(v_a_1033_);
v___x_1038_ = l_Lean_Bool_toLBool(v___x_1037_);
v___x_1039_ = lean_box(v___x_1038_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1039_);
v___x_1041_ = v___x_1035_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1032_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1032_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
case 1:
{
uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref_known(v_v_809_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___x_1052_ = 0;
v___x_1053_ = lean_box(v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
default: 
{
v___y_841_ = v_a_810_;
v___y_842_ = v_a_811_;
v___y_843_ = v_a_812_;
v___y_844_ = v_a_813_;
goto v___jp_840_;
}
}
}
case 1:
{
lean_object* v_a_1055_; uint8_t v___y_1057_; 
v_a_1055_ = lean_ctor_get(v_u_808_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v_u_808_, 1);
if (lean_obj_tag(v_v_809_) == 5)
{
lean_dec_ref_known(v_v_809_, 1);
lean_dec(v_a_1055_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
goto v___jp_886_;
}
else
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Level_isParam(v_v_809_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; 
v___x_1102_ = l_Lean_Level_isMVar(v_a_1055_);
if (v___x_1102_ == 0)
{
v___y_1057_ = v___x_1101_;
goto v___jp_1056_;
}
else
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_Level_occurs(v_a_1055_, v_v_809_);
v___y_1057_ = v___x_1103_;
goto v___jp_1056_;
}
}
else
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_a_1055_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v___x_1104_ = 0;
v___x_1105_ = lean_box(v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
v___jp_1056_:
{
if (v___y_1057_ == 0)
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_decLevel_x3f(v_v_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1089_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
if (lean_obj_tag(v_a_1059_) == 0)
{
uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_dec(v_a_1055_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___x_1063_ = 2;
v___x_1064_ = lean_box(v___x_1063_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1069_; 
lean_del_object(v___x_1061_);
v_val_1068_ = lean_ctor_get(v_a_1059_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_a_1059_, 1);
v___x_1069_ = lean_is_level_def_eq(v_a_1055_, v_val_1068_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1080_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1080_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1080_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
uint8_t v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1074_ = lean_unbox(v_a_1070_);
lean_dec(v_a_1070_);
v___x_1075_ = l_Lean_Bool_toLBool(v___x_1074_);
v___x_1076_ = lean_box(v___x_1075_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1076_);
v___x_1078_ = v___x_1072_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_a_1081_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1069_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1069_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1055_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v_a_1090_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1058_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1058_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v_a_1055_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v___x_1098_ = 2;
v___x_1099_ = lean_box(v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_809_) == 5)
{
lean_dec_ref_known(v_v_809_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_u_808_);
goto v___jp_886_;
}
else
{
v___y_841_ = v_a_810_;
v___y_842_ = v_a_811_;
v___y_843_ = v_a_812_;
v___y_844_ = v_a_813_;
goto v___jp_840_;
}
}
}
v___jp_815_:
{
if (lean_obj_tag(v___y_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_827_; 
v_a_817_ = lean_ctor_get(v___y_816_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___y_816_);
if (v_isSharedCheck_827_ == 0)
{
v___x_819_ = v___y_816_;
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___y_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
uint8_t v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_821_ = lean_unbox(v_a_817_);
lean_dec(v_a_817_);
v___x_822_ = l_Lean_Bool_toLBool(v___x_821_);
v___x_823_ = lean_box(v___x_822_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_a_828_ = lean_ctor_get(v___y_816_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___y_816_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___y_816_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___y_816_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
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
v___jp_836_:
{
uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = 2;
v___x_838_ = lean_box(v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
v___jp_840_:
{
uint8_t v_univApprox_845_; 
v_univApprox_845_ = lean_ctor_get_uint8(v___y_841_, sizeof(void*)*7 + 1);
if (v_univApprox_845_ == 0)
{
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v_v_809_);
lean_dec(v_u_808_);
goto v___jp_836_;
}
else
{
lean_object* v___x_846_; 
lean_inc(v_v_809_);
lean_inc(v_u_808_);
v___x_846_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_808_, v_v_809_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_877_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_877_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_877_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_877_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___x_851_; 
v___x_851_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
lean_del_object(v___x_849_);
v___x_852_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_808_, v_v_809_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_863_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_863_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
uint8_t v___x_857_; 
v___x_857_ = lean_unbox(v_a_853_);
lean_dec(v_a_853_);
if (v___x_857_ == 0)
{
lean_del_object(v___x_855_);
goto v___jp_836_;
}
else
{
uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = 1;
v___x_859_ = lean_box(v___x_858_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_852_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_852_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v_v_809_);
lean_dec(v_u_808_);
v___x_872_ = 1;
v___x_873_ = lean_box(v___x_872_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_873_);
v___x_875_ = v___x_849_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v_v_809_);
lean_dec(v_u_808_);
v_a_878_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_846_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_846_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
v___jp_886_:
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = 2;
v___x_888_ = lean_box(v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
v___jp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_902_; 
v___x_892_ = l_Lean_Level_mvarId_x21(v_u_808_);
lean_dec(v_u_808_);
v___x_893_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_892_, v_v_809_, v___y_891_);
lean_dec(v___y_891_);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_893_, 0);
lean_dec(v_unused_903_);
v___x_895_ = v___x_893_;
v_isShared_896_ = v_isSharedCheck_902_;
goto v_resetjp_894_;
}
else
{
lean_dec(v___x_893_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_902_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_897_ = 1;
v___x_898_ = lean_box(v___x_897_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_898_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_916_; 
v___x_906_ = l_Lean_Level_mvarId_x21(v_v_809_);
lean_dec(v_v_809_);
v___x_907_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_906_, v_u_808_, v___y_905_);
lean_dec(v___y_905_);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_907_, 0);
lean_dec(v_unused_917_);
v___x_909_ = v___x_907_;
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
else
{
lean_dec(v___x_907_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_911_ = 1;
v___x_912_ = lean_box(v___x_911_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1107_, lean_object* v_v_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1107_, v_v_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v_mctx_1119_; lean_object* v___x_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1123_; lean_object* v_cache_1124_; lean_object* v_zetaDeltaFVarIds_1125_; lean_object* v_postponed_1126_; lean_object* v_diag_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v___x_1118_ = lean_st_ref_get(v___y_1116_);
v_mctx_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_mctx_1119_);
lean_dec(v___x_1118_);
v___x_1120_ = lean_instantiate_level_mvars(v_mctx_1119_, v_l_1115_);
v_fst_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_fst_1121_);
v_snd_1122_ = lean_ctor_get(v___x_1120_, 1);
lean_inc(v_snd_1122_);
lean_dec_ref(v___x_1120_);
v___x_1123_ = lean_st_ref_take(v___y_1116_);
v_cache_1124_ = lean_ctor_get(v___x_1123_, 1);
v_zetaDeltaFVarIds_1125_ = lean_ctor_get(v___x_1123_, 2);
v_postponed_1126_ = lean_ctor_get(v___x_1123_, 3);
v_diag_1127_ = lean_ctor_get(v___x_1123_, 4);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1137_);
v___x_1129_ = v___x_1123_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_diag_1127_);
lean_inc(v_postponed_1126_);
lean_inc(v_zetaDeltaFVarIds_1125_);
lean_inc(v_cache_1124_);
lean_dec(v___x_1123_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_fst_1121_);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_fst_1121_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_zetaDeltaFVarIds_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_postponed_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_diag_1127_);
v___x_1132_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_st_ref_put(v___y_1116_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_snd_1122_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1138_, v___y_1139_);
lean_dec(v___y_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1142_, v___y_1144_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(32u);
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1159_ = ((size_t)5ULL);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_unsigned_to_nat(32u);
v___x_1162_ = lean_mk_empty_array_with_capacity(v___x_1161_);
v___x_1163_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1164_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
lean_ctor_set(v___x_1164_, 2, v___x_1160_);
lean_ctor_set(v___x_1164_, 3, v___x_1160_);
lean_ctor_set_usize(v___x_1164_, 4, v___x_1159_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v_traceState_1168_; lean_object* v_traces_1169_; lean_object* v___x_1170_; lean_object* v_traceState_1171_; lean_object* v_env_1172_; lean_object* v_nextMacroScope_1173_; lean_object* v_ngen_1174_; lean_object* v_auxDeclNGen_1175_; lean_object* v_cache_1176_; lean_object* v_recordedDeps_1177_; lean_object* v_messages_1178_; lean_object* v_infoState_1179_; lean_object* v_snapshotTasks_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1199_; 
v___x_1167_ = lean_st_ref_get(v___y_1165_);
v_traceState_1168_ = lean_ctor_get(v___x_1167_, 4);
lean_inc_ref(v_traceState_1168_);
lean_dec(v___x_1167_);
v_traces_1169_ = lean_ctor_get(v_traceState_1168_, 0);
lean_inc_ref(v_traces_1169_);
lean_dec_ref(v_traceState_1168_);
v___x_1170_ = lean_st_ref_take(v___y_1165_);
v_traceState_1171_ = lean_ctor_get(v___x_1170_, 4);
v_env_1172_ = lean_ctor_get(v___x_1170_, 0);
v_nextMacroScope_1173_ = lean_ctor_get(v___x_1170_, 1);
v_ngen_1174_ = lean_ctor_get(v___x_1170_, 2);
v_auxDeclNGen_1175_ = lean_ctor_get(v___x_1170_, 3);
v_cache_1176_ = lean_ctor_get(v___x_1170_, 5);
v_recordedDeps_1177_ = lean_ctor_get(v___x_1170_, 6);
v_messages_1178_ = lean_ctor_get(v___x_1170_, 7);
v_infoState_1179_ = lean_ctor_get(v___x_1170_, 8);
v_snapshotTasks_1180_ = lean_ctor_get(v___x_1170_, 9);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1182_ = v___x_1170_;
v_isShared_1183_ = v_isSharedCheck_1199_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snapshotTasks_1180_);
lean_inc(v_infoState_1179_);
lean_inc(v_messages_1178_);
lean_inc(v_recordedDeps_1177_);
lean_inc(v_cache_1176_);
lean_inc(v_traceState_1171_);
lean_inc(v_auxDeclNGen_1175_);
lean_inc(v_ngen_1174_);
lean_inc(v_nextMacroScope_1173_);
lean_inc(v_env_1172_);
lean_dec(v___x_1170_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1199_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
uint64_t v_tid_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1197_; 
v_tid_1184_ = lean_ctor_get_uint64(v_traceState_1171_, sizeof(void*)*1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_traceState_1171_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v_traceState_1171_, 0);
lean_dec(v_unused_1198_);
v___x_1186_ = v_traceState_1171_;
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_traceState_1171_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1188_);
lean_ctor_set_uint64(v_reuseFailAlloc_1196_, sizeof(void*)*1, v_tid_1184_);
v___x_1190_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 4, v___x_1190_);
v___x_1192_ = v___x_1182_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_env_1172_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_nextMacroScope_1173_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_ngen_1174_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_auxDeclNGen_1175_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1195_, 5, v_cache_1176_);
lean_ctor_set(v_reuseFailAlloc_1195_, 6, v_recordedDeps_1177_);
lean_ctor_set(v_reuseFailAlloc_1195_, 7, v_messages_1178_);
lean_ctor_set(v_reuseFailAlloc_1195_, 8, v_infoState_1179_);
lean_ctor_set(v_reuseFailAlloc_1195_, 9, v_snapshotTasks_1180_);
v___x_1192_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_st_ref_put(v___y_1165_, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_traces_1169_);
return v___x_1194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1200_);
lean_dec(v___y_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1215_, lean_object* v_k_1216_, uint8_t v_v_1217_){
_start:
{
lean_object* v_map_1218_; uint8_t v_hasTrace_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1233_; 
v_map_1218_ = lean_ctor_get(v_o_1215_, 0);
v_hasTrace_1219_ = lean_ctor_get_uint8(v_o_1215_, sizeof(void*)*1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_o_1215_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1221_ = v_o_1215_;
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_map_1218_);
lean_dec(v_o_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1223_, 0, v_v_1217_);
lean_inc(v_k_1216_);
v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1216_, v___x_1223_, v_map_1218_);
if (v_hasTrace_1219_ == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; lean_object* v___x_1228_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1226_ = l_Lean_Name_isPrefixOf(v___x_1225_, v_k_1216_);
lean_dec(v_k_1216_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1228_ = v___x_1221_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1224_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*1, v___x_1226_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_k_1216_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1231_ = v___x_1221_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, sizeof(void*)*1, v_hasTrace_1219_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1234_, lean_object* v_k_1235_, lean_object* v_v_1236_){
_start:
{
uint8_t v_v_boxed_1237_; lean_object* v_res_1238_; 
v_v_boxed_1237_ = lean_unbox(v_v_1236_);
v_res_1238_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1234_, v_k_1235_, v_v_boxed_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1239_, lean_object* v_opt_1240_){
_start:
{
lean_object* v_name_1241_; lean_object* v_defValue_1242_; lean_object* v_map_1243_; lean_object* v___x_1244_; 
v_name_1241_ = lean_ctor_get(v_opt_1240_, 0);
v_defValue_1242_ = lean_ctor_get(v_opt_1240_, 1);
v_map_1243_ = lean_ctor_get(v_opts_1239_, 0);
v___x_1244_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1243_, v_name_1241_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_inc(v_defValue_1242_);
return v_defValue_1242_;
}
else
{
lean_object* v_val_1245_; 
v_val_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1244_, 1);
if (lean_obj_tag(v_val_1245_) == 3)
{
lean_object* v_v_1246_; 
v_v_1246_ = lean_ctor_get(v_val_1245_, 0);
lean_inc(v_v_1246_);
lean_dec_ref_known(v_val_1245_, 1);
return v_v_1246_;
}
else
{
lean_dec(v_val_1245_);
lean_inc(v_defValue_1242_);
return v_defValue_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1247_, lean_object* v_opt_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1247_, v_opt_1248_);
lean_dec_ref(v_opt_1248_);
lean_dec_ref(v_opts_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1250_, lean_object* v_opt_1251_){
_start:
{
lean_object* v_name_1252_; lean_object* v_defValue_1253_; lean_object* v_map_1254_; lean_object* v___x_1255_; 
v_name_1252_ = lean_ctor_get(v_opt_1251_, 0);
v_defValue_1253_ = lean_ctor_get(v_opt_1251_, 1);
v_map_1254_ = lean_ctor_get(v_opts_1250_, 0);
v___x_1255_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1254_, v_name_1252_);
if (lean_obj_tag(v___x_1255_) == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_unbox(v_defValue_1253_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v___x_1255_, 1);
if (lean_obj_tag(v_val_1257_) == 1)
{
uint8_t v_v_1258_; 
v_v_1258_ = lean_ctor_get_uint8(v_val_1257_, 0);
lean_dec_ref_known(v_val_1257_, 0);
return v_v_1258_;
}
else
{
uint8_t v___x_1259_; 
lean_dec(v_val_1257_);
v___x_1259_ = lean_unbox(v_defValue_1253_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1260_, lean_object* v_opt_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1260_, v_opt_1261_);
lean_dec_ref(v_opt_1261_);
lean_dec_ref(v_opts_1260_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v_lhs_1267_, lean_object* v_rhs_1268_, uint8_t v___x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___y_1303_; 
if (v___x_1264_ == 0)
{
lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_a_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
lean_inc(v_lhs_1267_);
v___x_1340_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1267_, v___y_1271_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = l_Lean_Level_normalize(v_a_1341_);
lean_dec(v_a_1341_);
lean_inc(v_rhs_1268_);
v___x_1343_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1268_, v___y_1271_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = l_Lean_Level_normalize(v_a_1344_);
lean_dec(v_a_1344_);
v___x_1346_ = lean_level_eq(v_lhs_1267_, v___x_1342_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
v___x_1347_ = lean_is_level_def_eq(v___x_1342_, v___x_1345_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1347_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_level_eq(v_rhs_1268_, v___x_1345_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
v___x_1349_ = lean_is_level_def_eq(v___x_1342_, v___x_1345_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
lean_dec(v___x_1345_);
lean_dec(v___x_1342_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v_rhs_1268_);
lean_inc(v_lhs_1267_);
v___x_1350_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1267_, v_rhs_1268_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1392_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1392_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1392_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = 2;
v___x_1356_ = lean_unbox(v_a_1351_);
v___x_1357_ = l_Lean_instBEqLBool_beq(v___x_1356_, v___x_1355_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1358_ = 1;
v___x_1359_ = lean_unbox(v_a_1351_);
lean_dec(v_a_1351_);
v___x_1360_ = l_Lean_instBEqLBool_beq(v___x_1359_, v___x_1358_);
v___x_1361_ = lean_box(v___x_1360_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1361_);
v___x_1363_ = v___x_1353_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v___x_1365_; 
lean_del_object(v___x_1353_);
lean_dec(v_a_1351_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v_lhs_1267_);
lean_inc(v_rhs_1268_);
v___x_1365_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1268_, v_lhs_1267_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1383_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1383_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1383_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_unbox(v_a_1366_);
v___x_1371_ = l_Lean_instBEqLBool_beq(v___x_1370_, v___x_1355_);
if (v___x_1371_ == 0)
{
uint8_t v___x_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1372_ = 1;
v___x_1373_ = lean_unbox(v_a_1366_);
lean_dec(v_a_1366_);
v___x_1374_ = l_Lean_instBEqLBool_beq(v___x_1373_, v___x_1372_);
v___x_1375_ = lean_box(v___x_1374_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1375_);
v___x_1377_ = v___x_1368_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v___x_1379_; 
lean_del_object(v___x_1368_);
lean_dec(v_a_1366_);
lean_inc(v_lhs_1267_);
v___x_1379_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1267_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; uint8_t v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v___x_1381_ = lean_unbox(v_a_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref_known(v___x_1379_, 1);
lean_inc(v_rhs_1268_);
v___x_1382_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1268_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
v___y_1303_ = v___x_1382_;
goto v___jp_1302_;
}
else
{
v___y_1303_ = v___x_1379_;
goto v___jp_1302_;
}
}
else
{
v___y_1303_ = v___x_1379_;
goto v___jp_1302_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v_a_1384_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1365_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1365_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v_a_1393_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1350_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1350_);
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
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1401_ = l_Lean_Level_getOffset(v_lhs_1267_);
lean_dec(v_lhs_1267_);
v___x_1402_ = l_Lean_Level_getOffset(v_rhs_1268_);
lean_dec(v_rhs_1268_);
v___x_1403_ = lean_nat_dec_eq(v___x_1401_, v___x_1402_);
lean_dec(v___x_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
v___jp_1275_:
{
lean_object* v_toCold_1276_; lean_object* v_options_1277_; uint8_t v_hasTrace_1278_; 
v_toCold_1276_ = lean_ctor_get(v___y_1272_, 0);
v_options_1277_ = lean_ctor_get(v_toCold_1276_, 2);
v_hasTrace_1278_ = lean_ctor_get_uint8(v_options_1277_, sizeof(void*)*1);
if (v_hasTrace_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1279_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1279_;
}
else
{
lean_object* v_inheritedTraceOptions_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_inheritedTraceOptions_1280_ = lean_ctor_get(v_toCold_1276_, 11);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1282_ = l_Lean_Name_mkStr3(v___x_1265_, v___x_1266_, v___x_1281_);
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1282_);
v___x_1284_ = l_Lean_Name_append(v___x_1283_, v___x_1282_);
v___x_1285_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1280_, v_options_1277_, v___x_1284_);
lean_dec(v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v___x_1282_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1286_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1287_ = l_Lean_MessageData_ofLevel(v_lhs_1267_);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_MessageData_ofLevel(v_rhs_1268_);
v___x_1291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1282_, v___x_1291_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v___x_1293_; 
lean_dec_ref_known(v___x_1292_, 1);
v___x_1293_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1293_;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1292_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
v___jp_1302_:
{
if (lean_obj_tag(v___y_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1339_; 
v_a_1304_ = lean_ctor_get(v___y_1303_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___y_1303_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1306_ = v___y_1303_;
v_isShared_1307_ = v_isSharedCheck_1339_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___y_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1339_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_unbox(v_a_1304_);
lean_dec(v_a_1304_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; uint8_t v_isDefEqStuckEx_1310_; 
v___x_1309_ = l_Lean_Meta_Context_config(v___y_1270_);
v_isDefEqStuckEx_1310_ = lean_ctor_get_uint8(v___x_1309_, 4);
lean_dec_ref(v___x_1309_);
if (v_isDefEqStuckEx_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1311_ = lean_box(v___x_1264_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1311_);
v___x_1313_ = v___x_1306_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_Level_isMVar(v_lhs_1267_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_Level_isMVar(v_rhs_1268_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1317_ = lean_box(v___x_1316_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1317_);
v___x_1319_ = v___x_1306_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
else
{
lean_del_object(v___x_1306_);
goto v___jp_1275_;
}
}
else
{
lean_del_object(v___x_1306_);
goto v___jp_1275_;
}
}
}
else
{
lean_object* v___x_1321_; 
lean_del_object(v___x_1306_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
v___x_1321_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1267_, v_rhs_1268_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1321_, 0);
lean_dec(v_unused_1330_);
v___x_1323_ = v___x_1321_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v___x_1321_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = lean_box(v___x_1269_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_a_1331_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1321_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1321_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
else
{
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1265_);
return v___y_1303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v_lhs_1409_, lean_object* v_rhs_1410_, lean_object* v___x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_13232__boxed_1417_; uint8_t v___x_13235__boxed_1418_; lean_object* v_res_1419_; 
v___x_13232__boxed_1417_ = lean_unbox(v___x_1406_);
v___x_13235__boxed_1418_ = lean_unbox(v___x_1411_);
v_res_1419_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13232__boxed_1417_, v___x_1407_, v___x_1408_, v_lhs_1409_, v_rhs_1410_, v___x_13235__boxed_1418_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1420_){
_start:
{
if (lean_obj_tag(v_e_1420_) == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = 2;
return v___x_1421_;
}
else
{
lean_object* v_a_1422_; uint8_t v___x_1423_; 
v_a_1422_ = lean_ctor_get(v_e_1420_, 0);
v___x_1423_ = lean_unbox(v_a_1422_);
if (v___x_1423_ == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = 1;
return v___x_1424_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = 0;
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1426_);
lean_dec_ref(v_e_1426_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v_x_1429_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v_x_1429_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v_x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 1);
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
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
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v_x_1429_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v_x_1429_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_x_1429_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 0);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1450_, size_t v_i_1451_, lean_object* v_bs_1452_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_lt(v_i_1451_, v_sz_1450_);
if (v___x_1453_ == 0)
{
return v_bs_1452_;
}
else
{
lean_object* v_v_1454_; lean_object* v_msg_1455_; lean_object* v___x_1456_; lean_object* v_bs_x27_1457_; size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v_v_1454_ = lean_array_uget_borrowed(v_bs_1452_, v_i_1451_);
v_msg_1455_ = lean_ctor_get(v_v_1454_, 1);
lean_inc_ref(v_msg_1455_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v_bs_x27_1457_ = lean_array_uset(v_bs_1452_, v_i_1451_, v___x_1456_);
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_add(v_i_1451_, v___x_1458_);
v___x_1460_ = lean_array_uset(v_bs_x27_1457_, v_i_1451_, v_msg_1455_);
v_i_1451_ = v___x_1459_;
v_bs_1452_ = v___x_1460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1462_, lean_object* v_i_1463_, lean_object* v_bs_1464_){
_start:
{
size_t v_sz_boxed_1465_; size_t v_i_boxed_1466_; lean_object* v_res_1467_; 
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1462_);
lean_dec(v_sz_1462_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1463_);
lean_dec(v_i_1463_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1465_, v_i_boxed_1466_, v_bs_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1468_, lean_object* v_data_1469_, lean_object* v_ref_1470_, lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_toCold_1477_; lean_object* v_currRecDepth_1478_; lean_object* v_ref_1479_; uint16_t v_optionFlags_1480_; uint8_t v_suppressElabErrors_1481_; uint8_t v_isRecordingDeps_1482_; lean_object* v_ref_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v_traceState_1486_; lean_object* v_traces_1487_; lean_object* v___x_1488_; size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v_msg_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1532_; 
v_toCold_1477_ = lean_ctor_get(v___y_1474_, 0);
v_currRecDepth_1478_ = lean_ctor_get(v___y_1474_, 1);
v_ref_1479_ = lean_ctor_get(v___y_1474_, 2);
v_optionFlags_1480_ = lean_ctor_get_uint16(v___y_1474_, sizeof(void*)*3);
v_suppressElabErrors_1481_ = lean_ctor_get_uint8(v___y_1474_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1482_ = lean_ctor_get_uint8(v___y_1474_, sizeof(void*)*3 + 3);
v_ref_1483_ = l_Lean_replaceRef(v_ref_1470_, v_ref_1479_);
lean_inc(v_currRecDepth_1478_);
lean_inc_ref(v_toCold_1477_);
v___x_1484_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1484_, 0, v_toCold_1477_);
lean_ctor_set(v___x_1484_, 1, v_currRecDepth_1478_);
lean_ctor_set(v___x_1484_, 2, v_ref_1483_);
lean_ctor_set_uint16(v___x_1484_, sizeof(void*)*3, v_optionFlags_1480_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 2, v_suppressElabErrors_1481_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 3, v_isRecordingDeps_1482_);
v___x_1485_ = lean_st_ref_get(v___y_1475_);
v_traceState_1486_ = lean_ctor_get(v___x_1485_, 4);
lean_inc_ref(v_traceState_1486_);
lean_dec(v___x_1485_);
v_traces_1487_ = lean_ctor_get(v_traceState_1486_, 0);
lean_inc_ref(v_traces_1487_);
lean_dec_ref(v_traceState_1486_);
v___x_1488_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1487_);
lean_dec_ref(v_traces_1487_);
v_sz_1489_ = lean_array_size(v___x_1488_);
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1489_, v___x_1490_, v___x_1488_);
v_msg_1492_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1492_, 0, v_data_1469_);
lean_ctor_set(v_msg_1492_, 1, v_msg_1471_);
lean_ctor_set(v_msg_1492_, 2, v___x_1491_);
v___x_1493_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1492_, v___y_1472_, v___y_1473_, v___x_1484_, v___y_1475_);
lean_dec_ref_known(v___x_1484_, 3);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1532_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1532_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v_traceState_1499_; lean_object* v_env_1500_; lean_object* v_nextMacroScope_1501_; lean_object* v_ngen_1502_; lean_object* v_auxDeclNGen_1503_; lean_object* v_cache_1504_; lean_object* v_recordedDeps_1505_; lean_object* v_messages_1506_; lean_object* v_infoState_1507_; lean_object* v_snapshotTasks_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1531_; 
v___x_1498_ = lean_st_ref_take(v___y_1475_);
v_traceState_1499_ = lean_ctor_get(v___x_1498_, 4);
v_env_1500_ = lean_ctor_get(v___x_1498_, 0);
v_nextMacroScope_1501_ = lean_ctor_get(v___x_1498_, 1);
v_ngen_1502_ = lean_ctor_get(v___x_1498_, 2);
v_auxDeclNGen_1503_ = lean_ctor_get(v___x_1498_, 3);
v_cache_1504_ = lean_ctor_get(v___x_1498_, 5);
v_recordedDeps_1505_ = lean_ctor_get(v___x_1498_, 6);
v_messages_1506_ = lean_ctor_get(v___x_1498_, 7);
v_infoState_1507_ = lean_ctor_get(v___x_1498_, 8);
v_snapshotTasks_1508_ = lean_ctor_get(v___x_1498_, 9);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1510_ = v___x_1498_;
v_isShared_1511_ = v_isSharedCheck_1531_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_snapshotTasks_1508_);
lean_inc(v_infoState_1507_);
lean_inc(v_messages_1506_);
lean_inc(v_recordedDeps_1505_);
lean_inc(v_cache_1504_);
lean_inc(v_traceState_1499_);
lean_inc(v_auxDeclNGen_1503_);
lean_inc(v_ngen_1502_);
lean_inc(v_nextMacroScope_1501_);
lean_inc(v_env_1500_);
lean_dec(v___x_1498_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1531_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
uint64_t v_tid_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1529_; 
v_tid_1512_ = lean_ctor_get_uint64(v_traceState_1499_, sizeof(void*)*1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_traceState_1499_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_traceState_1499_, 0);
lean_dec(v_unused_1530_);
v___x_1514_ = v_traceState_1499_;
v_isShared_1515_ = v_isSharedCheck_1529_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_traceState_1499_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1529_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_ref_1470_);
lean_ctor_set(v___x_1517_, 1, v_a_1494_);
v___x_1518_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1468_, v___x_1517_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1518_);
v___x_1520_ = v___x_1514_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1518_);
lean_ctor_set_uint64(v_reuseFailAlloc_1528_, sizeof(void*)*1, v_tid_1512_);
v___x_1520_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v___x_1520_);
v___x_1522_ = v___x_1510_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_env_1500_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_nextMacroScope_1501_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_ngen_1502_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_auxDeclNGen_1503_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1527_, 5, v_cache_1504_);
lean_ctor_set(v_reuseFailAlloc_1527_, 6, v_recordedDeps_1505_);
lean_ctor_set(v_reuseFailAlloc_1527_, 7, v_messages_1506_);
lean_ctor_set(v_reuseFailAlloc_1527_, 8, v_infoState_1507_);
lean_ctor_set(v_reuseFailAlloc_1527_, 9, v_snapshotTasks_1508_);
v___x_1522_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_st_ref_put(v___y_1475_, v___x_1522_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1516_);
v___x_1525_ = v___x_1496_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1516_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1533_, lean_object* v_data_1534_, lean_object* v_ref_1535_, lean_object* v_msg_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1533_, v_data_1534_, v_ref_1535_, v_msg_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1542_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1543_; double v___x_1544_; 
v___x_1543_ = lean_unsigned_to_nat(1000u);
v___x_1544_ = lean_float_of_nat(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1545_, uint8_t v_collapsed_1546_, lean_object* v_tag_1547_, lean_object* v_opts_1548_, uint8_t v_clsEnabled_1549_, lean_object* v_oldTraces_1550_, lean_object* v_ref_1551_, lean_object* v_msg_1552_, lean_object* v_resStartStop_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_fst_1559_; lean_object* v_snd_1560_; lean_object* v_data_1562_; lean_object* v_fst_1573_; lean_object* v_snd_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; uint8_t v___y_1587_; double v___y_1619_; 
v_fst_1559_ = lean_ctor_get(v_resStartStop_1553_, 0);
lean_inc(v_fst_1559_);
v_snd_1560_ = lean_ctor_get(v_resStartStop_1553_, 1);
lean_inc(v_snd_1560_);
lean_dec_ref(v_resStartStop_1553_);
v_fst_1573_ = lean_ctor_get(v_snd_1560_, 0);
lean_inc(v_fst_1573_);
v_snd_1574_ = lean_ctor_get(v_snd_1560_, 1);
lean_inc(v_snd_1574_);
lean_dec(v_snd_1560_);
v___x_1575_ = l_Lean_trace_profiler;
v___x_1576_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1548_, v___x_1575_);
if (v___x_1576_ == 0)
{
v___y_1587_ = v___x_1576_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1625_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1548_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; double v___x_1628_; double v___x_1629_; double v___x_1630_; 
v___x_1626_ = l_Lean_trace_profiler_threshold;
v___x_1627_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1548_, v___x_1626_);
v___x_1628_ = lean_float_of_nat(v___x_1627_);
v___x_1629_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1630_ = lean_float_div(v___x_1628_, v___x_1629_);
v___y_1619_ = v___x_1630_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; double v___x_1633_; 
v___x_1631_ = l_Lean_trace_profiler_threshold;
v___x_1632_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1548_, v___x_1631_);
v___x_1633_ = lean_float_of_nat(v___x_1632_);
v___y_1619_ = v___x_1633_;
goto v___jp_1618_;
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1550_, v_data_1562_, v_ref_1551_, v_msg_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref_known(v___x_1563_, 1);
v___x_1564_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1559_);
return v___x_1564_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_fst_1559_);
v_a_1565_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1563_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
v___jp_1577_:
{
uint8_t v_result_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; double v___x_1581_; lean_object* v_data_1582_; 
v_result_1578_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1559_);
v___x_1579_ = lean_box(v_result_1578_);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___x_1581_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1547_);
lean_inc_ref(v___x_1580_);
lean_inc(v_cls_1545_);
v_data_1582_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1582_, 0, v_cls_1545_);
lean_ctor_set(v_data_1582_, 1, v___x_1580_);
lean_ctor_set(v_data_1582_, 2, v_tag_1547_);
lean_ctor_set_float(v_data_1582_, sizeof(void*)*3, v___x_1581_);
lean_ctor_set_float(v_data_1582_, sizeof(void*)*3 + 8, v___x_1581_);
lean_ctor_set_uint8(v_data_1582_, sizeof(void*)*3 + 16, v_collapsed_1546_);
if (v___x_1576_ == 0)
{
lean_dec_ref_known(v___x_1580_, 1);
lean_dec(v_snd_1574_);
lean_dec(v_fst_1573_);
lean_dec_ref(v_tag_1547_);
lean_dec(v_cls_1545_);
v_data_1562_ = v_data_1582_;
goto v___jp_1561_;
}
else
{
lean_object* v_data_1583_; double v___x_1584_; double v___x_1585_; 
lean_dec_ref_known(v_data_1582_, 3);
v_data_1583_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1583_, 0, v_cls_1545_);
lean_ctor_set(v_data_1583_, 1, v___x_1580_);
lean_ctor_set(v_data_1583_, 2, v_tag_1547_);
v___x_1584_ = lean_unbox_float(v_fst_1573_);
lean_dec(v_fst_1573_);
lean_ctor_set_float(v_data_1583_, sizeof(void*)*3, v___x_1584_);
v___x_1585_ = lean_unbox_float(v_snd_1574_);
lean_dec(v_snd_1574_);
lean_ctor_set_float(v_data_1583_, sizeof(void*)*3 + 8, v___x_1585_);
lean_ctor_set_uint8(v_data_1583_, sizeof(void*)*3 + 16, v_collapsed_1546_);
v_data_1562_ = v_data_1583_;
goto v___jp_1561_;
}
}
v___jp_1586_:
{
if (v_clsEnabled_1549_ == 0)
{
if (v___y_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v_traceState_1589_; lean_object* v_env_1590_; lean_object* v_nextMacroScope_1591_; lean_object* v_ngen_1592_; lean_object* v_auxDeclNGen_1593_; lean_object* v_cache_1594_; lean_object* v_recordedDeps_1595_; lean_object* v_messages_1596_; lean_object* v_infoState_1597_; lean_object* v_snapshotTasks_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_snd_1574_);
lean_dec(v_fst_1573_);
lean_dec_ref(v_msg_1552_);
lean_dec(v_ref_1551_);
lean_dec_ref(v_tag_1547_);
lean_dec(v_cls_1545_);
v___x_1588_ = lean_st_ref_take(v___y_1557_);
v_traceState_1589_ = lean_ctor_get(v___x_1588_, 4);
v_env_1590_ = lean_ctor_get(v___x_1588_, 0);
v_nextMacroScope_1591_ = lean_ctor_get(v___x_1588_, 1);
v_ngen_1592_ = lean_ctor_get(v___x_1588_, 2);
v_auxDeclNGen_1593_ = lean_ctor_get(v___x_1588_, 3);
v_cache_1594_ = lean_ctor_get(v___x_1588_, 5);
v_recordedDeps_1595_ = lean_ctor_get(v___x_1588_, 6);
v_messages_1596_ = lean_ctor_get(v___x_1588_, 7);
v_infoState_1597_ = lean_ctor_get(v___x_1588_, 8);
v_snapshotTasks_1598_ = lean_ctor_get(v___x_1588_, 9);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1600_ = v___x_1588_;
v_isShared_1601_ = v_isSharedCheck_1617_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_snapshotTasks_1598_);
lean_inc(v_infoState_1597_);
lean_inc(v_messages_1596_);
lean_inc(v_recordedDeps_1595_);
lean_inc(v_cache_1594_);
lean_inc(v_traceState_1589_);
lean_inc(v_auxDeclNGen_1593_);
lean_inc(v_ngen_1592_);
lean_inc(v_nextMacroScope_1591_);
lean_inc(v_env_1590_);
lean_dec(v___x_1588_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1617_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
uint64_t v_tid_1602_; lean_object* v_traces_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1616_; 
v_tid_1602_ = lean_ctor_get_uint64(v_traceState_1589_, sizeof(void*)*1);
v_traces_1603_ = lean_ctor_get(v_traceState_1589_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_traceState_1589_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1605_ = v_traceState_1589_;
v_isShared_1606_ = v_isSharedCheck_1616_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_traces_1603_);
lean_dec(v_traceState_1589_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1616_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1550_, v_traces_1603_);
lean_dec_ref(v_traces_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1607_);
lean_ctor_set_uint64(v_reuseFailAlloc_1615_, sizeof(void*)*1, v_tid_1602_);
v___x_1609_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 4, v___x_1609_);
v___x_1611_ = v___x_1600_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_env_1590_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_nextMacroScope_1591_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_ngen_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_auxDeclNGen_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v_cache_1594_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_recordedDeps_1595_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_messages_1596_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_infoState_1597_);
lean_ctor_set(v_reuseFailAlloc_1614_, 9, v_snapshotTasks_1598_);
v___x_1611_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_st_ref_put(v___y_1557_, v___x_1611_);
v___x_1613_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1559_);
return v___x_1613_;
}
}
}
}
}
else
{
goto v___jp_1577_;
}
}
else
{
goto v___jp_1577_;
}
}
v___jp_1618_:
{
double v___x_1620_; double v___x_1621_; double v___x_1622_; uint8_t v___x_1623_; 
v___x_1620_ = lean_unbox_float(v_snd_1574_);
v___x_1621_ = lean_unbox_float(v_fst_1573_);
v___x_1622_ = lean_float_sub(v___x_1620_, v___x_1621_);
v___x_1623_ = lean_float_decLt(v___y_1619_, v___x_1622_);
v___y_1587_ = v___x_1623_;
goto v___jp_1586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1634_, lean_object* v_collapsed_1635_, lean_object* v_tag_1636_, lean_object* v_opts_1637_, lean_object* v_clsEnabled_1638_, lean_object* v_oldTraces_1639_, lean_object* v_ref_1640_, lean_object* v_msg_1641_, lean_object* v_resStartStop_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v_collapsed_boxed_1648_; uint8_t v_clsEnabled_boxed_1649_; lean_object* v_res_1650_; 
v_collapsed_boxed_1648_ = lean_unbox(v_collapsed_1635_);
v_clsEnabled_boxed_1649_ = lean_unbox(v_clsEnabled_1638_);
v_res_1650_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1634_, v_collapsed_boxed_1648_, v_tag_1636_, v_opts_1637_, v_clsEnabled_boxed_1649_, v_oldTraces_1639_, v_ref_1640_, v_msg_1641_, v_resStartStop_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v_opts_1637_);
return v_res_1650_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1651_; double v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(1000000000u);
v___x_1652_ = lean_float_of_nat(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1668_ = l_Lean_Name_append(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___y_1677_; uint8_t v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v_a_1690_; lean_object* v___y_1700_; lean_object* v___y_1701_; uint8_t v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v_a_1713_; lean_object* v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; uint16_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v_toCold_1742_; lean_object* v_currRecDepth_1743_; lean_object* v_ref_1744_; uint8_t v_suppressElabErrors_1745_; uint8_t v_isRecordingDeps_1746_; lean_object* v___y_1747_; lean_object* v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint16_t v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1837_; uint8_t v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; uint16_t v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; uint8_t v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1876_; uint8_t v___y_1877_; lean_object* v___y_1878_; uint8_t v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; uint8_t v___y_1886_; uint16_t v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; uint8_t v___y_1893_; lean_object* v___y_1895_; lean_object* v___y_1896_; uint8_t v___y_1897_; uint16_t v___y_1898_; uint8_t v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; uint8_t v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v_lhs_1935_; lean_object* v_rhs_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; 
if (lean_obj_tag(v_x_1669_) == 1)
{
if (lean_obj_tag(v_x_1670_) == 1)
{
lean_object* v_a_1967_; lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1967_ = lean_ctor_get(v_x_1669_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v_x_1669_, 1);
v_a_1968_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v_x_1670_, 1);
v___x_1969_ = lean_is_level_def_eq(v_a_1967_, v_a_1968_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
return v___x_1969_;
}
else
{
v_lhs_1935_ = v_x_1669_;
v_rhs_1936_ = v_x_1670_;
v___y_1937_ = v_a_1671_;
v___y_1938_ = v_a_1672_;
v___y_1939_ = v_a_1673_;
v___y_1940_ = v_a_1674_;
goto v___jp_1934_;
}
}
else
{
v_lhs_1935_ = v_x_1669_;
v_rhs_1936_ = v_x_1670_;
v___y_1937_ = v_a_1671_;
v___y_1938_ = v_a_1672_;
v___y_1939_ = v_a_1673_;
v___y_1940_ = v_a_1674_;
goto v___jp_1934_;
}
v___jp_1676_:
{
lean_object* v___x_1691_; double v___x_1692_; double v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1691_ = lean_io_get_num_heartbeats();
v___x_1692_ = lean_float_of_nat(v___y_1679_);
v___x_1693_ = lean_float_of_nat(v___x_1691_);
v___x_1694_ = lean_box_float(v___x_1692_);
v___x_1695_ = lean_box_float(v___x_1693_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1690_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
v___x_1698_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1688_, v___y_1678_, v___y_1689_, v___y_1684_, v___y_1685_, v___y_1681_, v___y_1687_, v___y_1682_, v___x_1697_, v___y_1680_, v___y_1686_, v___y_1683_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1684_);
return v___x_1698_;
}
v___jp_1699_:
{
lean_object* v___x_1714_; double v___x_1715_; double v___x_1716_; double v___x_1717_; double v___x_1718_; double v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1714_ = lean_io_mono_nanos_now();
v___x_1715_ = lean_float_of_nat(v___y_1701_);
v___x_1716_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1717_ = lean_float_div(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_float_of_nat(v___x_1714_);
v___x_1719_ = lean_float_div(v___x_1718_, v___x_1716_);
v___x_1720_ = lean_box_float(v___x_1717_);
v___x_1721_ = lean_box_float(v___x_1719_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v_a_1713_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
lean_inc_ref(v___y_1712_);
lean_inc(v___y_1711_);
v___x_1724_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1711_, v___y_1702_, v___y_1712_, v___y_1707_, v___y_1708_, v___y_1704_, v___y_1710_, v___y_1705_, v___x_1723_, v___y_1703_, v___y_1709_, v___y_1706_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v___y_1707_);
return v___x_1724_;
}
v___jp_1725_:
{
lean_object* v_fileName_1748_; lean_object* v_fileMap_1749_; lean_object* v_currNamespace_1750_; lean_object* v_openDecls_1751_; lean_object* v_initHeartbeats_1752_; lean_object* v_maxHeartbeats_1753_; lean_object* v_quotContext_1754_; lean_object* v_currMacroScope_1755_; lean_object* v_cancelTk_x3f_1756_; lean_object* v_inheritedTraceOptions_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1809_; 
v_fileName_1748_ = lean_ctor_get(v_toCold_1742_, 0);
v_fileMap_1749_ = lean_ctor_get(v_toCold_1742_, 1);
v_currNamespace_1750_ = lean_ctor_get(v_toCold_1742_, 4);
v_openDecls_1751_ = lean_ctor_get(v_toCold_1742_, 5);
v_initHeartbeats_1752_ = lean_ctor_get(v_toCold_1742_, 6);
v_maxHeartbeats_1753_ = lean_ctor_get(v_toCold_1742_, 7);
v_quotContext_1754_ = lean_ctor_get(v_toCold_1742_, 8);
v_currMacroScope_1755_ = lean_ctor_get(v_toCold_1742_, 9);
v_cancelTk_x3f_1756_ = lean_ctor_get(v_toCold_1742_, 10);
v_inheritedTraceOptions_1757_ = lean_ctor_get(v_toCold_1742_, 11);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_toCold_1742_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1810_ = lean_ctor_get(v_toCold_1742_, 3);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_toCold_1742_, 2);
lean_dec(v_unused_1811_);
v___x_1759_ = v_toCold_1742_;
v_isShared_1760_ = v_isSharedCheck_1809_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_inheritedTraceOptions_1757_);
lean_inc(v_cancelTk_x3f_1756_);
lean_inc(v_currMacroScope_1755_);
lean_inc(v_quotContext_1754_);
lean_inc(v_maxHeartbeats_1753_);
lean_inc(v_initHeartbeats_1752_);
lean_inc(v_openDecls_1751_);
lean_inc(v_currNamespace_1750_);
lean_inc(v_fileMap_1749_);
lean_inc(v_fileName_1748_);
lean_dec(v_toCold_1742_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1809_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1761_ = l_Lean_maxRecDepth;
v___x_1762_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1731_, v___x_1761_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 3, v___x_1762_);
lean_ctor_set(v___x_1759_, 2, v___y_1731_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_fileName_1748_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_fileMap_1749_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v___y_1731_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_currNamespace_1750_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_openDecls_1751_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_initHeartbeats_1752_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_maxHeartbeats_1753_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_quotContext_1754_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_currMacroScope_1755_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v_cancelTk_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1808_, 11, v_inheritedTraceOptions_1757_);
v___x_1764_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1765_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v_currRecDepth_1743_);
lean_ctor_set(v___x_1765_, 2, v_ref_1744_);
lean_ctor_set_uint16(v___x_1765_, sizeof(void*)*3, v___y_1736_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*3 + 2, v_suppressElabErrors_1745_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*3 + 3, v_isRecordingDeps_1746_);
v___x_1766_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1741_, v___y_1728_, v___y_1737_, v___x_1765_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref_known(v___x_1765_, 3);
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1767_, v___y_1728_, v___y_1737_, v___y_1732_, v___y_1726_);
lean_dec_ref(v___y_1732_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1771_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1734_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_io_mono_nanos_now();
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1728_);
v___x_1773_ = lean_apply_5(v___y_1729_, v___y_1728_, v___y_1737_, v___y_1733_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 1);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
v___y_1700_ = v___y_1726_;
v___y_1701_ = v___x_1772_;
v___y_1702_ = v___y_1727_;
v___y_1703_ = v___y_1728_;
v___y_1704_ = v___y_1730_;
v___y_1705_ = v_a_1769_;
v___y_1706_ = v___y_1733_;
v___y_1707_ = v___y_1734_;
v___y_1708_ = v___y_1735_;
v___y_1709_ = v___y_1737_;
v___y_1710_ = v___y_1738_;
v___y_1711_ = v___y_1739_;
v___y_1712_ = v___y_1740_;
v_a_1713_ = v___x_1779_;
goto v___jp_1699_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1773_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1773_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 0);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
v___y_1700_ = v___y_1726_;
v___y_1701_ = v___x_1772_;
v___y_1702_ = v___y_1727_;
v___y_1703_ = v___y_1728_;
v___y_1704_ = v___y_1730_;
v___y_1705_ = v_a_1769_;
v___y_1706_ = v___y_1733_;
v___y_1707_ = v___y_1734_;
v___y_1708_ = v___y_1735_;
v___y_1709_ = v___y_1737_;
v___y_1710_ = v___y_1738_;
v___y_1711_ = v___y_1739_;
v___y_1712_ = v___y_1740_;
v_a_1713_ = v___x_1787_;
goto v___jp_1699_;
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1728_);
v___x_1791_ = lean_apply_5(v___y_1729_, v___y_1728_, v___y_1737_, v___y_1733_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 1);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
v___y_1677_ = v___y_1726_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___x_1790_;
v___y_1680_ = v___y_1728_;
v___y_1681_ = v___y_1730_;
v___y_1682_ = v_a_1769_;
v___y_1683_ = v___y_1733_;
v___y_1684_ = v___y_1734_;
v___y_1685_ = v___y_1735_;
v___y_1686_ = v___y_1737_;
v___y_1687_ = v___y_1738_;
v___y_1688_ = v___y_1739_;
v___y_1689_ = v___y_1740_;
v_a_1690_ = v___x_1797_;
goto v___jp_1676_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_a_1800_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1791_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1791_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 0);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
v___y_1677_ = v___y_1726_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___x_1790_;
v___y_1680_ = v___y_1728_;
v___y_1681_ = v___y_1730_;
v___y_1682_ = v_a_1769_;
v___y_1683_ = v___y_1733_;
v___y_1684_ = v___y_1734_;
v___y_1685_ = v___y_1735_;
v___y_1686_ = v___y_1737_;
v___y_1687_ = v___y_1738_;
v___y_1688_ = v___y_1739_;
v___y_1689_ = v___y_1740_;
v_a_1690_ = v___x_1805_;
goto v___jp_1676_;
}
}
}
}
}
}
}
v___jp_1812_:
{
lean_object* v_toCold_1831_; lean_object* v_currRecDepth_1832_; lean_object* v_ref_1833_; uint8_t v_suppressElabErrors_1834_; uint8_t v_isRecordingDeps_1835_; 
v_toCold_1831_ = lean_ctor_get(v___y_1829_, 0);
lean_inc_ref(v_toCold_1831_);
v_currRecDepth_1832_ = lean_ctor_get(v___y_1829_, 1);
lean_inc(v_currRecDepth_1832_);
v_ref_1833_ = lean_ctor_get(v___y_1829_, 2);
lean_inc(v_ref_1833_);
v_suppressElabErrors_1834_ = lean_ctor_get_uint8(v___y_1829_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1835_ = lean_ctor_get_uint8(v___y_1829_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_1829_);
v___y_1726_ = v___y_1813_;
v___y_1727_ = v___y_1814_;
v___y_1728_ = v___y_1815_;
v___y_1729_ = v___y_1816_;
v___y_1730_ = v___y_1817_;
v___y_1731_ = v___y_1818_;
v___y_1732_ = v___y_1819_;
v___y_1733_ = v___y_1820_;
v___y_1734_ = v___y_1821_;
v___y_1735_ = v___y_1822_;
v___y_1736_ = v___y_1823_;
v___y_1737_ = v___y_1824_;
v___y_1738_ = v___y_1825_;
v___y_1739_ = v___y_1826_;
v___y_1740_ = v___y_1827_;
v___y_1741_ = v___y_1828_;
v_toCold_1742_ = v_toCold_1831_;
v_currRecDepth_1743_ = v_currRecDepth_1832_;
v_ref_1744_ = v_ref_1833_;
v_suppressElabErrors_1745_ = v_suppressElabErrors_1834_;
v_isRecordingDeps_1746_ = v_isRecordingDeps_1835_;
v___y_1747_ = v___y_1830_;
goto v___jp_1725_;
}
v___jp_1836_:
{
lean_object* v___x_1854_; lean_object* v_env_1855_; lean_object* v_nextMacroScope_1856_; lean_object* v_ngen_1857_; lean_object* v_auxDeclNGen_1858_; lean_object* v_traceState_1859_; lean_object* v_recordedDeps_1860_; lean_object* v_messages_1861_; lean_object* v_infoState_1862_; lean_object* v_snapshotTasks_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1873_; 
v___x_1854_ = lean_st_ref_take(v___y_1837_);
v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
v_nextMacroScope_1856_ = lean_ctor_get(v___x_1854_, 1);
v_ngen_1857_ = lean_ctor_get(v___x_1854_, 2);
v_auxDeclNGen_1858_ = lean_ctor_get(v___x_1854_, 3);
v_traceState_1859_ = lean_ctor_get(v___x_1854_, 4);
v_recordedDeps_1860_ = lean_ctor_get(v___x_1854_, 6);
v_messages_1861_ = lean_ctor_get(v___x_1854_, 7);
v_infoState_1862_ = lean_ctor_get(v___x_1854_, 8);
v_snapshotTasks_1863_ = lean_ctor_get(v___x_1854_, 9);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v___x_1854_, 5);
lean_dec(v_unused_1874_);
v___x_1865_ = v___x_1854_;
v_isShared_1866_ = v_isSharedCheck_1873_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snapshotTasks_1863_);
lean_inc(v_infoState_1862_);
lean_inc(v_messages_1861_);
lean_inc(v_recordedDeps_1860_);
lean_inc(v_traceState_1859_);
lean_inc(v_auxDeclNGen_1858_);
lean_inc(v_ngen_1857_);
lean_inc(v_nextMacroScope_1856_);
lean_inc(v_env_1855_);
lean_dec(v___x_1854_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1873_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = l_Lean_Kernel_enableDiag(v_env_1855_, v___y_1851_);
v___x_1868_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 5, v___x_1868_);
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_nextMacroScope_1856_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_ngen_1857_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_auxDeclNGen_1858_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_traceState_1859_);
lean_ctor_set(v_reuseFailAlloc_1872_, 5, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1872_, 6, v_recordedDeps_1860_);
lean_ctor_set(v_reuseFailAlloc_1872_, 7, v_messages_1861_);
lean_ctor_set(v_reuseFailAlloc_1872_, 8, v_infoState_1862_);
lean_ctor_set(v_reuseFailAlloc_1872_, 9, v_snapshotTasks_1863_);
v___x_1870_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_st_ref_put(v___y_1837_, v___x_1870_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1837_);
v___y_1813_ = v___y_1837_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1839_;
v___y_1816_ = v___y_1840_;
v___y_1817_ = v___y_1841_;
v___y_1818_ = v___y_1842_;
v___y_1819_ = v___y_1843_;
v___y_1820_ = v___y_1844_;
v___y_1821_ = v___y_1845_;
v___y_1822_ = v___y_1846_;
v___y_1823_ = v___y_1847_;
v___y_1824_ = v___y_1848_;
v___y_1825_ = v___y_1849_;
v___y_1826_ = v___y_1850_;
v___y_1827_ = v___y_1852_;
v___y_1828_ = v___y_1853_;
v___y_1829_ = v___y_1843_;
v___y_1830_ = v___y_1837_;
goto v___jp_1812_;
}
}
}
v___jp_1875_:
{
if (v___y_1879_ == 0)
{
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1876_);
v___y_1813_ = v___y_1876_;
v___y_1814_ = v___y_1877_;
v___y_1815_ = v___y_1878_;
v___y_1816_ = v___y_1880_;
v___y_1817_ = v___y_1881_;
v___y_1818_ = v___y_1882_;
v___y_1819_ = v___y_1883_;
v___y_1820_ = v___y_1884_;
v___y_1821_ = v___y_1885_;
v___y_1822_ = v___y_1886_;
v___y_1823_ = v___y_1887_;
v___y_1824_ = v___y_1888_;
v___y_1825_ = v___y_1889_;
v___y_1826_ = v___y_1890_;
v___y_1827_ = v___y_1891_;
v___y_1828_ = v___y_1892_;
v___y_1829_ = v___y_1883_;
v___y_1830_ = v___y_1876_;
goto v___jp_1812_;
}
else
{
v___y_1837_ = v___y_1876_;
v___y_1838_ = v___y_1877_;
v___y_1839_ = v___y_1878_;
v___y_1840_ = v___y_1880_;
v___y_1841_ = v___y_1881_;
v___y_1842_ = v___y_1882_;
v___y_1843_ = v___y_1883_;
v___y_1844_ = v___y_1884_;
v___y_1845_ = v___y_1885_;
v___y_1846_ = v___y_1886_;
v___y_1847_ = v___y_1887_;
v___y_1848_ = v___y_1888_;
v___y_1849_ = v___y_1889_;
v___y_1850_ = v___y_1890_;
v___y_1851_ = v___y_1893_;
v___y_1852_ = v___y_1891_;
v___y_1853_ = v___y_1892_;
goto v___jp_1836_;
}
}
v___jp_1894_:
{
lean_object* v___x_1914_; lean_object* v_a_1915_; lean_object* v_ref_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint16_t v___x_1926_; lean_object* v___x_1927_; lean_object* v_env_1928_; uint8_t v___x_1929_; uint16_t v___x_1930_; uint16_t v___x_1931_; uint16_t v___x_1932_; uint8_t v___x_1933_; 
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1895_);
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
v_ref_1916_ = l_Lean_replaceRef(v___y_1910_, v___y_1910_);
lean_inc(v_ref_1916_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1909_);
v___x_1917_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1917_, 0, v___y_1909_);
lean_ctor_set(v___x_1917_, 1, v___y_1907_);
lean_ctor_set(v___x_1917_, 2, v_ref_1916_);
lean_ctor_set_uint16(v___x_1917_, sizeof(void*)*3, v___y_1898_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*3 + 2, v___y_1899_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*3 + 3, v___y_1903_);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1919_ = 0;
v___x_1920_ = l_Lean_MessageData_ofLevel(v___y_1896_);
v___x_1921_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_MessageData_ofLevel(v___y_1901_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
lean_inc_ref(v___y_1906_);
v___x_1925_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1906_, v___x_1918_, v___x_1919_);
v___x_1926_ = l_Lean_OptionFlags_ofOptions(v___x_1925_);
v___x_1927_ = lean_st_ref_get(v___y_1895_);
v_env_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_ref(v_env_1928_);
lean_dec(v___x_1927_);
v___x_1929_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1928_);
lean_dec_ref(v_env_1928_);
v___x_1930_ = 512;
v___x_1931_ = lean_uint16_land(v___x_1926_, v___x_1930_);
v___x_1932_ = 0;
v___x_1933_ = lean_uint16_dec_eq(v___x_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
if (v___y_1911_ == 0)
{
lean_dec(v_ref_1916_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1907_);
v___y_1876_ = v___y_1895_;
v___y_1877_ = v___y_1897_;
v___y_1878_ = v___y_1900_;
v___y_1879_ = v___x_1929_;
v___y_1880_ = v___y_1902_;
v___y_1881_ = v_a_1915_;
v___y_1882_ = v___x_1925_;
v___y_1883_ = v___x_1917_;
v___y_1884_ = v___y_1904_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1905_;
v___y_1887_ = v___x_1926_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___y_1912_;
v___y_1891_ = v___y_1913_;
v___y_1892_ = v___x_1924_;
v___y_1893_ = v___y_1911_;
goto v___jp_1875_;
}
else
{
if (v___x_1929_ == 0)
{
lean_dec(v_ref_1916_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1907_);
v___y_1837_ = v___y_1895_;
v___y_1838_ = v___y_1897_;
v___y_1839_ = v___y_1900_;
v___y_1840_ = v___y_1902_;
v___y_1841_ = v_a_1915_;
v___y_1842_ = v___x_1925_;
v___y_1843_ = v___x_1917_;
v___y_1844_ = v___y_1904_;
v___y_1845_ = v___y_1906_;
v___y_1846_ = v___y_1905_;
v___y_1847_ = v___x_1926_;
v___y_1848_ = v___y_1908_;
v___y_1849_ = v___y_1910_;
v___y_1850_ = v___y_1912_;
v___y_1851_ = v___y_1911_;
v___y_1852_ = v___y_1913_;
v___y_1853_ = v___x_1924_;
goto v___jp_1836_;
}
else
{
lean_inc(v___y_1895_);
v___y_1726_ = v___y_1895_;
v___y_1727_ = v___y_1897_;
v___y_1728_ = v___y_1900_;
v___y_1729_ = v___y_1902_;
v___y_1730_ = v_a_1915_;
v___y_1731_ = v___x_1925_;
v___y_1732_ = v___x_1917_;
v___y_1733_ = v___y_1904_;
v___y_1734_ = v___y_1906_;
v___y_1735_ = v___y_1905_;
v___y_1736_ = v___x_1926_;
v___y_1737_ = v___y_1908_;
v___y_1738_ = v___y_1910_;
v___y_1739_ = v___y_1912_;
v___y_1740_ = v___y_1913_;
v___y_1741_ = v___x_1924_;
v_toCold_1742_ = v___y_1909_;
v_currRecDepth_1743_ = v___y_1907_;
v_ref_1744_ = v_ref_1916_;
v_suppressElabErrors_1745_ = v___y_1899_;
v_isRecordingDeps_1746_ = v___y_1903_;
v___y_1747_ = v___y_1895_;
goto v___jp_1725_;
}
}
}
else
{
lean_dec(v_ref_1916_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1907_);
v___y_1876_ = v___y_1895_;
v___y_1877_ = v___y_1897_;
v___y_1878_ = v___y_1900_;
v___y_1879_ = v___x_1929_;
v___y_1880_ = v___y_1902_;
v___y_1881_ = v_a_1915_;
v___y_1882_ = v___x_1925_;
v___y_1883_ = v___x_1917_;
v___y_1884_ = v___y_1904_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1905_;
v___y_1887_ = v___x_1926_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___y_1912_;
v___y_1891_ = v___y_1913_;
v___y_1892_ = v___x_1924_;
v___y_1893_ = v___x_1919_;
goto v___jp_1875_;
}
}
v___jp_1934_:
{
lean_object* v_toCold_1941_; lean_object* v_options_1942_; lean_object* v_currRecDepth_1943_; lean_object* v_ref_1944_; uint16_t v_optionFlags_1945_; uint8_t v_suppressElabErrors_1946_; uint8_t v_isRecordingDeps_1947_; lean_object* v_inheritedTraceOptions_1948_; uint8_t v_hasTrace_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___y_1958_; 
v_toCold_1941_ = lean_ctor_get(v___y_1939_, 0);
v_options_1942_ = lean_ctor_get(v_toCold_1941_, 2);
v_currRecDepth_1943_ = lean_ctor_get(v___y_1939_, 1);
v_ref_1944_ = lean_ctor_get(v___y_1939_, 2);
v_optionFlags_1945_ = lean_ctor_get_uint16(v___y_1939_, sizeof(void*)*3);
v_suppressElabErrors_1946_ = lean_ctor_get_uint8(v___y_1939_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1947_ = lean_ctor_get_uint8(v___y_1939_, sizeof(void*)*3 + 3);
v_inheritedTraceOptions_1948_ = lean_ctor_get(v_toCold_1941_, 11);
v_hasTrace_1949_ = lean_ctor_get_uint8(v_options_1942_, sizeof(void*)*1);
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1951_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1952_ = l_Lean_Level_getLevelOffset(v_lhs_1935_);
v___x_1953_ = l_Lean_Level_getLevelOffset(v_rhs_1936_);
v___x_1954_ = lean_level_eq(v___x_1952_, v___x_1953_);
lean_dec(v___x_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = 1;
v___x_1956_ = lean_box(v___x_1954_);
v___x_1957_ = lean_box(v___x_1955_);
lean_inc(v_rhs_1936_);
lean_inc(v_lhs_1935_);
v___y_1958_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1958_, 0, v___x_1956_);
lean_closure_set(v___y_1958_, 1, v___x_1950_);
lean_closure_set(v___y_1958_, 2, v___x_1951_);
lean_closure_set(v___y_1958_, 3, v_lhs_1935_);
lean_closure_set(v___y_1958_, 4, v_rhs_1936_);
lean_closure_set(v___y_1958_, 5, v___x_1957_);
if (v_hasTrace_1949_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v___y_1958_);
v___x_1959_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1954_, v___x_1950_, v___x_1951_, v_lhs_1935_, v_rhs_1936_, v___x_1955_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1960_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1961_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1962_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1948_, v_options_1942_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = l_Lean_trace_profiler;
v___x_1965_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_options_1942_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v___y_1958_);
v___x_1966_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1954_, v___x_1950_, v___x_1951_, v_lhs_1935_, v_rhs_1936_, v___x_1955_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v___x_1966_;
}
else
{
lean_inc(v_ref_1944_);
lean_inc(v_currRecDepth_1943_);
lean_inc_ref(v_options_1942_);
lean_inc_ref(v_toCold_1941_);
v___y_1895_ = v___y_1940_;
v___y_1896_ = v_lhs_1935_;
v___y_1897_ = v___x_1955_;
v___y_1898_ = v_optionFlags_1945_;
v___y_1899_ = v_suppressElabErrors_1946_;
v___y_1900_ = v___y_1937_;
v___y_1901_ = v_rhs_1936_;
v___y_1902_ = v___y_1958_;
v___y_1903_ = v_isRecordingDeps_1947_;
v___y_1904_ = v___y_1939_;
v___y_1905_ = v___x_1963_;
v___y_1906_ = v_options_1942_;
v___y_1907_ = v_currRecDepth_1943_;
v___y_1908_ = v___y_1938_;
v___y_1909_ = v_toCold_1941_;
v___y_1910_ = v_ref_1944_;
v___y_1911_ = v_hasTrace_1949_;
v___y_1912_ = v___x_1960_;
v___y_1913_ = v___x_1961_;
goto v___jp_1894_;
}
}
else
{
lean_inc(v_ref_1944_);
lean_inc(v_currRecDepth_1943_);
lean_inc_ref(v_options_1942_);
lean_inc_ref(v_toCold_1941_);
v___y_1895_ = v___y_1940_;
v___y_1896_ = v_lhs_1935_;
v___y_1897_ = v___x_1955_;
v___y_1898_ = v_optionFlags_1945_;
v___y_1899_ = v_suppressElabErrors_1946_;
v___y_1900_ = v___y_1937_;
v___y_1901_ = v_rhs_1936_;
v___y_1902_ = v___y_1958_;
v___y_1903_ = v_isRecordingDeps_1947_;
v___y_1904_ = v___y_1939_;
v___y_1905_ = v___x_1963_;
v___y_1906_ = v_options_1942_;
v___y_1907_ = v_currRecDepth_1943_;
v___y_1908_ = v___y_1938_;
v___y_1909_ = v_toCold_1941_;
v___y_1910_ = v_ref_1944_;
v___y_1911_ = v_hasTrace_1949_;
v___y_1912_ = v___x_1960_;
v___y_1913_ = v___x_1961_;
goto v___jp_1894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = lean_is_level_def_eq(v_x_1970_, v_x_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1978_, lean_object* v_x_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1979_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1986_, v_x_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2051_ = 0;
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2053_ = l_Lean_registerTraceClass(v___x_2050_, v___x_2051_, v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; 
lean_dec_ref_known(v___x_2053_, 1);
v___x_2054_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2055_ = 1;
v___x_2056_ = l_Lean_registerTraceClass(v___x_2054_, v___x_2055_, v___x_2052_);
return v___x_2056_;
}
else
{
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2058_;
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
