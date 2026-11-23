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
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_hasAssignableLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_2706__boxed_196_; size_t v_x_2707__boxed_197_; lean_object* v_res_198_; 
v_x_2706__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_x_2707__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_191_, v_x_2706__boxed_196_, v_x_2707__boxed_197_, v_x_194_, v_x_195_);
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
lean_object* v___x_210_; lean_object* v_mctx_211_; lean_object* v_cache_212_; lean_object* v_zetaDeltaFVarIds_213_; lean_object* v_postponed_214_; lean_object* v_diag_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_243_; 
v___x_210_ = lean_st_ref_take(v___y_208_);
v_mctx_211_ = lean_ctor_get(v___x_210_, 0);
v_cache_212_ = lean_ctor_get(v___x_210_, 1);
v_zetaDeltaFVarIds_213_ = lean_ctor_get(v___x_210_, 2);
v_postponed_214_ = lean_ctor_get(v___x_210_, 3);
v_diag_215_ = lean_ctor_get(v___x_210_, 4);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_243_ == 0)
{
v___x_217_ = v___x_210_;
v_isShared_218_ = v_isSharedCheck_243_;
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
v_isShared_218_ = v_isSharedCheck_243_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_depth_219_; lean_object* v_levelAssignDepth_220_; lean_object* v_lmvarCounter_221_; lean_object* v_mvarCounter_222_; lean_object* v_lDecls_223_; lean_object* v_decls_224_; lean_object* v_userNames_225_; lean_object* v_lAssignment_226_; lean_object* v_eAssignment_227_; lean_object* v_dAssignment_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_242_; 
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
v_isSharedCheck_242_ = !lean_is_exclusive(v_mctx_211_);
if (v_isSharedCheck_242_ == 0)
{
v___x_230_ = v_mctx_211_;
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
else
{
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
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v___x_233_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_226_, v_mvarId_206_, v_val_207_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 7, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_depth_219_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_levelAssignDepth_220_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_lmvarCounter_221_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_mvarCounter_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_lDecls_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_decls_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_userNames_225_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v_eAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 9, v_dAssignment_228_);
v___x_235_ = v_reuseFailAlloc_241_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_235_);
v___x_237_ = v___x_217_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_zetaDeltaFVarIds_213_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_postponed_214_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_diag_215_);
v___x_237_ = v_reuseFailAlloc_240_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_st_ref_put(v___y_208_, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_232_);
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* v_mvarId_244_, lean_object* v_val_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_244_, v_val_245_, v___y_246_);
lean_dec(v___y_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_env_256_; uint8_t v___x_257_; lean_object* v_env_258_; lean_object* v___x_259_; lean_object* v_toCold_260_; lean_object* v_mctx_261_; lean_object* v_lctx_262_; lean_object* v_options_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_255_ = lean_st_ref_get(v___y_253_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_255_);
v___x_257_ = 0;
v_env_258_ = l_Lean_Environment_setRecordingDeps(v_env_256_, v___x_257_);
v___x_259_ = lean_st_ref_get(v___y_251_);
v_toCold_260_ = lean_ctor_get(v___y_252_, 0);
v_mctx_261_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_mctx_261_);
lean_dec(v___x_259_);
v_lctx_262_ = lean_ctor_get(v___y_250_, 2);
v_options_263_ = lean_ctor_get(v_toCold_260_, 2);
lean_inc_ref(v_options_263_);
lean_inc_ref(v_lctx_262_);
v___x_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_264_, 0, v_env_258_);
lean_ctor_set(v___x_264_, 1, v_mctx_261_);
lean_ctor_set(v___x_264_, 2, v_lctx_262_);
lean_ctor_set(v___x_264_, 3, v_options_263_);
v___x_265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_msgData_249_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_274_; double v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_float_of_nat(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_279_, lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_ref_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_333_; 
v_ref_286_ = lean_ctor_get(v___y_283_, 2);
v___x_287_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_333_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_333_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_333_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v_traceState_293_; lean_object* v_env_294_; lean_object* v_nextMacroScope_295_; lean_object* v_ngen_296_; lean_object* v_auxDeclNGen_297_; lean_object* v_cache_298_; lean_object* v_recordedDeps_299_; lean_object* v_messages_300_; lean_object* v_infoState_301_; lean_object* v_snapshotTasks_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_332_; 
v___x_292_ = lean_st_ref_take(v___y_284_);
v_traceState_293_ = lean_ctor_get(v___x_292_, 4);
v_env_294_ = lean_ctor_get(v___x_292_, 0);
v_nextMacroScope_295_ = lean_ctor_get(v___x_292_, 1);
v_ngen_296_ = lean_ctor_get(v___x_292_, 2);
v_auxDeclNGen_297_ = lean_ctor_get(v___x_292_, 3);
v_cache_298_ = lean_ctor_get(v___x_292_, 5);
v_recordedDeps_299_ = lean_ctor_get(v___x_292_, 6);
v_messages_300_ = lean_ctor_get(v___x_292_, 7);
v_infoState_301_ = lean_ctor_get(v___x_292_, 8);
v_snapshotTasks_302_ = lean_ctor_get(v___x_292_, 9);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_332_ == 0)
{
v___x_304_ = v___x_292_;
v_isShared_305_ = v_isSharedCheck_332_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_snapshotTasks_302_);
lean_inc(v_infoState_301_);
lean_inc(v_messages_300_);
lean_inc(v_recordedDeps_299_);
lean_inc(v_cache_298_);
lean_inc(v_traceState_293_);
lean_inc(v_auxDeclNGen_297_);
lean_inc(v_ngen_296_);
lean_inc(v_nextMacroScope_295_);
lean_inc(v_env_294_);
lean_dec(v___x_292_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_332_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint64_t v_tid_306_; lean_object* v_traces_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_331_; 
v_tid_306_ = lean_ctor_get_uint64(v_traceState_293_, sizeof(void*)*1);
v_traces_307_ = lean_ctor_get(v_traceState_293_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_traceState_293_);
if (v_isSharedCheck_331_ == 0)
{
v___x_309_ = v_traceState_293_;
v_isShared_310_ = v_isSharedCheck_331_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_traces_307_);
lean_dec(v_traceState_293_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_331_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; double v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_box(0);
v___x_313_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_314_ = 0;
v___x_315_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_316_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_316_, 0, v_cls_279_);
lean_ctor_set(v___x_316_, 1, v___x_312_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
lean_ctor_set_float(v___x_316_, sizeof(void*)*3, v___x_313_);
lean_ctor_set_float(v___x_316_, sizeof(void*)*3 + 8, v___x_313_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*3 + 16, v___x_314_);
v___x_317_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_318_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v_a_288_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_inc(v_ref_286_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_ref_286_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Lean_PersistentArray_push___redArg(v_traces_307_, v___x_319_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_320_);
v___x_322_ = v___x_309_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_320_);
lean_ctor_set_uint64(v_reuseFailAlloc_330_, sizeof(void*)*1, v_tid_306_);
v___x_322_ = v_reuseFailAlloc_330_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v___x_322_);
v___x_324_ = v___x_304_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_env_294_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_nextMacroScope_295_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_ngen_296_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_auxDeclNGen_297_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 5, v_cache_298_);
lean_ctor_set(v_reuseFailAlloc_329_, 6, v_recordedDeps_299_);
lean_ctor_set(v_reuseFailAlloc_329_, 7, v_messages_300_);
lean_ctor_set(v_reuseFailAlloc_329_, 8, v_infoState_301_);
lean_ctor_set(v_reuseFailAlloc_329_, 9, v_snapshotTasks_302_);
v___x_324_ = v_reuseFailAlloc_329_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_st_ref_put(v___y_284_, v___x_324_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_311_);
v___x_327_ = v___x_290_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_311_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_334_, lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_334_, v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = lean_unsigned_to_nat(39u);
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_350_ = l_mkPanicMessageWithDecl(v___x_349_, v___x_348_, v___x_347_, v___x_346_, v___x_345_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_363_ = l_Lean_Name_append(v___x_362_, v___x_361_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_370_, lean_object* v_v_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_Level_isMax(v_v_371_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_v_371_);
lean_dec(v_mvarId_370_);
v___x_378_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_379_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_378_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_mkFreshLevelMVar(v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_toCold_381_; lean_object* v_options_382_; lean_object* v_a_383_; lean_object* v_inheritedTraceOptions_384_; uint8_t v_hasTrace_385_; lean_object* v___x_386_; 
v_toCold_381_ = lean_ctor_get(v_a_374_, 0);
v_options_382_ = lean_ctor_get(v_toCold_381_, 2);
v_a_383_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_380_, 1);
v_inheritedTraceOptions_384_ = lean_ctor_get(v_toCold_381_, 11);
v_hasTrace_385_ = lean_ctor_get_uint8(v_options_382_, sizeof(void*)*1);
v___x_386_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_370_, v_v_371_, v_a_383_);
if (v_hasTrace_385_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_370_, v___x_386_, v_a_373_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_389_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_384_, v_options_382_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_370_, v___x_386_, v_a_373_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_370_);
v___x_393_ = l_Lean_mkLevelMVar(v_mvarId_370_);
v___x_394_ = l_Lean_MessageData_ofLevel(v___x_393_);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_392_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
lean_inc(v___x_386_);
v___x_398_ = l_Lean_MessageData_ofLevel(v___x_386_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_388_, v___x_399_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
lean_dec_ref_known(v___x_400_, 1);
v___x_401_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_370_, v___x_386_, v_a_373_);
return v___x_401_;
}
else
{
lean_dec(v___x_386_);
lean_dec(v_mvarId_370_);
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_v_371_);
lean_dec(v_mvarId_370_);
v_a_402_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_380_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_380_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_410_, lean_object* v_v_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_410_, v_v_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_418_, lean_object* v_val_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_418_, v_val_419_, v___y_421_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_426_, lean_object* v_val_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_426_, v_val_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_435_, v_x_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, size_t v_x_441_, size_t v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_440_, v_x_441_, v_x_442_, v_x_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
size_t v_x_3216__boxed_452_; size_t v_x_3217__boxed_453_; lean_object* v_res_454_; 
v_x_3216__boxed_452_ = lean_unbox_usize(v_x_448_);
lean_dec(v_x_448_);
v_x_3217__boxed_453_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_res_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_446_, v_x_447_, v_x_3216__boxed_452_, v_x_3217__boxed_453_, v_x_450_, v_x_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_455_, lean_object* v_n_456_, lean_object* v_k_457_, lean_object* v_v_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_456_, v_k_457_, v_v_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_460_, size_t v_depth_461_, lean_object* v_keys_462_, lean_object* v_vals_463_, lean_object* v_heq_464_, lean_object* v_i_465_, lean_object* v_entries_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_461_, v_keys_462_, v_vals_463_, v_i_465_, v_entries_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_468_, lean_object* v_depth_469_, lean_object* v_keys_470_, lean_object* v_vals_471_, lean_object* v_heq_472_, lean_object* v_i_473_, lean_object* v_entries_474_){
_start:
{
size_t v_depth_boxed_475_; lean_object* v_res_476_; 
v_depth_boxed_475_ = lean_unbox_usize(v_depth_469_);
lean_dec(v_depth_469_);
v_res_476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_468_, v_depth_boxed_475_, v_keys_470_, v_vals_471_, v_heq_472_, v_i_473_, v_entries_474_);
lean_dec_ref(v_vals_471_);
lean_dec_ref(v_keys_470_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_478_, v_x_479_, v_x_480_, v_x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_486_, lean_object* v_v_x27_487_, lean_object* v_mvarId_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
uint8_t v___x_494_; lean_object* v___y_496_; 
v___x_494_ = lean_level_eq(v_u_486_, v_v_x27_487_);
if (v___x_494_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_mvarId_488_);
lean_dec(v_u_486_);
v___x_507_ = lean_box(v___x_494_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v_toCold_509_; lean_object* v_options_510_; uint8_t v_hasTrace_511_; 
v_toCold_509_ = lean_ctor_get(v_a_491_, 0);
v_options_510_ = lean_ctor_get(v_toCold_509_, 2);
v_hasTrace_511_ = lean_ctor_get_uint8(v_options_510_, sizeof(void*)*1);
if (v_hasTrace_511_ == 0)
{
v___y_496_ = v_a_490_;
goto v___jp_495_;
}
else
{
lean_object* v_inheritedTraceOptions_512_; lean_object* v_cls_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_inheritedTraceOptions_512_ = lean_ctor_get(v_toCold_509_, 11);
v_cls_513_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_514_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_515_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_512_, v_options_510_, v___x_514_);
if (v___x_515_ == 0)
{
v___y_496_ = v_a_490_;
goto v___jp_495_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_516_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_488_);
v___x_517_ = l_Lean_mkLevelMVar(v_mvarId_488_);
v___x_518_ = l_Lean_MessageData_ofLevel(v___x_517_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_516_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
lean_inc(v_u_486_);
v___x_522_ = l_Lean_MessageData_ofLevel(v_u_486_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_513_, v___x_523_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref_known(v___x_524_, 1);
v___y_496_ = v_a_490_;
goto v___jp_495_;
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_mvarId_488_);
lean_dec(v_u_486_);
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v___x_497_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_488_, v_u_486_, v___y_496_);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_506_);
v___x_499_ = v___x_497_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_dec(v___x_497_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_box(v___x_494_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_533_, lean_object* v_v_x27_534_, lean_object* v_mvarId_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_533_, v_v_x27_534_, v_mvarId_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_v_x27_534_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_542_, lean_object* v_v_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
if (lean_obj_tag(v_v_543_) == 2)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v_v_543_, 1);
lean_inc(v_a_553_);
if (lean_obj_tag(v_a_553_) == 5)
{
lean_object* v_a_554_; lean_object* v_a_555_; lean_object* v___x_556_; 
v_a_554_ = lean_ctor_get(v_v_543_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v_v_543_, 2);
v_a_555_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v_a_553_, 1);
v___x_556_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_542_, v_a_554_, v_a_555_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_554_);
return v___x_556_;
}
else
{
lean_object* v_a_557_; 
v_a_557_ = lean_ctor_get(v_v_543_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v_v_543_, 2);
if (lean_obj_tag(v_a_557_) == 5)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v_a_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_a_557_, 1);
v___x_559_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_542_, v_a_553_, v_a_558_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_553_);
return v___x_559_;
}
else
{
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_u_542_);
goto v___jp_549_;
}
}
}
else
{
lean_dec(v_v_543_);
lean_dec(v_u_542_);
goto v___jp_549_;
}
v___jp_549_:
{
uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = 0;
v___x_551_ = lean_box(v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_560_, lean_object* v_v_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_560_, v_v_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_571_, lean_object* v_u_u2082_572_, lean_object* v_v_x27_573_, lean_object* v_mvarId_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
uint8_t v___x_580_; uint8_t v___x_581_; lean_object* v___y_583_; lean_object* v___y_595_; 
v___x_580_ = lean_level_eq(v_u_u2081_571_, v_v_x27_573_);
v___x_581_ = 1;
if (v___x_580_ == 0)
{
uint8_t v___x_606_; 
v___x_606_ = lean_level_eq(v_u_u2082_572_, v_v_x27_573_);
lean_dec(v_u_u2082_572_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_mvarId_574_);
lean_dec(v_u_u2081_571_);
v___x_607_ = lean_box(v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_toCold_609_; lean_object* v_options_610_; uint8_t v_hasTrace_611_; 
v_toCold_609_ = lean_ctor_get(v_a_577_, 0);
v_options_610_ = lean_ctor_get(v_toCold_609_, 2);
v_hasTrace_611_ = lean_ctor_get_uint8(v_options_610_, sizeof(void*)*1);
if (v_hasTrace_611_ == 0)
{
v___y_595_ = v_a_576_;
goto v___jp_594_;
}
else
{
lean_object* v_inheritedTraceOptions_612_; lean_object* v_cls_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_inheritedTraceOptions_612_ = lean_ctor_get(v_toCold_609_, 11);
v_cls_613_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_614_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_612_, v_options_610_, v___x_614_);
if (v___x_615_ == 0)
{
v___y_595_ = v_a_576_;
goto v___jp_594_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_574_);
v___x_617_ = l_Lean_mkLevelMVar(v_mvarId_574_);
v___x_618_ = l_Lean_MessageData_ofLevel(v___x_617_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_616_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc(v_u_u2081_571_);
v___x_622_ = l_Lean_MessageData_ofLevel(v_u_u2081_571_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_613_, v___x_623_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref_known(v___x_624_, 1);
v___y_595_ = v_a_576_;
goto v___jp_594_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_mvarId_574_);
lean_dec(v_u_u2081_571_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_633_; lean_object* v_options_634_; uint8_t v_hasTrace_635_; 
lean_dec(v_u_u2081_571_);
v_toCold_633_ = lean_ctor_get(v_a_577_, 0);
v_options_634_ = lean_ctor_get(v_toCold_633_, 2);
v_hasTrace_635_ = lean_ctor_get_uint8(v_options_634_, sizeof(void*)*1);
if (v_hasTrace_635_ == 0)
{
v___y_583_ = v_a_576_;
goto v___jp_582_;
}
else
{
lean_object* v_inheritedTraceOptions_636_; lean_object* v_cls_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_inheritedTraceOptions_636_ = lean_ctor_get(v_toCold_633_, 11);
v_cls_637_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_638_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_636_, v_options_634_, v___x_638_);
if (v___x_639_ == 0)
{
v___y_583_ = v_a_576_;
goto v___jp_582_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_640_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_574_);
v___x_641_ = l_Lean_mkLevelMVar(v_mvarId_574_);
v___x_642_ = l_Lean_MessageData_ofLevel(v___x_641_);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_640_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_inc(v_u_u2082_572_);
v___x_646_ = l_Lean_MessageData_ofLevel(v_u_u2082_572_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_637_, v___x_647_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_dec_ref_known(v___x_648_, 1);
v___y_583_ = v_a_576_;
goto v___jp_582_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_mvarId_574_);
lean_dec(v_u_u2082_572_);
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
v___jp_582_:
{
lean_object* v___x_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v___x_584_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_574_, v_u_u2082_572_, v___y_583_);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_593_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_box(v___x_581_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
v___jp_594_:
{
lean_object* v___x_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v___x_596_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_574_, v_u_u2081_571_, v___y_595_);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_596_, 0);
lean_dec(v_unused_605_);
v___x_598_ = v___x_596_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_dec(v___x_596_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_box(v___x_581_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
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
lean_dec_ref_known(v_u_667_, 2);
v_a_681_ = lean_ctor_get(v_v_668_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v_v_668_, 2);
v_a_682_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v_a_678_, 1);
v___x_683_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_681_);
return v___x_683_;
}
else
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v_v_668_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v_v_668_, 2);
if (lean_obj_tag(v_a_684_) == 5)
{
lean_object* v_a_685_; lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_685_ = lean_ctor_get(v_u_667_, 0);
lean_inc(v_a_685_);
v_a_686_ = lean_ctor_get(v_u_667_, 1);
lean_inc(v_a_686_);
lean_dec_ref_known(v_u_667_, 2);
v_a_687_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v_a_684_, 1);
v___x_688_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_685_, v_a_686_, v_a_678_, v_a_687_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_678_);
return v___x_688_;
}
else
{
lean_dec(v_a_684_);
lean_dec(v_a_678_);
lean_dec_ref_known(v_u_667_, 2);
goto v___jp_674_;
}
}
}
else
{
lean_dec_ref_known(v_u_667_, 2);
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
lean_object* v_toCold_715_; lean_object* v_ref_716_; lean_object* v___y_718_; lean_object* v_options_738_; uint8_t v_hasTrace_739_; 
v_toCold_715_ = lean_ctor_get(v_a_712_, 0);
v_ref_716_ = lean_ctor_get(v_a_712_, 2);
v_options_738_ = lean_ctor_get(v_toCold_715_, 2);
v_hasTrace_739_ = lean_ctor_get_uint8(v_options_738_, sizeof(void*)*1);
if (v_hasTrace_739_ == 0)
{
v___y_718_ = v_a_711_;
goto v___jp_717_;
}
else
{
lean_object* v_inheritedTraceOptions_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_inheritedTraceOptions_740_ = lean_ctor_get(v_toCold_715_, 11);
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_740_, v_options_738_, v___x_742_);
if (v___x_743_ == 0)
{
v___y_718_ = v_a_711_;
goto v___jp_717_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_inc(v_lhs_708_);
v___x_744_ = l_Lean_MessageData_ofLevel(v_lhs_708_);
v___x_745_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
lean_inc(v_rhs_709_);
v___x_747_ = l_Lean_MessageData_ofLevel(v_rhs_709_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_741_, v___x_748_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec_ref_known(v___x_749_, 1);
v___y_718_ = v_a_711_;
goto v___jp_717_;
}
else
{
lean_dec(v_rhs_709_);
lean_dec(v_lhs_708_);
return v___x_749_;
}
}
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v_mctx_720_; lean_object* v_cache_721_; lean_object* v_zetaDeltaFVarIds_722_; lean_object* v_postponed_723_; lean_object* v_diag_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_737_; 
v___x_719_ = lean_st_ref_take(v___y_718_);
v_mctx_720_ = lean_ctor_get(v___x_719_, 0);
v_cache_721_ = lean_ctor_get(v___x_719_, 1);
v_zetaDeltaFVarIds_722_ = lean_ctor_get(v___x_719_, 2);
v_postponed_723_ = lean_ctor_get(v___x_719_, 3);
v_diag_724_ = lean_ctor_get(v___x_719_, 4);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_737_ == 0)
{
v___x_726_ = v___x_719_;
v_isShared_727_ = v_isSharedCheck_737_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_diag_724_);
lean_inc(v_postponed_723_);
lean_inc(v_zetaDeltaFVarIds_722_);
lean_inc(v_cache_721_);
lean_inc(v_mctx_720_);
lean_dec(v___x_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_737_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_defEqCtx_x3f_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_defEqCtx_x3f_728_ = lean_ctor_get(v_a_710_, 4);
v___x_729_ = lean_box(0);
lean_inc(v_defEqCtx_x3f_728_);
lean_inc(v_ref_716_);
v___x_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_730_, 0, v_ref_716_);
lean_ctor_set(v___x_730_, 1, v_lhs_708_);
lean_ctor_set(v___x_730_, 2, v_rhs_709_);
lean_ctor_set(v___x_730_, 3, v_defEqCtx_x3f_728_);
v___x_731_ = l_Lean_PersistentArray_push___redArg(v_postponed_723_, v___x_730_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 3, v___x_731_);
v___x_733_ = v___x_726_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_mctx_720_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_cache_721_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_zetaDeltaFVarIds_722_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_diag_724_);
v___x_733_ = v_reuseFailAlloc_736_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_st_ref_put(v___y_718_, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_729_);
return v___x_735_;
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
lean_dec_ref_known(v_v_758_, 1);
v___x_766_ = l_Lean_LMVarId_getLevel(v_a_765_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
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
uint8_t v_a_814_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_873_; lean_object* v___y_887_; 
switch(lean_obj_tag(v_u_806_))
{
case 5:
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v_u_806_, 0);
lean_inc(v_a_900_);
v___x_901_ = l_Lean_LMVarId_isReadOnly(v_a_900_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_998_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_998_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_998_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_998_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
uint8_t v___x_906_; 
v___x_906_ = lean_unbox(v_a_902_);
lean_dec(v_a_902_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_del_object(v___x_904_);
lean_inc(v_a_900_);
lean_inc(v_v_807_);
v___x_907_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_807_, v_a_900_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_984_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_984_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_984_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_984_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
uint8_t v___x_918_; 
v___x_918_ = lean_unbox(v_a_908_);
lean_dec(v_a_908_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_Level_occurs(v_u_806_, v_v_807_);
if (v___x_919_ == 0)
{
lean_object* v_toCold_920_; lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
lean_del_object(v___x_910_);
v_toCold_920_ = lean_ctor_get(v_a_810_, 0);
v_options_921_ = lean_ctor_get(v_toCold_920_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_873_ = v_a_809_;
goto v___jp_872_;
}
else
{
lean_object* v_inheritedTraceOptions_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_inheritedTraceOptions_923_ = lean_ctor_get(v_toCold_920_, 11);
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_923_, v_options_921_, v___x_925_);
if (v___x_926_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_873_ = v_a_809_;
goto v___jp_872_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc_ref(v_u_806_);
v___x_927_ = l_Lean_MessageData_ofLevel(v_u_806_);
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
lean_inc(v_v_807_);
v___x_930_ = l_Lean_MessageData_ofLevel(v_v_807_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_924_, v___x_931_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_dec_ref_known(v___x_932_, 1);
v___y_873_ = v_a_809_;
goto v___jp_872_;
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_809_);
lean_dec(v_v_807_);
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
else
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_Level_isMax(v_v_807_);
if (v___x_941_ == 0)
{
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
goto v___jp_912_;
}
else
{
uint8_t v___x_942_; 
v___x_942_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_806_, v_v_807_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_910_);
v___x_943_ = l_Lean_Level_mvarId_x21(v_u_806_);
lean_dec_ref_known(v_u_806_, 1);
v___x_944_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_943_, v_v_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_954_);
v___x_946_ = v___x_944_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_dec(v___x_944_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = 1;
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
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_a_955_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_944_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_944_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
goto v___jp_912_;
}
}
}
}
else
{
lean_object* v_toCold_963_; lean_object* v_options_964_; uint8_t v_hasTrace_965_; 
lean_del_object(v___x_910_);
v_toCold_963_ = lean_ctor_get(v_a_810_, 0);
v_options_964_ = lean_ctor_get(v_toCold_963_, 2);
v_hasTrace_965_ = lean_ctor_get_uint8(v_options_964_, sizeof(void*)*1);
if (v_hasTrace_965_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_887_ = v_a_809_;
goto v___jp_886_;
}
else
{
lean_object* v_inheritedTraceOptions_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_inheritedTraceOptions_966_ = lean_ctor_get(v_toCold_963_, 11);
v___x_967_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_968_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_966_, v_options_964_, v___x_968_);
if (v___x_969_ == 0)
{
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
v___y_887_ = v_a_809_;
goto v___jp_886_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc(v_v_807_);
v___x_970_ = l_Lean_MessageData_ofLevel(v_v_807_);
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_inc_ref(v_u_806_);
v___x_973_ = l_Lean_MessageData_ofLevel(v_u_806_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_967_, v___x_974_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_808_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec_ref_known(v___x_975_, 1);
v___y_887_ = v_a_809_;
goto v___jp_886_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_809_);
lean_dec(v_v_807_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
v___jp_912_:
{
uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_913_ = 2;
v___x_914_ = lean_box(v___x_913_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_914_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v_a_985_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_907_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_907_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v___x_993_ = 2;
v___x_994_ = lean_box(v___x_993_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_994_);
v___x_996_ = v___x_904_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
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
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref_known(v_u_806_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v_a_999_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_901_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_901_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
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
lean_dec_ref_known(v_v_807_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
goto v___jp_868_;
}
case 2:
{
lean_object* v_a_1007_; lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1007_ = lean_ctor_get(v_v_807_, 0);
lean_inc(v_a_1007_);
v_a_1008_ = lean_ctor_get(v_v_807_, 1);
lean_inc(v_a_1008_);
lean_dec_ref_known(v_v_807_, 2);
lean_inc(v_a_811_);
lean_inc_ref(v_a_810_);
lean_inc(v_a_809_);
lean_inc_ref(v_a_808_);
v___x_1009_ = lean_is_level_def_eq(v_u_806_, v_a_1007_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; uint8_t v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_unbox(v_a_1010_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; 
lean_dec(v_a_1008_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v___x_1012_ = lean_unbox(v_a_1010_);
lean_dec(v_a_1010_);
v_a_814_ = v___x_1012_;
goto v___jp_813_;
}
else
{
lean_object* v___x_1013_; 
lean_dec(v_a_1010_);
v___x_1013_ = lean_is_level_def_eq(v_u_806_, v_a_1008_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; uint8_t v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_unbox(v_a_1014_);
lean_dec(v_a_1014_);
v_a_814_ = v___x_1015_;
goto v___jp_813_;
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1013_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1013_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_a_1008_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v_a_1024_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1009_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1009_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
case 3:
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1032_ = lean_ctor_get(v_v_807_, 1);
lean_inc(v_a_1032_);
lean_dec_ref_known(v_v_807_, 2);
v___x_1033_ = lean_is_level_def_eq(v_u_806_, v_a_1032_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1044_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1038_ = lean_unbox(v_a_1034_);
lean_dec(v_a_1034_);
v___x_1039_ = l_Lean_Bool_toLBool(v___x_1038_);
v___x_1040_ = lean_box(v___x_1039_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1040_);
v___x_1042_ = v___x_1036_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1033_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1033_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
case 1:
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref_known(v_v_807_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
v___x_1053_ = 0;
v___x_1054_ = lean_box(v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
default: 
{
v___y_823_ = v_a_808_;
v___y_824_ = v_a_809_;
v___y_825_ = v_a_810_;
v___y_826_ = v_a_811_;
goto v___jp_822_;
}
}
}
case 1:
{
lean_object* v_a_1056_; 
v_a_1056_ = lean_ctor_get(v_u_806_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v_u_806_, 1);
if (lean_obj_tag(v_v_807_) == 5)
{
lean_dec_ref_known(v_v_807_, 1);
lean_dec(v_a_1056_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
goto v___jp_868_;
}
else
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Level_isParam(v_v_807_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Lean_Level_isMVar(v_a_1056_);
if (v___x_1099_ == 0)
{
goto v___jp_1057_;
}
else
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Lean_Level_occurs(v_a_1056_, v_v_807_);
if (v___x_1100_ == 0)
{
goto v___jp_1057_;
}
else
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_a_1056_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v___x_1101_ = 2;
v___x_1102_ = lean_box(v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
}
else
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_a_1056_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_v_807_);
v___x_1104_ = 0;
v___x_1105_ = lean_box(v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
v___jp_1057_:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_decLevel_x3f(v_v_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
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
lean_dec(v_a_1056_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
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
v___x_1069_ = lean_is_level_def_eq(v_a_1056_, v_val_1068_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
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
lean_dec(v_a_1056_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
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
}
default: 
{
if (lean_obj_tag(v_v_807_) == 5)
{
lean_dec_ref_known(v_v_807_, 1);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_u_806_);
goto v___jp_868_;
}
else
{
v___y_823_ = v_a_808_;
v___y_824_ = v_a_809_;
v___y_825_ = v_a_810_;
v___y_826_ = v_a_811_;
goto v___jp_822_;
}
}
}
v___jp_813_:
{
uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_Bool_toLBool(v_a_814_);
v___x_816_ = lean_box(v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
v___jp_818_:
{
uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = 2;
v___x_820_ = lean_box(v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
v___jp_822_:
{
uint8_t v_univApprox_827_; 
v_univApprox_827_ = lean_ctor_get_uint8(v___y_823_, sizeof(void*)*7 + 1);
if (v_univApprox_827_ == 0)
{
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v_v_807_);
lean_dec(v_u_806_);
goto v___jp_818_;
}
else
{
lean_object* v___x_828_; 
lean_inc(v_v_807_);
lean_inc(v_u_806_);
v___x_828_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_806_, v_v_807_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_859_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_859_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_859_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_859_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = lean_unbox(v_a_829_);
lean_dec(v_a_829_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_del_object(v___x_831_);
v___x_834_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_806_, v_v_807_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_845_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; 
v___x_839_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_839_ == 0)
{
lean_del_object(v___x_837_);
goto v___jp_818_;
}
else
{
uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = 1;
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
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_834_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_834_);
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
else
{
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v_v_807_);
lean_dec(v_u_806_);
v___x_854_ = 1;
v___x_855_ = lean_box(v___x_854_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_855_);
v___x_857_ = v___x_831_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v_v_807_);
lean_dec(v_u_806_);
v_a_860_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_828_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_828_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
v___jp_868_:
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = 2;
v___x_870_ = lean_box(v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_884_; 
v___x_874_ = l_Lean_Level_mvarId_x21(v_u_806_);
lean_dec(v_u_806_);
v___x_875_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_874_, v_v_807_, v___y_873_);
lean_dec(v___y_873_);
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
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_898_; 
v___x_888_ = l_Lean_Level_mvarId_x21(v_v_807_);
lean_dec(v_v_807_);
v___x_889_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_888_, v_u_806_, v___y_887_);
lean_dec(v___y_887_);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_889_, 0);
lean_dec(v_unused_899_);
v___x_891_ = v___x_889_;
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
else
{
lean_dec(v___x_889_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_893_ = 1;
v___x_894_ = lean_box(v___x_893_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1264_, lean_object* v_lhs_1265_, lean_object* v_rhs_1266_, uint8_t v___x_1267_, lean_object* v___x_1268_, lean_object* v___x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
if (v___x_1264_ == 0)
{
lean_object* v___x_1294_; lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_a_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
lean_inc(v_lhs_1265_);
v___x_1294_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1265_, v___y_1271_);
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref(v___x_1294_);
v___x_1296_ = l_Lean_Level_normalize(v_a_1295_);
lean_dec(v_a_1295_);
lean_inc(v_rhs_1266_);
v___x_1297_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1266_, v___y_1271_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = l_Lean_Level_normalize(v_a_1298_);
lean_dec(v_a_1298_);
v___x_1300_ = lean_level_eq(v_lhs_1265_, v___x_1296_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
v___x_1301_ = lean_is_level_def_eq(v___x_1296_, v___x_1299_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1301_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_level_eq(v_rhs_1266_, v___x_1299_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
v___x_1303_ = lean_is_level_def_eq(v___x_1296_, v___x_1299_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; 
lean_dec(v___x_1299_);
lean_dec(v___x_1296_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v_rhs_1266_);
lean_inc(v_lhs_1265_);
v___x_1304_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1265_, v_rhs_1266_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1391_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1391_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1391_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
uint8_t v___x_1309_; uint8_t v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = 2;
v___x_1310_ = lean_unbox(v_a_1305_);
v___x_1311_ = l_Lean_instBEqLBool_beq(v___x_1310_, v___x_1309_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; uint8_t v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v___x_1312_ = 1;
v___x_1313_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
v___x_1314_ = l_Lean_instBEqLBool_beq(v___x_1313_, v___x_1312_);
v___x_1315_ = lean_box(v___x_1314_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1315_);
v___x_1317_ = v___x_1307_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v___x_1319_; 
lean_del_object(v___x_1307_);
lean_dec(v_a_1305_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v_lhs_1265_);
lean_inc(v_rhs_1266_);
v___x_1319_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1266_, v_lhs_1265_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1382_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1382_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1382_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
uint8_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_unbox(v_a_1320_);
v___x_1325_ = l_Lean_instBEqLBool_beq(v___x_1324_, v___x_1309_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; uint8_t v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v___x_1326_ = 1;
v___x_1327_ = lean_unbox(v_a_1320_);
lean_dec(v_a_1320_);
v___x_1328_ = l_Lean_instBEqLBool_beq(v___x_1327_, v___x_1326_);
v___x_1329_ = lean_box(v___x_1328_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1329_);
v___x_1331_ = v___x_1322_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
else
{
lean_object* v___x_1333_; 
lean_del_object(v___x_1322_);
lean_dec(v_a_1320_);
lean_inc(v_lhs_1265_);
v___x_1333_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1265_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; uint8_t v___x_1335_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = lean_unbox(v_a_1334_);
lean_dec(v_a_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_inc(v_rhs_1266_);
v___x_1336_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1266_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1381_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1381_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1381_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_unbox(v_a_1337_);
lean_dec(v_a_1337_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; uint8_t v_isDefEqStuckEx_1370_; 
v___x_1369_ = l_Lean_Meta_Context_config(v___y_1270_);
v_isDefEqStuckEx_1370_ = lean_ctor_get_uint8(v___x_1369_, 4);
lean_dec_ref(v___x_1369_);
if (v_isDefEqStuckEx_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v___x_1371_ = lean_box(v___x_1264_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1371_);
v___x_1373_ = v___x_1339_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Lean_Level_isMVar(v_lhs_1265_);
if (v___x_1375_ == 0)
{
uint8_t v___x_1376_; 
v___x_1376_ = l_Lean_Level_isMVar(v_rhs_1266_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v___x_1377_ = lean_box(v___x_1376_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1377_);
v___x_1379_ = v___x_1339_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_del_object(v___x_1339_);
goto v___jp_1341_;
}
}
else
{
lean_del_object(v___x_1339_);
goto v___jp_1341_;
}
}
}
else
{
lean_del_object(v___x_1339_);
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
goto v___jp_1275_;
}
v___jp_1341_:
{
lean_object* v_toCold_1342_; lean_object* v_options_1343_; uint8_t v_hasTrace_1344_; 
v_toCold_1342_ = lean_ctor_get(v___y_1272_, 0);
v_options_1343_ = lean_ctor_get(v_toCold_1342_, 2);
v_hasTrace_1344_ = lean_ctor_get_uint8(v_options_1343_, sizeof(void*)*1);
if (v_hasTrace_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v___x_1345_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1345_;
}
else
{
lean_object* v_inheritedTraceOptions_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_inheritedTraceOptions_1346_ = lean_ctor_get(v_toCold_1342_, 11);
v___x_1347_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1348_ = l_Lean_Name_mkStr3(v___x_1268_, v___x_1269_, v___x_1347_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1348_);
v___x_1350_ = l_Lean_Name_append(v___x_1349_, v___x_1348_);
v___x_1351_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1346_, v_options_1343_, v___x_1350_);
lean_dec(v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v___x_1348_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v___x_1352_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1353_ = l_Lean_MessageData_ofLevel(v_lhs_1265_);
v___x_1354_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_MessageData_ofLevel(v_rhs_1266_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1348_, v___x_1357_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref_known(v___x_1358_, 1);
v___x_1359_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1359_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1358_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
return v___x_1336_;
}
}
else
{
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
goto v___jp_1275_;
}
}
else
{
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v_a_1383_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1319_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1319_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
lean_dec(v_rhs_1266_);
lean_dec(v_lhs_1265_);
v_a_1392_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1304_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1304_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v___x_1268_);
v___x_1400_ = l_Lean_Level_getOffset(v_lhs_1265_);
lean_dec(v_lhs_1265_);
v___x_1401_ = l_Lean_Level_getOffset(v_rhs_1266_);
lean_dec(v_rhs_1266_);
v___x_1402_ = lean_nat_dec_eq(v___x_1400_, v___x_1401_);
lean_dec(v___x_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(v___x_1402_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
v___jp_1275_:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1265_, v_rhs_1266_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1284_; 
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1276_, 0);
lean_dec(v_unused_1285_);
v___x_1278_ = v___x_1276_;
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
else
{
lean_dec(v___x_1276_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1284_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_box(v___x_1267_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1276_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1276_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1405_, lean_object* v_lhs_1406_, lean_object* v_rhs_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v___x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_13576__boxed_1416_; uint8_t v___x_13577__boxed_1417_; lean_object* v_res_1418_; 
v___x_13576__boxed_1416_ = lean_unbox(v___x_1405_);
v___x_13577__boxed_1417_ = lean_unbox(v___x_1408_);
v_res_1418_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13576__boxed_1416_, v_lhs_1406_, v_rhs_1407_, v___x_13577__boxed_1417_, v___x_1409_, v___x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1419_){
_start:
{
if (lean_obj_tag(v_e_1419_) == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = 2;
return v___x_1420_;
}
else
{
lean_object* v_a_1421_; uint8_t v___x_1422_; 
v_a_1421_ = lean_ctor_get(v_e_1419_, 0);
v___x_1422_ = lean_unbox(v_a_1421_);
if (v___x_1422_ == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = 1;
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = 0;
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1425_);
lean_dec_ref(v_e_1425_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v_x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v_x_1428_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v_x_1428_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v_x_1428_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v_x_1428_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v_x_1428_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 0);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1449_, size_t v_i_1450_, lean_object* v_bs_1451_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_usize_dec_lt(v_i_1450_, v_sz_1449_);
if (v___x_1452_ == 0)
{
return v_bs_1451_;
}
else
{
lean_object* v_v_1453_; lean_object* v_msg_1454_; lean_object* v___x_1455_; lean_object* v_bs_x27_1456_; size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v_v_1453_ = lean_array_uget_borrowed(v_bs_1451_, v_i_1450_);
v_msg_1454_ = lean_ctor_get(v_v_1453_, 1);
lean_inc_ref(v_msg_1454_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v_bs_x27_1456_ = lean_array_uset(v_bs_1451_, v_i_1450_, v___x_1455_);
v___x_1457_ = ((size_t)1ULL);
v___x_1458_ = lean_usize_add(v_i_1450_, v___x_1457_);
v___x_1459_ = lean_array_uset(v_bs_x27_1456_, v_i_1450_, v_msg_1454_);
v_i_1450_ = v___x_1458_;
v_bs_1451_ = v___x_1459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1461_, lean_object* v_i_1462_, lean_object* v_bs_1463_){
_start:
{
size_t v_sz_boxed_1464_; size_t v_i_boxed_1465_; lean_object* v_res_1466_; 
v_sz_boxed_1464_ = lean_unbox_usize(v_sz_1461_);
lean_dec(v_sz_1461_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1462_);
lean_dec(v_i_1462_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1464_, v_i_boxed_1465_, v_bs_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1467_, lean_object* v_data_1468_, lean_object* v_ref_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_toCold_1476_; lean_object* v_currRecDepth_1477_; lean_object* v_ref_1478_; uint16_t v_optionFlags_1479_; uint8_t v_suppressElabErrors_1480_; uint8_t v_checkDeprecated_1481_; uint8_t v_isRecordingDeps_1482_; lean_object* v_ref_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v_traceState_1486_; lean_object* v_traces_1487_; lean_object* v___x_1488_; size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v_msg_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1532_; 
v_toCold_1476_ = lean_ctor_get(v___y_1473_, 0);
v_currRecDepth_1477_ = lean_ctor_get(v___y_1473_, 1);
v_ref_1478_ = lean_ctor_get(v___y_1473_, 2);
v_optionFlags_1479_ = lean_ctor_get_uint16(v___y_1473_, sizeof(void*)*3);
v_suppressElabErrors_1480_ = lean_ctor_get_uint8(v___y_1473_, sizeof(void*)*3 + 2);
v_checkDeprecated_1481_ = lean_ctor_get_uint8(v___y_1473_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1482_ = lean_ctor_get_uint8(v___y_1473_, sizeof(void*)*3 + 4);
v_ref_1483_ = l_Lean_replaceRef(v_ref_1469_, v_ref_1478_);
lean_inc(v_currRecDepth_1477_);
lean_inc_ref(v_toCold_1476_);
v___x_1484_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1484_, 0, v_toCold_1476_);
lean_ctor_set(v___x_1484_, 1, v_currRecDepth_1477_);
lean_ctor_set(v___x_1484_, 2, v_ref_1483_);
lean_ctor_set_uint16(v___x_1484_, sizeof(void*)*3, v_optionFlags_1479_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 2, v_suppressElabErrors_1480_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 3, v_checkDeprecated_1481_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 4, v_isRecordingDeps_1482_);
v___x_1485_ = lean_st_ref_get(v___y_1474_);
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
lean_ctor_set(v_msg_1492_, 0, v_data_1468_);
lean_ctor_set(v_msg_1492_, 1, v_msg_1470_);
lean_ctor_set(v_msg_1492_, 2, v___x_1491_);
v___x_1493_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1492_, v___y_1471_, v___y_1472_, v___x_1484_, v___y_1474_);
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
v___x_1498_ = lean_st_ref_take(v___y_1474_);
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
lean_ctor_set(v___x_1517_, 0, v_ref_1469_);
lean_ctor_set(v___x_1517_, 1, v_a_1494_);
v___x_1518_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1467_, v___x_1517_);
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
v___x_1523_ = lean_st_ref_put(v___y_1474_, v___x_1522_);
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
lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; lean_object* v_a_1690_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; uint8_t v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v_a_1713_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; uint16_t v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; lean_object* v___y_1741_; lean_object* v_toCold_1742_; lean_object* v_currRecDepth_1743_; lean_object* v_ref_1744_; uint8_t v_suppressElabErrors_1745_; uint8_t v_checkDeprecated_1746_; uint8_t v_isRecordingDeps_1747_; lean_object* v___y_1748_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint16_t v___y_1826_; lean_object* v___y_1827_; uint8_t v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; uint8_t v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; uint16_t v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; uint8_t v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1878_; uint8_t v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; uint8_t v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; uint16_t v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; uint8_t v___y_1893_; lean_object* v___y_1894_; uint8_t v___y_1895_; lean_object* v___y_1897_; lean_object* v___y_1898_; uint8_t v___y_1899_; uint16_t v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; uint8_t v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1915_; uint8_t v___y_1916_; lean_object* v_lhs_1938_; lean_object* v_rhs_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; 
if (lean_obj_tag(v_x_1669_) == 1)
{
if (lean_obj_tag(v_x_1670_) == 1)
{
lean_object* v_a_1971_; lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1971_ = lean_ctor_get(v_x_1669_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v_x_1669_, 1);
v_a_1972_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v_x_1670_, 1);
v___x_1973_ = lean_is_level_def_eq(v_a_1971_, v_a_1972_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
return v___x_1973_;
}
else
{
v_lhs_1938_ = v_x_1669_;
v_rhs_1939_ = v_x_1670_;
v___y_1940_ = v_a_1671_;
v___y_1941_ = v_a_1672_;
v___y_1942_ = v_a_1673_;
v___y_1943_ = v_a_1674_;
goto v___jp_1937_;
}
}
else
{
v_lhs_1938_ = v_x_1669_;
v_rhs_1939_ = v_x_1670_;
v___y_1940_ = v_a_1671_;
v___y_1941_ = v_a_1672_;
v___y_1942_ = v_a_1673_;
v___y_1943_ = v_a_1674_;
goto v___jp_1937_;
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
lean_inc_ref(v___y_1684_);
lean_inc(v___y_1680_);
v___x_1698_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1680_, v___y_1683_, v___y_1684_, v___y_1688_, v___y_1689_, v___y_1682_, v___y_1687_, v___y_1681_, v___x_1697_, v___y_1685_, v___y_1686_, v___y_1678_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1688_);
return v___x_1698_;
}
v___jp_1699_:
{
lean_object* v___x_1714_; double v___x_1715_; double v___x_1716_; double v___x_1717_; double v___x_1718_; double v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1714_ = lean_io_mono_nanos_now();
v___x_1715_ = lean_float_of_nat(v___y_1702_);
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
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1703_);
v___x_1724_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1703_, v___y_1706_, v___y_1707_, v___y_1711_, v___y_1712_, v___y_1705_, v___y_1710_, v___y_1704_, v___x_1723_, v___y_1708_, v___y_1709_, v___y_1701_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v___y_1711_);
return v___x_1724_;
}
v___jp_1725_:
{
lean_object* v_fileName_1749_; lean_object* v_fileMap_1750_; lean_object* v_currNamespace_1751_; lean_object* v_openDecls_1752_; lean_object* v_initHeartbeats_1753_; lean_object* v_maxHeartbeats_1754_; lean_object* v_quotContext_1755_; lean_object* v_currMacroScope_1756_; lean_object* v_cancelTk_x3f_1757_; lean_object* v_inheritedTraceOptions_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1810_; 
v_fileName_1749_ = lean_ctor_get(v_toCold_1742_, 0);
v_fileMap_1750_ = lean_ctor_get(v_toCold_1742_, 1);
v_currNamespace_1751_ = lean_ctor_get(v_toCold_1742_, 4);
v_openDecls_1752_ = lean_ctor_get(v_toCold_1742_, 5);
v_initHeartbeats_1753_ = lean_ctor_get(v_toCold_1742_, 6);
v_maxHeartbeats_1754_ = lean_ctor_get(v_toCold_1742_, 7);
v_quotContext_1755_ = lean_ctor_get(v_toCold_1742_, 8);
v_currMacroScope_1756_ = lean_ctor_get(v_toCold_1742_, 9);
v_cancelTk_x3f_1757_ = lean_ctor_get(v_toCold_1742_, 10);
v_inheritedTraceOptions_1758_ = lean_ctor_get(v_toCold_1742_, 11);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_toCold_1742_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; lean_object* v_unused_1812_; 
v_unused_1811_ = lean_ctor_get(v_toCold_1742_, 3);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_toCold_1742_, 2);
lean_dec(v_unused_1812_);
v___x_1760_ = v_toCold_1742_;
v_isShared_1761_ = v_isSharedCheck_1810_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_inheritedTraceOptions_1758_);
lean_inc(v_cancelTk_x3f_1757_);
lean_inc(v_currMacroScope_1756_);
lean_inc(v_quotContext_1755_);
lean_inc(v_maxHeartbeats_1754_);
lean_inc(v_initHeartbeats_1753_);
lean_inc(v_openDecls_1752_);
lean_inc(v_currNamespace_1751_);
lean_inc(v_fileMap_1750_);
lean_inc(v_fileName_1749_);
lean_dec(v_toCold_1742_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1810_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = l_Lean_maxRecDepth;
v___x_1763_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1737_, v___x_1762_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 3, v___x_1763_);
lean_ctor_set(v___x_1760_, 2, v___y_1737_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_fileName_1749_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_fileMap_1750_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v___y_1737_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v_currNamespace_1751_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v_openDecls_1752_);
lean_ctor_set(v_reuseFailAlloc_1809_, 6, v_initHeartbeats_1753_);
lean_ctor_set(v_reuseFailAlloc_1809_, 7, v_maxHeartbeats_1754_);
lean_ctor_set(v_reuseFailAlloc_1809_, 8, v_quotContext_1755_);
lean_ctor_set(v_reuseFailAlloc_1809_, 9, v_currMacroScope_1756_);
lean_ctor_set(v_reuseFailAlloc_1809_, 10, v_cancelTk_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1809_, 11, v_inheritedTraceOptions_1758_);
v___x_1765_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1766_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v_currRecDepth_1743_);
lean_ctor_set(v___x_1766_, 2, v_ref_1744_);
lean_ctor_set_uint16(v___x_1766_, sizeof(void*)*3, v___y_1738_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*3 + 2, v_suppressElabErrors_1745_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*3 + 3, v_checkDeprecated_1746_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*3 + 4, v_isRecordingDeps_1747_);
v___x_1767_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1729_, v___y_1734_, v___y_1735_, v___x_1766_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref_known(v___x_1766_, 3);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1768_, v___y_1734_, v___y_1735_, v___y_1731_, v___y_1726_);
lean_dec_ref(v___y_1731_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1772_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1741_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_io_mono_nanos_now();
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1735_);
lean_inc_ref(v___y_1734_);
v___x_1774_ = lean_apply_5(v___y_1739_, v___y_1734_, v___y_1735_, v___y_1727_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set_tag(v___x_1777_, 1);
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
v___y_1700_ = v___y_1726_;
v___y_1701_ = v___y_1727_;
v___y_1702_ = v___x_1773_;
v___y_1703_ = v___y_1728_;
v___y_1704_ = v_a_1770_;
v___y_1705_ = v___y_1730_;
v___y_1706_ = v___y_1732_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1736_;
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1740_;
v_a_1713_ = v___x_1780_;
goto v___jp_1699_;
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1774_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1774_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 0);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
v___y_1700_ = v___y_1726_;
v___y_1701_ = v___y_1727_;
v___y_1702_ = v___x_1773_;
v___y_1703_ = v___y_1728_;
v___y_1704_ = v_a_1770_;
v___y_1705_ = v___y_1730_;
v___y_1706_ = v___y_1732_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1736_;
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1740_;
v_a_1713_ = v___x_1788_;
goto v___jp_1699_;
}
}
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1735_);
lean_inc_ref(v___y_1734_);
v___x_1792_ = lean_apply_5(v___y_1739_, v___y_1734_, v___y_1735_, v___y_1727_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 1);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
v___y_1677_ = v___y_1726_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___x_1791_;
v___y_1680_ = v___y_1728_;
v___y_1681_ = v_a_1770_;
v___y_1682_ = v___y_1730_;
v___y_1683_ = v___y_1732_;
v___y_1684_ = v___y_1733_;
v___y_1685_ = v___y_1734_;
v___y_1686_ = v___y_1735_;
v___y_1687_ = v___y_1736_;
v___y_1688_ = v___y_1741_;
v___y_1689_ = v___y_1740_;
v_a_1690_ = v___x_1798_;
goto v___jp_1676_;
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1792_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1792_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 0);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
v___y_1677_ = v___y_1726_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___x_1791_;
v___y_1680_ = v___y_1728_;
v___y_1681_ = v_a_1770_;
v___y_1682_ = v___y_1730_;
v___y_1683_ = v___y_1732_;
v___y_1684_ = v___y_1733_;
v___y_1685_ = v___y_1734_;
v___y_1686_ = v___y_1735_;
v___y_1687_ = v___y_1736_;
v___y_1688_ = v___y_1741_;
v___y_1689_ = v___y_1740_;
v_a_1690_ = v___x_1806_;
goto v___jp_1676_;
}
}
}
}
}
}
}
v___jp_1813_:
{
lean_object* v_toCold_1832_; lean_object* v_currRecDepth_1833_; lean_object* v_ref_1834_; uint8_t v_suppressElabErrors_1835_; uint8_t v_checkDeprecated_1836_; uint8_t v_isRecordingDeps_1837_; 
v_toCold_1832_ = lean_ctor_get(v___y_1830_, 0);
lean_inc_ref(v_toCold_1832_);
v_currRecDepth_1833_ = lean_ctor_get(v___y_1830_, 1);
lean_inc(v_currRecDepth_1833_);
v_ref_1834_ = lean_ctor_get(v___y_1830_, 2);
lean_inc(v_ref_1834_);
v_suppressElabErrors_1835_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 2);
v_checkDeprecated_1836_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1837_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_1830_);
v___y_1726_ = v___y_1814_;
v___y_1727_ = v___y_1815_;
v___y_1728_ = v___y_1816_;
v___y_1729_ = v___y_1817_;
v___y_1730_ = v___y_1818_;
v___y_1731_ = v___y_1819_;
v___y_1732_ = v___y_1820_;
v___y_1733_ = v___y_1821_;
v___y_1734_ = v___y_1822_;
v___y_1735_ = v___y_1823_;
v___y_1736_ = v___y_1824_;
v___y_1737_ = v___y_1825_;
v___y_1738_ = v___y_1826_;
v___y_1739_ = v___y_1827_;
v___y_1740_ = v___y_1828_;
v___y_1741_ = v___y_1829_;
v_toCold_1742_ = v_toCold_1832_;
v_currRecDepth_1743_ = v_currRecDepth_1833_;
v_ref_1744_ = v_ref_1834_;
v_suppressElabErrors_1745_ = v_suppressElabErrors_1835_;
v_checkDeprecated_1746_ = v_checkDeprecated_1836_;
v_isRecordingDeps_1747_ = v_isRecordingDeps_1837_;
v___y_1748_ = v___y_1831_;
goto v___jp_1725_;
}
v___jp_1838_:
{
lean_object* v___x_1856_; lean_object* v_env_1857_; lean_object* v_nextMacroScope_1858_; lean_object* v_ngen_1859_; lean_object* v_auxDeclNGen_1860_; lean_object* v_traceState_1861_; lean_object* v_recordedDeps_1862_; lean_object* v_messages_1863_; lean_object* v_infoState_1864_; lean_object* v_snapshotTasks_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1875_; 
v___x_1856_ = lean_st_ref_take(v___y_1839_);
v_env_1857_ = lean_ctor_get(v___x_1856_, 0);
v_nextMacroScope_1858_ = lean_ctor_get(v___x_1856_, 1);
v_ngen_1859_ = lean_ctor_get(v___x_1856_, 2);
v_auxDeclNGen_1860_ = lean_ctor_get(v___x_1856_, 3);
v_traceState_1861_ = lean_ctor_get(v___x_1856_, 4);
v_recordedDeps_1862_ = lean_ctor_get(v___x_1856_, 6);
v_messages_1863_ = lean_ctor_get(v___x_1856_, 7);
v_infoState_1864_ = lean_ctor_get(v___x_1856_, 8);
v_snapshotTasks_1865_ = lean_ctor_get(v___x_1856_, 9);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v___x_1856_, 5);
lean_dec(v_unused_1876_);
v___x_1867_ = v___x_1856_;
v_isShared_1868_ = v_isSharedCheck_1875_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snapshotTasks_1865_);
lean_inc(v_infoState_1864_);
lean_inc(v_messages_1863_);
lean_inc(v_recordedDeps_1862_);
lean_inc(v_traceState_1861_);
lean_inc(v_auxDeclNGen_1860_);
lean_inc(v_ngen_1859_);
lean_inc(v_nextMacroScope_1858_);
lean_inc(v_env_1857_);
lean_dec(v___x_1856_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1875_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1869_ = l_Lean_Kernel_enableDiag(v_env_1857_, v___y_1855_);
v___x_1870_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 5, v___x_1870_);
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1872_ = v___x_1867_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_nextMacroScope_1858_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_ngen_1859_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_auxDeclNGen_1860_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_traceState_1861_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_recordedDeps_1862_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v_messages_1863_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_infoState_1864_);
lean_ctor_set(v_reuseFailAlloc_1874_, 9, v_snapshotTasks_1865_);
v___x_1872_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_st_ref_put(v___y_1839_, v___x_1872_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1839_);
v___y_1814_ = v___y_1839_;
v___y_1815_ = v___y_1840_;
v___y_1816_ = v___y_1841_;
v___y_1817_ = v___y_1842_;
v___y_1818_ = v___y_1843_;
v___y_1819_ = v___y_1844_;
v___y_1820_ = v___y_1845_;
v___y_1821_ = v___y_1846_;
v___y_1822_ = v___y_1847_;
v___y_1823_ = v___y_1848_;
v___y_1824_ = v___y_1851_;
v___y_1825_ = v___y_1850_;
v___y_1826_ = v___y_1849_;
v___y_1827_ = v___y_1854_;
v___y_1828_ = v___y_1853_;
v___y_1829_ = v___y_1852_;
v___y_1830_ = v___y_1844_;
v___y_1831_ = v___y_1839_;
goto v___jp_1813_;
}
}
}
v___jp_1877_:
{
if (v___y_1879_ == 0)
{
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1878_);
v___y_1814_ = v___y_1878_;
v___y_1815_ = v___y_1880_;
v___y_1816_ = v___y_1881_;
v___y_1817_ = v___y_1882_;
v___y_1818_ = v___y_1883_;
v___y_1819_ = v___y_1884_;
v___y_1820_ = v___y_1885_;
v___y_1821_ = v___y_1886_;
v___y_1822_ = v___y_1887_;
v___y_1823_ = v___y_1888_;
v___y_1824_ = v___y_1889_;
v___y_1825_ = v___y_1891_;
v___y_1826_ = v___y_1890_;
v___y_1827_ = v___y_1892_;
v___y_1828_ = v___y_1893_;
v___y_1829_ = v___y_1894_;
v___y_1830_ = v___y_1884_;
v___y_1831_ = v___y_1878_;
goto v___jp_1813_;
}
else
{
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
v___y_1849_ = v___y_1890_;
v___y_1850_ = v___y_1891_;
v___y_1851_ = v___y_1889_;
v___y_1852_ = v___y_1894_;
v___y_1853_ = v___y_1893_;
v___y_1854_ = v___y_1892_;
v___y_1855_ = v___y_1895_;
goto v___jp_1838_;
}
}
v___jp_1896_:
{
lean_object* v___x_1917_; lean_object* v_a_1918_; lean_object* v_ref_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint16_t v___x_1929_; lean_object* v___x_1930_; lean_object* v_env_1931_; uint8_t v___x_1932_; uint16_t v___x_1933_; uint16_t v___x_1934_; uint16_t v___x_1935_; uint8_t v___x_1936_; 
v___x_1917_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1897_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
v_ref_1919_ = l_Lean_replaceRef(v___y_1910_, v___y_1910_);
lean_inc(v_ref_1919_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1914_);
v___x_1920_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1920_, 0, v___y_1914_);
lean_ctor_set(v___x_1920_, 1, v___y_1901_);
lean_ctor_set(v___x_1920_, 2, v_ref_1919_);
lean_ctor_set_uint16(v___x_1920_, sizeof(void*)*3, v___y_1900_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*3 + 2, v___y_1899_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*3 + 3, v___y_1902_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*3 + 4, v___y_1916_);
v___x_1921_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1922_ = 0;
v___x_1923_ = l_Lean_MessageData_ofLevel(v___y_1903_);
v___x_1924_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_MessageData_ofLevel(v___y_1905_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
lean_inc_ref(v___y_1913_);
v___x_1928_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1913_, v___x_1921_, v___x_1922_);
v___x_1929_ = l_Lean_OptionFlags_ofOptions(v___x_1928_);
v___x_1930_ = lean_st_ref_get(v___y_1897_);
v_env_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_env_1931_);
lean_dec(v___x_1930_);
v___x_1932_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1931_);
lean_dec_ref(v_env_1931_);
v___x_1933_ = 512;
v___x_1934_ = lean_uint16_land(v___x_1929_, v___x_1933_);
v___x_1935_ = 0;
v___x_1936_ = lean_uint16_dec_eq(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
if (v___y_1915_ == 0)
{
lean_dec(v_ref_1919_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1901_);
v___y_1878_ = v___y_1897_;
v___y_1879_ = v___x_1932_;
v___y_1880_ = v___y_1898_;
v___y_1881_ = v___y_1904_;
v___y_1882_ = v___x_1927_;
v___y_1883_ = v_a_1918_;
v___y_1884_ = v___x_1920_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___x_1929_;
v___y_1891_ = v___x_1928_;
v___y_1892_ = v___y_1912_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1915_;
goto v___jp_1877_;
}
else
{
if (v___x_1932_ == 0)
{
lean_dec(v_ref_1919_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1901_);
v___y_1839_ = v___y_1897_;
v___y_1840_ = v___y_1898_;
v___y_1841_ = v___y_1904_;
v___y_1842_ = v___x_1927_;
v___y_1843_ = v_a_1918_;
v___y_1844_ = v___x_1920_;
v___y_1845_ = v___y_1906_;
v___y_1846_ = v___y_1907_;
v___y_1847_ = v___y_1908_;
v___y_1848_ = v___y_1909_;
v___y_1849_ = v___x_1929_;
v___y_1850_ = v___x_1928_;
v___y_1851_ = v___y_1910_;
v___y_1852_ = v___y_1913_;
v___y_1853_ = v___y_1911_;
v___y_1854_ = v___y_1912_;
v___y_1855_ = v___y_1915_;
goto v___jp_1838_;
}
else
{
lean_inc(v___y_1897_);
v___y_1726_ = v___y_1897_;
v___y_1727_ = v___y_1898_;
v___y_1728_ = v___y_1904_;
v___y_1729_ = v___x_1927_;
v___y_1730_ = v_a_1918_;
v___y_1731_ = v___x_1920_;
v___y_1732_ = v___y_1906_;
v___y_1733_ = v___y_1907_;
v___y_1734_ = v___y_1908_;
v___y_1735_ = v___y_1909_;
v___y_1736_ = v___y_1910_;
v___y_1737_ = v___x_1928_;
v___y_1738_ = v___x_1929_;
v___y_1739_ = v___y_1912_;
v___y_1740_ = v___y_1911_;
v___y_1741_ = v___y_1913_;
v_toCold_1742_ = v___y_1914_;
v_currRecDepth_1743_ = v___y_1901_;
v_ref_1744_ = v_ref_1919_;
v_suppressElabErrors_1745_ = v___y_1899_;
v_checkDeprecated_1746_ = v___y_1902_;
v_isRecordingDeps_1747_ = v___y_1916_;
v___y_1748_ = v___y_1897_;
goto v___jp_1725_;
}
}
}
else
{
lean_dec(v_ref_1919_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1901_);
v___y_1878_ = v___y_1897_;
v___y_1879_ = v___x_1932_;
v___y_1880_ = v___y_1898_;
v___y_1881_ = v___y_1904_;
v___y_1882_ = v___x_1927_;
v___y_1883_ = v_a_1918_;
v___y_1884_ = v___x_1920_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___x_1929_;
v___y_1891_ = v___x_1928_;
v___y_1892_ = v___y_1912_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___x_1922_;
goto v___jp_1877_;
}
}
v___jp_1937_:
{
lean_object* v_toCold_1944_; lean_object* v_options_1945_; lean_object* v_currRecDepth_1946_; lean_object* v_ref_1947_; uint16_t v_optionFlags_1948_; uint8_t v_suppressElabErrors_1949_; uint8_t v_checkDeprecated_1950_; uint8_t v_isRecordingDeps_1951_; lean_object* v_inheritedTraceOptions_1952_; uint8_t v_hasTrace_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___y_1962_; 
v_toCold_1944_ = lean_ctor_get(v___y_1942_, 0);
v_options_1945_ = lean_ctor_get(v_toCold_1944_, 2);
v_currRecDepth_1946_ = lean_ctor_get(v___y_1942_, 1);
v_ref_1947_ = lean_ctor_get(v___y_1942_, 2);
v_optionFlags_1948_ = lean_ctor_get_uint16(v___y_1942_, sizeof(void*)*3);
v_suppressElabErrors_1949_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*3 + 2);
v_checkDeprecated_1950_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1951_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*3 + 4);
v_inheritedTraceOptions_1952_ = lean_ctor_get(v_toCold_1944_, 11);
v_hasTrace_1953_ = lean_ctor_get_uint8(v_options_1945_, sizeof(void*)*1);
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1956_ = l_Lean_Level_getLevelOffset(v_lhs_1938_);
v___x_1957_ = l_Lean_Level_getLevelOffset(v_rhs_1939_);
v___x_1958_ = lean_level_eq(v___x_1956_, v___x_1957_);
lean_dec(v___x_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = 1;
v___x_1960_ = lean_box(v___x_1958_);
v___x_1961_ = lean_box(v___x_1959_);
lean_inc(v_rhs_1939_);
lean_inc(v_lhs_1938_);
v___y_1962_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1962_, 0, v___x_1960_);
lean_closure_set(v___y_1962_, 1, v_lhs_1938_);
lean_closure_set(v___y_1962_, 2, v_rhs_1939_);
lean_closure_set(v___y_1962_, 3, v___x_1961_);
lean_closure_set(v___y_1962_, 4, v___x_1954_);
lean_closure_set(v___y_1962_, 5, v___x_1955_);
if (v_hasTrace_1953_ == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref(v___y_1962_);
v___x_1963_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1958_, v_lhs_1938_, v_rhs_1939_, v___x_1959_, v___x_1954_, v___x_1955_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1964_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1965_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1966_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1952_, v_options_1945_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = l_Lean_trace_profiler;
v___x_1969_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_options_1945_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref(v___y_1962_);
v___x_1970_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1958_, v_lhs_1938_, v_rhs_1939_, v___x_1959_, v___x_1954_, v___x_1955_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v___x_1970_;
}
else
{
lean_inc(v_ref_1947_);
lean_inc(v_currRecDepth_1946_);
lean_inc_ref(v_options_1945_);
lean_inc_ref(v_toCold_1944_);
v___y_1897_ = v___y_1943_;
v___y_1898_ = v___y_1942_;
v___y_1899_ = v_suppressElabErrors_1949_;
v___y_1900_ = v_optionFlags_1948_;
v___y_1901_ = v_currRecDepth_1946_;
v___y_1902_ = v_checkDeprecated_1950_;
v___y_1903_ = v_lhs_1938_;
v___y_1904_ = v___x_1964_;
v___y_1905_ = v_rhs_1939_;
v___y_1906_ = v___x_1959_;
v___y_1907_ = v___x_1965_;
v___y_1908_ = v___y_1940_;
v___y_1909_ = v___y_1941_;
v___y_1910_ = v_ref_1947_;
v___y_1911_ = v___x_1967_;
v___y_1912_ = v___y_1962_;
v___y_1913_ = v_options_1945_;
v___y_1914_ = v_toCold_1944_;
v___y_1915_ = v_hasTrace_1953_;
v___y_1916_ = v_isRecordingDeps_1951_;
goto v___jp_1896_;
}
}
else
{
lean_inc(v_ref_1947_);
lean_inc(v_currRecDepth_1946_);
lean_inc_ref(v_options_1945_);
lean_inc_ref(v_toCold_1944_);
v___y_1897_ = v___y_1943_;
v___y_1898_ = v___y_1942_;
v___y_1899_ = v_suppressElabErrors_1949_;
v___y_1900_ = v_optionFlags_1948_;
v___y_1901_ = v_currRecDepth_1946_;
v___y_1902_ = v_checkDeprecated_1950_;
v___y_1903_ = v_lhs_1938_;
v___y_1904_ = v___x_1964_;
v___y_1905_ = v_rhs_1939_;
v___y_1906_ = v___x_1959_;
v___y_1907_ = v___x_1965_;
v___y_1908_ = v___y_1940_;
v___y_1909_ = v___y_1941_;
v___y_1910_ = v_ref_1947_;
v___y_1911_ = v___x_1967_;
v___y_1912_ = v___y_1962_;
v___y_1913_ = v_options_1945_;
v___y_1914_ = v_toCold_1944_;
v___y_1915_ = v_hasTrace_1953_;
v___y_1916_ = v_isRecordingDeps_1951_;
goto v___jp_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = lean_is_level_def_eq(v_x_1974_, v_x_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1983_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1990_, v_x_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2055_ = 0;
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2057_ = l_Lean_registerTraceClass(v___x_2054_, v___x_2055_, v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
lean_dec_ref_known(v___x_2057_, 1);
v___x_2058_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2059_ = 1;
v___x_2060_ = l_Lean_registerTraceClass(v___x_2058_, v___x_2059_, v___x_2056_);
return v___x_2060_;
}
else
{
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2062_;
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
