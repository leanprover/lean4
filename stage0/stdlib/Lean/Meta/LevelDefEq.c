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
size_t v_x_2713__boxed_196_; size_t v_x_2714__boxed_197_; lean_object* v_res_198_; 
v_x_2713__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_x_2714__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_191_, v_x_2713__boxed_196_, v_x_2714__boxed_197_, v_x_194_, v_x_195_);
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
lean_object* v___x_210_; lean_object* v_mctx_211_; lean_object* v_cache_212_; lean_object* v_zetaDeltaFVarIds_213_; lean_object* v_postponed_214_; lean_object* v_diag_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_244_; 
v___x_210_ = lean_st_ref_take(v___y_208_);
v_mctx_211_ = lean_ctor_get(v___x_210_, 0);
v_cache_212_ = lean_ctor_get(v___x_210_, 1);
v_zetaDeltaFVarIds_213_ = lean_ctor_get(v___x_210_, 2);
v_postponed_214_ = lean_ctor_get(v___x_210_, 3);
v_diag_215_ = lean_ctor_get(v___x_210_, 4);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_244_ == 0)
{
v___x_217_ = v___x_210_;
v_isShared_218_ = v_isSharedCheck_244_;
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
v_isShared_218_ = v_isSharedCheck_244_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_depth_219_; lean_object* v_levelAssignDepth_220_; lean_object* v_lmvarCounter_221_; lean_object* v_mvarCounter_222_; lean_object* v_lDecls_223_; lean_object* v_decls_224_; lean_object* v_userNames_225_; lean_object* v_lAssignment_226_; lean_object* v_eAssignment_227_; lean_object* v_dAssignment_228_; lean_object* v_instanceTypedMVars_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
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
v_isSharedCheck_243_ = !lean_is_exclusive(v_mctx_211_);
if (v_isSharedCheck_243_ == 0)
{
v___x_231_ = v_mctx_211_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
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
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_box(0);
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_226_, v_mvarId_206_, v_val_207_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 7, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_depth_219_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_levelAssignDepth_220_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_lmvarCounter_221_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_mvarCounter_222_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_lDecls_223_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_decls_224_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_userNames_225_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_eAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 9, v_dAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_242_, 10, v_instanceTypedMVars_229_);
v___x_236_ = v_reuseFailAlloc_242_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_236_);
v___x_238_ = v___x_217_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_zetaDeltaFVarIds_213_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_postponed_214_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_diag_215_);
v___x_238_ = v_reuseFailAlloc_241_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_st_ref_put(v___y_208_, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_233_);
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* v_mvarId_245_, lean_object* v_val_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_245_, v_val_246_, v___y_247_);
lean_dec(v___y_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object* v_msgData_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; lean_object* v_env_257_; uint8_t v___x_258_; lean_object* v_env_259_; lean_object* v___x_260_; lean_object* v_toCold_261_; lean_object* v_mctx_262_; lean_object* v_lctx_263_; lean_object* v_options_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_256_ = lean_st_ref_get(v___y_254_);
v_env_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_env_257_);
lean_dec(v___x_256_);
v___x_258_ = 0;
v_env_259_ = l_Lean_Environment_setRecordingDeps(v_env_257_, v___x_258_);
v___x_260_ = lean_st_ref_get(v___y_252_);
v_toCold_261_ = lean_ctor_get(v___y_253_, 0);
v_mctx_262_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_mctx_262_);
lean_dec(v___x_260_);
v_lctx_263_ = lean_ctor_get(v___y_251_, 2);
v_options_264_ = lean_ctor_get(v_toCold_261_, 2);
lean_inc_ref(v_options_264_);
lean_inc_ref(v_lctx_263_);
v___x_265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_265_, 0, v_env_259_);
lean_ctor_set(v___x_265_, 1, v_mctx_262_);
lean_ctor_set(v___x_265_, 2, v_lctx_263_);
lean_ctor_set(v___x_265_, 3, v_options_264_);
v___x_266_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_msgData_250_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_274_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_275_; double v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_float_of_nat(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_280_, lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_ref_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_334_; 
v_ref_287_ = lean_ctor_get(v___y_284_, 2);
v___x_288_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_334_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_334_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_334_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v_traceState_294_; lean_object* v_env_295_; lean_object* v_nextMacroScope_296_; lean_object* v_ngen_297_; lean_object* v_auxDeclNGen_298_; lean_object* v_cache_299_; lean_object* v_recordedDeps_300_; lean_object* v_messages_301_; lean_object* v_infoState_302_; lean_object* v_snapshotTasks_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_333_; 
v___x_293_ = lean_st_ref_take(v___y_285_);
v_traceState_294_ = lean_ctor_get(v___x_293_, 4);
v_env_295_ = lean_ctor_get(v___x_293_, 0);
v_nextMacroScope_296_ = lean_ctor_get(v___x_293_, 1);
v_ngen_297_ = lean_ctor_get(v___x_293_, 2);
v_auxDeclNGen_298_ = lean_ctor_get(v___x_293_, 3);
v_cache_299_ = lean_ctor_get(v___x_293_, 5);
v_recordedDeps_300_ = lean_ctor_get(v___x_293_, 6);
v_messages_301_ = lean_ctor_get(v___x_293_, 7);
v_infoState_302_ = lean_ctor_get(v___x_293_, 8);
v_snapshotTasks_303_ = lean_ctor_get(v___x_293_, 9);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_333_ == 0)
{
v___x_305_ = v___x_293_;
v_isShared_306_ = v_isSharedCheck_333_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_snapshotTasks_303_);
lean_inc(v_infoState_302_);
lean_inc(v_messages_301_);
lean_inc(v_recordedDeps_300_);
lean_inc(v_cache_299_);
lean_inc(v_traceState_294_);
lean_inc(v_auxDeclNGen_298_);
lean_inc(v_ngen_297_);
lean_inc(v_nextMacroScope_296_);
lean_inc(v_env_295_);
lean_dec(v___x_293_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_333_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
uint64_t v_tid_307_; lean_object* v_traces_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_332_; 
v_tid_307_ = lean_ctor_get_uint64(v_traceState_294_, sizeof(void*)*1);
v_traces_308_ = lean_ctor_get(v_traceState_294_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_traceState_294_);
if (v_isSharedCheck_332_ == 0)
{
v___x_310_ = v_traceState_294_;
v_isShared_311_ = v_isSharedCheck_332_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_traces_308_);
lean_dec(v_traceState_294_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_332_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; double v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_box(0);
v___x_314_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_315_ = 0;
v___x_316_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_317_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_317_, 0, v_cls_280_);
lean_ctor_set(v___x_317_, 1, v___x_313_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
lean_ctor_set_float(v___x_317_, sizeof(void*)*3, v___x_314_);
lean_ctor_set_float(v___x_317_, sizeof(void*)*3 + 8, v___x_314_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*3 + 16, v___x_315_);
v___x_318_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_319_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v_a_289_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_inc(v_ref_287_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_ref_287_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Lean_PersistentArray_push___redArg(v_traces_308_, v___x_320_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_321_);
v___x_323_ = v___x_310_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_321_);
lean_ctor_set_uint64(v_reuseFailAlloc_331_, sizeof(void*)*1, v_tid_307_);
v___x_323_ = v_reuseFailAlloc_331_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 4, v___x_323_);
v___x_325_ = v___x_305_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_env_295_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_nextMacroScope_296_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_ngen_297_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_auxDeclNGen_298_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v_cache_299_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_recordedDeps_300_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_messages_301_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_infoState_302_);
lean_ctor_set(v_reuseFailAlloc_330_, 9, v_snapshotTasks_303_);
v___x_325_ = v_reuseFailAlloc_330_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_st_ref_put(v___y_285_, v___x_325_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_312_);
v___x_328_ = v___x_291_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_312_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_335_, v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_347_ = lean_unsigned_to_nat(2u);
v___x_348_ = lean_unsigned_to_nat(39u);
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_351_ = l_mkPanicMessageWithDecl(v___x_350_, v___x_349_, v___x_348_, v___x_347_, v___x_346_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_364_ = l_Lean_Name_append(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_371_, lean_object* v_v_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Level_isMax(v_v_372_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_v_372_);
lean_dec(v_mvarId_371_);
v___x_379_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_380_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_379_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_mkFreshLevelMVar(v_a_373_, v_a_374_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_toCold_382_; lean_object* v_options_383_; lean_object* v_a_384_; lean_object* v_inheritedTraceOptions_385_; uint8_t v_hasTrace_386_; lean_object* v___x_387_; 
v_toCold_382_ = lean_ctor_get(v_a_375_, 0);
v_options_383_ = lean_ctor_get(v_toCold_382_, 2);
v_a_384_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_381_, 1);
v_inheritedTraceOptions_385_ = lean_ctor_get(v_toCold_382_, 11);
v_hasTrace_386_ = lean_ctor_get_uint8(v_options_383_, sizeof(void*)*1);
v___x_387_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_371_, v_v_372_, v_a_384_);
if (v_hasTrace_386_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_371_, v___x_387_, v_a_374_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_391_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_385_, v_options_383_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_371_, v___x_387_, v_a_374_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_393_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_371_);
v___x_394_ = l_Lean_mkLevelMVar(v_mvarId_371_);
v___x_395_ = l_Lean_MessageData_ofLevel(v___x_394_);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_393_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
lean_inc(v___x_387_);
v___x_399_ = l_Lean_MessageData_ofLevel(v___x_387_);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_389_, v___x_400_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_402_; 
lean_dec_ref_known(v___x_401_, 1);
v___x_402_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_371_, v___x_387_, v_a_374_);
return v___x_402_;
}
else
{
lean_dec(v___x_387_);
lean_dec(v_mvarId_371_);
return v___x_401_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_v_372_);
lean_dec(v_mvarId_371_);
v_a_403_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_381_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_381_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_411_, lean_object* v_v_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_411_, v_v_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_419_, lean_object* v_val_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_419_, v_val_420_, v___y_422_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_427_, lean_object* v_val_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_427_, v_val_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_436_, v_x_437_, v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_440_, lean_object* v_x_441_, size_t v_x_442_, size_t v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_441_, v_x_442_, v_x_443_, v_x_444_, v_x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
size_t v_x_3223__boxed_453_; size_t v_x_3224__boxed_454_; lean_object* v_res_455_; 
v_x_3223__boxed_453_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_x_3224__boxed_454_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_res_455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_447_, v_x_448_, v_x_3223__boxed_453_, v_x_3224__boxed_454_, v_x_451_, v_x_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_456_, lean_object* v_n_457_, lean_object* v_k_458_, lean_object* v_v_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_457_, v_k_458_, v_v_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_461_, size_t v_depth_462_, lean_object* v_keys_463_, lean_object* v_vals_464_, lean_object* v_heq_465_, lean_object* v_i_466_, lean_object* v_entries_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_462_, v_keys_463_, v_vals_464_, v_i_466_, v_entries_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_469_, lean_object* v_depth_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_heq_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
size_t v_depth_boxed_476_; lean_object* v_res_477_; 
v_depth_boxed_476_ = lean_unbox_usize(v_depth_470_);
lean_dec(v_depth_470_);
v_res_477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_469_, v_depth_boxed_476_, v_keys_471_, v_vals_472_, v_heq_473_, v_i_474_, v_entries_475_);
lean_dec_ref(v_vals_472_);
lean_dec_ref(v_keys_471_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_479_, v_x_480_, v_x_481_, v_x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_487_, lean_object* v_v_x27_488_, lean_object* v_mvarId_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
uint8_t v___x_495_; lean_object* v___y_497_; 
v___x_495_ = lean_level_eq(v_u_487_, v_v_x27_488_);
if (v___x_495_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_mvarId_489_);
lean_dec(v_u_487_);
v___x_508_ = lean_box(v___x_495_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_toCold_510_; lean_object* v_options_511_; uint8_t v_hasTrace_512_; 
v_toCold_510_ = lean_ctor_get(v_a_492_, 0);
v_options_511_ = lean_ctor_get(v_toCold_510_, 2);
v_hasTrace_512_ = lean_ctor_get_uint8(v_options_511_, sizeof(void*)*1);
if (v_hasTrace_512_ == 0)
{
v___y_497_ = v_a_491_;
goto v___jp_496_;
}
else
{
lean_object* v_inheritedTraceOptions_513_; lean_object* v_cls_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_inheritedTraceOptions_513_ = lean_ctor_get(v_toCold_510_, 11);
v_cls_514_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_513_, v_options_511_, v___x_515_);
if (v___x_516_ == 0)
{
v___y_497_ = v_a_491_;
goto v___jp_496_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_489_);
v___x_518_ = l_Lean_mkLevelMVar(v_mvarId_489_);
v___x_519_ = l_Lean_MessageData_ofLevel(v___x_518_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_inc(v_u_487_);
v___x_523_ = l_Lean_MessageData_ofLevel(v_u_487_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_514_, v___x_524_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_dec_ref_known(v___x_525_, 1);
v___y_497_ = v_a_491_;
goto v___jp_496_;
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_mvarId_489_);
lean_dec(v_u_487_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
v___jp_496_:
{
lean_object* v___x_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v___x_498_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_489_, v_u_487_, v___y_497_);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_507_);
v___x_500_ = v___x_498_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_dec(v___x_498_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_box(v___x_495_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_534_, lean_object* v_v_x27_535_, lean_object* v_mvarId_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_534_, v_v_x27_535_, v_mvarId_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_v_x27_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_543_, lean_object* v_v_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
if (lean_obj_tag(v_v_544_) == 2)
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v_v_544_, 1);
lean_inc(v_a_554_);
if (lean_obj_tag(v_a_554_) == 5)
{
lean_object* v_a_555_; lean_object* v_a_556_; lean_object* v___x_557_; 
v_a_555_ = lean_ctor_get(v_v_544_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v_v_544_, 2);
v_a_556_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v_a_554_, 1);
v___x_557_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_543_, v_a_555_, v_a_556_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_555_);
return v___x_557_;
}
else
{
lean_object* v_a_558_; 
v_a_558_ = lean_ctor_get(v_v_544_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_v_544_, 2);
if (lean_obj_tag(v_a_558_) == 5)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v_a_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v_a_558_, 1);
v___x_560_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_543_, v_a_554_, v_a_559_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_554_);
return v___x_560_;
}
else
{
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_u_543_);
goto v___jp_550_;
}
}
}
else
{
lean_dec(v_v_544_);
lean_dec(v_u_543_);
goto v___jp_550_;
}
v___jp_550_:
{
uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = 0;
v___x_552_ = lean_box(v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_561_, lean_object* v_v_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_561_, v_v_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_568_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_572_, lean_object* v_u_u2082_573_, lean_object* v_v_x27_574_, lean_object* v_mvarId_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
uint8_t v___x_581_; uint8_t v___x_582_; lean_object* v___y_584_; lean_object* v___y_596_; 
v___x_581_ = lean_level_eq(v_u_u2081_572_, v_v_x27_574_);
v___x_582_ = 1;
if (v___x_581_ == 0)
{
uint8_t v___x_607_; 
v___x_607_ = lean_level_eq(v_u_u2082_573_, v_v_x27_574_);
lean_dec(v_u_u2082_573_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v_mvarId_575_);
lean_dec(v_u_u2081_572_);
v___x_608_ = lean_box(v___x_607_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
else
{
lean_object* v_toCold_610_; lean_object* v_options_611_; uint8_t v_hasTrace_612_; 
v_toCold_610_ = lean_ctor_get(v_a_578_, 0);
v_options_611_ = lean_ctor_get(v_toCold_610_, 2);
v_hasTrace_612_ = lean_ctor_get_uint8(v_options_611_, sizeof(void*)*1);
if (v_hasTrace_612_ == 0)
{
v___y_596_ = v_a_577_;
goto v___jp_595_;
}
else
{
lean_object* v_inheritedTraceOptions_613_; lean_object* v_cls_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_inheritedTraceOptions_613_ = lean_ctor_get(v_toCold_610_, 11);
v_cls_614_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_615_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_613_, v_options_611_, v___x_615_);
if (v___x_616_ == 0)
{
v___y_596_ = v_a_577_;
goto v___jp_595_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_617_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_575_);
v___x_618_ = l_Lean_mkLevelMVar(v_mvarId_575_);
v___x_619_ = l_Lean_MessageData_ofLevel(v___x_618_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_617_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_inc(v_u_u2081_572_);
v___x_623_ = l_Lean_MessageData_ofLevel(v_u_u2081_572_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_614_, v___x_624_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec_ref_known(v___x_625_, 1);
v___y_596_ = v_a_577_;
goto v___jp_595_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_mvarId_575_);
lean_dec(v_u_u2081_572_);
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
lean_object* v_toCold_634_; lean_object* v_options_635_; uint8_t v_hasTrace_636_; 
lean_dec(v_u_u2081_572_);
v_toCold_634_ = lean_ctor_get(v_a_578_, 0);
v_options_635_ = lean_ctor_get(v_toCold_634_, 2);
v_hasTrace_636_ = lean_ctor_get_uint8(v_options_635_, sizeof(void*)*1);
if (v_hasTrace_636_ == 0)
{
v___y_584_ = v_a_577_;
goto v___jp_583_;
}
else
{
lean_object* v_inheritedTraceOptions_637_; lean_object* v_cls_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_inheritedTraceOptions_637_ = lean_ctor_get(v_toCold_634_, 11);
v_cls_638_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_639_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_637_, v_options_635_, v___x_639_);
if (v___x_640_ == 0)
{
v___y_584_ = v_a_577_;
goto v___jp_583_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_641_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_575_);
v___x_642_ = l_Lean_mkLevelMVar(v_mvarId_575_);
v___x_643_ = l_Lean_MessageData_ofLevel(v___x_642_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_641_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_inc(v_u_u2082_573_);
v___x_647_ = l_Lean_MessageData_ofLevel(v_u_u2082_573_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_638_, v___x_648_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_dec_ref_known(v___x_649_, 1);
v___y_584_ = v_a_577_;
goto v___jp_583_;
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_mvarId_575_);
lean_dec(v_u_u2082_573_);
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
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v___x_585_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_575_, v_u_u2082_573_, v___y_584_);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_585_, 0);
lean_dec(v_unused_594_);
v___x_587_ = v___x_585_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_dec(v___x_585_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_box(v___x_582_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
v___jp_595_:
{
lean_object* v___x_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v___x_597_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_575_, v_u_u2081_572_, v___y_596_);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_606_);
v___x_599_ = v___x_597_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___x_597_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_box(v___x_582_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
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
lean_dec_ref_known(v_u_668_, 2);
v_a_682_ = lean_ctor_get(v_v_669_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v_v_669_, 2);
v_a_683_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v_a_679_, 1);
v___x_684_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_682_);
return v___x_684_;
}
else
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v_v_669_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v_v_669_, 2);
if (lean_obj_tag(v_a_685_) == 5)
{
lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v___x_689_; 
v_a_686_ = lean_ctor_get(v_u_668_, 0);
lean_inc(v_a_686_);
v_a_687_ = lean_ctor_get(v_u_668_, 1);
lean_inc(v_a_687_);
lean_dec_ref_known(v_u_668_, 2);
v_a_688_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v_a_685_, 1);
v___x_689_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_686_, v_a_687_, v_a_679_, v_a_688_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_679_);
return v___x_689_;
}
else
{
lean_dec(v_a_685_);
lean_dec(v_a_679_);
lean_dec_ref_known(v_u_668_, 2);
goto v___jp_675_;
}
}
}
else
{
lean_dec_ref_known(v_u_668_, 2);
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
lean_object* v_toCold_716_; lean_object* v_ref_717_; lean_object* v___y_719_; lean_object* v_options_739_; uint8_t v_hasTrace_740_; 
v_toCold_716_ = lean_ctor_get(v_a_713_, 0);
v_ref_717_ = lean_ctor_get(v_a_713_, 2);
v_options_739_ = lean_ctor_get(v_toCold_716_, 2);
v_hasTrace_740_ = lean_ctor_get_uint8(v_options_739_, sizeof(void*)*1);
if (v_hasTrace_740_ == 0)
{
v___y_719_ = v_a_712_;
goto v___jp_718_;
}
else
{
lean_object* v_inheritedTraceOptions_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_inheritedTraceOptions_741_ = lean_ctor_get(v_toCold_716_, 11);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_743_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_741_, v_options_739_, v___x_743_);
if (v___x_744_ == 0)
{
v___y_719_ = v_a_712_;
goto v___jp_718_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_inc(v_lhs_709_);
v___x_745_ = l_Lean_MessageData_ofLevel(v_lhs_709_);
v___x_746_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
lean_inc(v_rhs_710_);
v___x_748_ = l_Lean_MessageData_ofLevel(v_rhs_710_);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_742_, v___x_749_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_dec_ref_known(v___x_750_, 1);
v___y_719_ = v_a_712_;
goto v___jp_718_;
}
else
{
lean_dec(v_rhs_710_);
lean_dec(v_lhs_709_);
return v___x_750_;
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
lean_object* v_defEqCtx_x3f_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v_defEqCtx_x3f_729_ = lean_ctor_get(v_a_711_, 4);
v___x_730_ = lean_box(0);
lean_inc(v_defEqCtx_x3f_729_);
lean_inc(v_ref_717_);
v___x_731_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_731_, 0, v_ref_717_);
lean_ctor_set(v___x_731_, 1, v_lhs_709_);
lean_ctor_set(v___x_731_, 2, v_rhs_710_);
lean_ctor_set(v___x_731_, 3, v_defEqCtx_x3f_729_);
v___x_732_ = l_Lean_PersistentArray_push___redArg(v_postponed_724_, v___x_731_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 3, v___x_732_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_mctx_721_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_cache_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_zetaDeltaFVarIds_723_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_diag_725_);
v___x_734_ = v_reuseFailAlloc_737_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_st_ref_put(v___y_719_, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_730_);
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_751_, lean_object* v_rhs_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_751_, v_rhs_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_759_, lean_object* v_mvarId_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
if (lean_obj_tag(v_v_759_) == 5)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v_v_759_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v_v_759_, 1);
v___x_767_ = l_Lean_LMVarId_getLevel(v_a_766_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = l_Lean_LMVarId_getLevel(v_mvarId_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_779_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_nat_dec_lt(v_a_770_, v_a_768_);
lean_dec(v_a_768_);
lean_dec(v_a_770_);
v___x_775_ = lean_box(v___x_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_768_);
v_a_780_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_769_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_769_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_mvarId_760_);
v_a_788_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_767_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_767_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
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
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_mvarId_760_);
lean_dec(v_v_759_);
v___x_796_ = 0;
v___x_797_ = lean_box(v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_799_, lean_object* v_mvarId_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_799_, v_mvarId_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_807_, lean_object* v_v_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_a_815_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_874_; lean_object* v___y_888_; 
switch(lean_obj_tag(v_u_807_))
{
case 5:
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_ctor_get(v_u_807_, 0);
lean_inc(v_a_901_);
v___x_902_ = l_Lean_LMVarId_isReadOnly(v_a_901_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_999_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_999_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_999_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_999_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint8_t v___x_907_; 
v___x_907_ = lean_unbox(v_a_903_);
lean_dec(v_a_903_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_del_object(v___x_905_);
lean_inc(v_a_901_);
lean_inc(v_v_808_);
v___x_908_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_808_, v_a_901_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_985_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_985_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_985_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_985_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_919_; 
v___x_919_ = lean_unbox(v_a_909_);
lean_dec(v_a_909_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; 
v___x_920_ = l_Lean_Level_occurs(v_u_807_, v_v_808_);
if (v___x_920_ == 0)
{
lean_object* v_toCold_921_; lean_object* v_options_922_; uint8_t v_hasTrace_923_; 
lean_del_object(v___x_911_);
v_toCold_921_ = lean_ctor_get(v_a_811_, 0);
v_options_922_ = lean_ctor_get(v_toCold_921_, 2);
v_hasTrace_923_ = lean_ctor_get_uint8(v_options_922_, sizeof(void*)*1);
if (v_hasTrace_923_ == 0)
{
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_809_);
v___y_874_ = v_a_810_;
goto v___jp_873_;
}
else
{
lean_object* v_inheritedTraceOptions_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_inheritedTraceOptions_924_ = lean_ctor_get(v_toCold_921_, 11);
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_924_, v_options_922_, v___x_926_);
if (v___x_927_ == 0)
{
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_809_);
v___y_874_ = v_a_810_;
goto v___jp_873_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_inc_ref(v_u_807_);
v___x_928_ = l_Lean_MessageData_ofLevel(v_u_807_);
v___x_929_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_inc(v_v_808_);
v___x_931_ = l_Lean_MessageData_ofLevel(v_v_808_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_925_, v___x_932_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_809_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_dec_ref_known(v___x_933_, 1);
v___y_874_ = v_a_810_;
goto v___jp_873_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_810_);
lean_dec(v_v_808_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
else
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_Level_isMax(v_v_808_);
if (v___x_942_ == 0)
{
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
goto v___jp_913_;
}
else
{
uint8_t v___x_943_; 
v___x_943_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_807_, v_v_808_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_911_);
v___x_944_ = l_Lean_Level_mvarId_x21(v_u_807_);
lean_dec_ref_known(v_u_807_, 1);
v___x_945_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_944_, v_v_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_954_; 
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v___x_945_, 0);
lean_dec(v_unused_955_);
v___x_947_ = v___x_945_;
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
else
{
lean_dec(v___x_945_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = 1;
v___x_950_ = lean_box(v___x_949_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_952_ = v___x_947_;
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
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_945_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_945_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
goto v___jp_913_;
}
}
}
}
else
{
lean_object* v_toCold_964_; lean_object* v_options_965_; uint8_t v_hasTrace_966_; 
lean_del_object(v___x_911_);
v_toCold_964_ = lean_ctor_get(v_a_811_, 0);
v_options_965_ = lean_ctor_get(v_toCold_964_, 2);
v_hasTrace_966_ = lean_ctor_get_uint8(v_options_965_, sizeof(void*)*1);
if (v_hasTrace_966_ == 0)
{
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_809_);
v___y_888_ = v_a_810_;
goto v___jp_887_;
}
else
{
lean_object* v_inheritedTraceOptions_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_inheritedTraceOptions_967_ = lean_ctor_get(v_toCold_964_, 11);
v___x_968_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_969_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_967_, v_options_965_, v___x_969_);
if (v___x_970_ == 0)
{
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_809_);
v___y_888_ = v_a_810_;
goto v___jp_887_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_inc(v_v_808_);
v___x_971_ = l_Lean_MessageData_ofLevel(v_v_808_);
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_inc_ref(v_u_807_);
v___x_974_ = l_Lean_MessageData_ofLevel(v_u_807_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_968_, v___x_975_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_809_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_dec_ref_known(v___x_976_, 1);
v___y_888_ = v_a_810_;
goto v___jp_887_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_810_);
lean_dec(v_v_808_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
v___jp_913_:
{
uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_914_ = 2;
v___x_915_ = lean_box(v___x_914_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_915_);
v___x_917_ = v___x_911_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
v_a_986_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_908_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_908_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
v___x_994_ = 2;
v___x_995_ = lean_box(v___x_994_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_995_);
v___x_997_ = v___x_905_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
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
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref_known(v_u_807_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
v_a_1000_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_902_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_902_);
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
case 0:
{
switch(lean_obj_tag(v_v_808_))
{
case 5:
{
lean_dec_ref_known(v_v_808_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
goto v___jp_869_;
}
case 2:
{
lean_object* v_a_1008_; lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v_v_808_, 0);
lean_inc(v_a_1008_);
v_a_1009_ = lean_ctor_get(v_v_808_, 1);
lean_inc(v_a_1009_);
lean_dec_ref_known(v_v_808_, 2);
lean_inc(v_a_812_);
lean_inc_ref(v_a_811_);
lean_inc(v_a_810_);
lean_inc_ref(v_a_809_);
v___x_1010_ = lean_is_level_def_eq(v_u_807_, v_a_1008_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; uint8_t v___x_1012_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = lean_unbox(v_a_1011_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
lean_dec(v_a_1009_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
v___x_1013_ = lean_unbox(v_a_1011_);
lean_dec(v_a_1011_);
v_a_815_ = v___x_1013_;
goto v___jp_814_;
}
else
{
lean_object* v___x_1014_; 
lean_dec(v_a_1011_);
v___x_1014_ = lean_is_level_def_eq(v_u_807_, v_a_1009_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; uint8_t v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_unbox(v_a_1015_);
lean_dec(v_a_1015_);
v_a_815_ = v___x_1016_;
goto v___jp_814_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1014_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1014_);
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
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_a_1009_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
v_a_1025_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1010_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1010_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
case 3:
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v_v_808_, 1);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_v_808_, 2);
v___x_1034_ = lean_is_level_def_eq(v_u_807_, v_a_1033_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1039_ = lean_unbox(v_a_1035_);
lean_dec(v_a_1035_);
v___x_1040_ = l_Lean_Bool_toLBool(v___x_1039_);
v___x_1041_ = lean_box(v___x_1040_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1041_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1034_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1034_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
case 1:
{
uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec_ref_known(v_v_808_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
v___x_1054_ = 0;
v___x_1055_ = lean_box(v___x_1054_);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
return v___x_1056_;
}
default: 
{
v___y_824_ = v_a_809_;
v___y_825_ = v_a_810_;
v___y_826_ = v_a_811_;
v___y_827_ = v_a_812_;
goto v___jp_823_;
}
}
}
case 1:
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v_u_807_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v_u_807_, 1);
if (lean_obj_tag(v_v_808_) == 5)
{
lean_dec_ref_known(v_v_808_, 1);
lean_dec(v_a_1057_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
goto v___jp_869_;
}
else
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Lean_Level_isParam(v_v_808_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Lean_Level_isMVar(v_a_1057_);
if (v___x_1100_ == 0)
{
goto v___jp_1058_;
}
else
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Level_occurs(v_a_1057_, v_v_808_);
if (v___x_1101_ == 0)
{
goto v___jp_1058_;
}
else
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v_a_1057_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
v___x_1102_ = 2;
v___x_1103_ = lean_box(v___x_1102_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
}
else
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v_a_1057_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_v_808_);
v___x_1105_ = 0;
v___x_1106_ = lean_box(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
v___jp_1058_:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_decLevel_x3f(v_v_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1090_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1090_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1090_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec(v_a_1057_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
v___x_1064_ = 2;
v___x_1065_ = lean_box(v___x_1064_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
lean_object* v_val_1069_; lean_object* v___x_1070_; 
lean_del_object(v___x_1062_);
v_val_1069_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_a_1060_, 1);
v___x_1070_ = lean_is_level_def_eq(v_a_1057_, v_val_1069_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1081_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
uint8_t v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1075_ = lean_unbox(v_a_1071_);
lean_dec(v_a_1071_);
v___x_1076_ = l_Lean_Bool_toLBool(v___x_1075_);
v___x_1077_ = lean_box(v___x_1076_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1077_);
v___x_1079_ = v___x_1073_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1070_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1070_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1057_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
v_a_1091_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1059_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1059_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
default: 
{
if (lean_obj_tag(v_v_808_) == 5)
{
lean_dec_ref_known(v_v_808_, 1);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_u_807_);
goto v___jp_869_;
}
else
{
v___y_824_ = v_a_809_;
v___y_825_ = v_a_810_;
v___y_826_ = v_a_811_;
v___y_827_ = v_a_812_;
goto v___jp_823_;
}
}
}
v___jp_814_:
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = l_Lean_Bool_toLBool(v_a_815_);
v___x_817_ = lean_box(v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
v___jp_819_:
{
uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = 2;
v___x_821_ = lean_box(v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
v___jp_823_:
{
uint8_t v_univApprox_828_; 
v_univApprox_828_ = lean_ctor_get_uint8(v___y_824_, sizeof(void*)*7 + 1);
if (v_univApprox_828_ == 0)
{
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v_v_808_);
lean_dec(v_u_807_);
goto v___jp_819_;
}
else
{
lean_object* v___x_829_; 
lean_inc(v_v_808_);
lean_inc(v_u_807_);
v___x_829_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_807_, v_v_808_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_860_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_860_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_860_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_860_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint8_t v___x_834_; 
v___x_834_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_del_object(v___x_832_);
v___x_835_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_807_, v_v_808_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_846_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_846_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
uint8_t v___x_840_; 
v___x_840_ = lean_unbox(v_a_836_);
lean_dec(v_a_836_);
if (v___x_840_ == 0)
{
lean_del_object(v___x_838_);
goto v___jp_819_;
}
else
{
uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = 1;
v___x_842_ = lean_box(v___x_841_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_835_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_835_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v_v_808_);
lean_dec(v_u_807_);
v___x_855_ = 1;
v___x_856_ = lean_box(v___x_855_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_856_);
v___x_858_ = v___x_832_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v_v_808_);
lean_dec(v_u_807_);
v_a_861_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_829_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_829_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
v___jp_869_:
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = 2;
v___x_871_ = lean_box(v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
v___jp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_885_; 
v___x_875_ = l_Lean_Level_mvarId_x21(v_u_807_);
lean_dec(v_u_807_);
v___x_876_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_875_, v_v_808_, v___y_874_);
lean_dec(v___y_874_);
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
v___jp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_899_; 
v___x_889_ = l_Lean_Level_mvarId_x21(v_v_808_);
lean_dec(v_v_808_);
v___x_890_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_889_, v_u_807_, v___y_888_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1108_, lean_object* v_v_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1108_, v_v_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_mctx_1120_; lean_object* v___x_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___x_1124_; lean_object* v_cache_1125_; lean_object* v_zetaDeltaFVarIds_1126_; lean_object* v_postponed_1127_; lean_object* v_diag_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1137_; 
v___x_1119_ = lean_st_ref_get(v___y_1117_);
v_mctx_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref(v_mctx_1120_);
lean_dec(v___x_1119_);
v___x_1121_ = lean_instantiate_level_mvars(v_mctx_1120_, v_l_1116_);
v_fst_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_fst_1122_);
v_snd_1123_ = lean_ctor_get(v___x_1121_, 1);
lean_inc(v_snd_1123_);
lean_dec_ref(v___x_1121_);
v___x_1124_ = lean_st_ref_take(v___y_1117_);
v_cache_1125_ = lean_ctor_get(v___x_1124_, 1);
v_zetaDeltaFVarIds_1126_ = lean_ctor_get(v___x_1124_, 2);
v_postponed_1127_ = lean_ctor_get(v___x_1124_, 3);
v_diag_1128_ = lean_ctor_get(v___x_1124_, 4);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1138_);
v___x_1130_ = v___x_1124_;
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_diag_1128_);
lean_inc(v_postponed_1127_);
lean_inc(v_zetaDeltaFVarIds_1126_);
lean_inc(v_cache_1125_);
lean_dec(v___x_1124_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_fst_1122_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_fst_1122_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_cache_1125_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_zetaDeltaFVarIds_1126_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_postponed_1127_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_diag_1128_);
v___x_1133_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_st_ref_put(v___y_1117_, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_snd_1123_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1139_, v___y_1140_);
lean_dec(v___y_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1143_, v___y_1145_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1156_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(32u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1160_ = ((size_t)5ULL);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_unsigned_to_nat(32u);
v___x_1163_ = lean_mk_empty_array_with_capacity(v___x_1162_);
v___x_1164_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1165_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v___x_1161_);
lean_ctor_set(v___x_1165_, 3, v___x_1161_);
lean_ctor_set_usize(v___x_1165_, 4, v___x_1160_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v_traceState_1169_; lean_object* v_traces_1170_; lean_object* v___x_1171_; lean_object* v_traceState_1172_; lean_object* v_env_1173_; lean_object* v_nextMacroScope_1174_; lean_object* v_ngen_1175_; lean_object* v_auxDeclNGen_1176_; lean_object* v_cache_1177_; lean_object* v_recordedDeps_1178_; lean_object* v_messages_1179_; lean_object* v_infoState_1180_; lean_object* v_snapshotTasks_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1200_; 
v___x_1168_ = lean_st_ref_get(v___y_1166_);
v_traceState_1169_ = lean_ctor_get(v___x_1168_, 4);
lean_inc_ref(v_traceState_1169_);
lean_dec(v___x_1168_);
v_traces_1170_ = lean_ctor_get(v_traceState_1169_, 0);
lean_inc_ref(v_traces_1170_);
lean_dec_ref(v_traceState_1169_);
v___x_1171_ = lean_st_ref_take(v___y_1166_);
v_traceState_1172_ = lean_ctor_get(v___x_1171_, 4);
v_env_1173_ = lean_ctor_get(v___x_1171_, 0);
v_nextMacroScope_1174_ = lean_ctor_get(v___x_1171_, 1);
v_ngen_1175_ = lean_ctor_get(v___x_1171_, 2);
v_auxDeclNGen_1176_ = lean_ctor_get(v___x_1171_, 3);
v_cache_1177_ = lean_ctor_get(v___x_1171_, 5);
v_recordedDeps_1178_ = lean_ctor_get(v___x_1171_, 6);
v_messages_1179_ = lean_ctor_get(v___x_1171_, 7);
v_infoState_1180_ = lean_ctor_get(v___x_1171_, 8);
v_snapshotTasks_1181_ = lean_ctor_get(v___x_1171_, 9);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1183_ = v___x_1171_;
v_isShared_1184_ = v_isSharedCheck_1200_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snapshotTasks_1181_);
lean_inc(v_infoState_1180_);
lean_inc(v_messages_1179_);
lean_inc(v_recordedDeps_1178_);
lean_inc(v_cache_1177_);
lean_inc(v_traceState_1172_);
lean_inc(v_auxDeclNGen_1176_);
lean_inc(v_ngen_1175_);
lean_inc(v_nextMacroScope_1174_);
lean_inc(v_env_1173_);
lean_dec(v___x_1171_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1200_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
uint64_t v_tid_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1198_; 
v_tid_1185_ = lean_ctor_get_uint64(v_traceState_1172_, sizeof(void*)*1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_traceState_1172_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_traceState_1172_, 0);
lean_dec(v_unused_1199_);
v___x_1187_ = v_traceState_1172_;
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
else
{
lean_dec(v_traceState_1172_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1189_);
lean_ctor_set_uint64(v_reuseFailAlloc_1197_, sizeof(void*)*1, v_tid_1185_);
v___x_1191_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 4, v___x_1191_);
v___x_1193_ = v___x_1183_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_env_1173_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_nextMacroScope_1174_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_ngen_1175_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_auxDeclNGen_1176_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1196_, 5, v_cache_1177_);
lean_ctor_set(v_reuseFailAlloc_1196_, 6, v_recordedDeps_1178_);
lean_ctor_set(v_reuseFailAlloc_1196_, 7, v_messages_1179_);
lean_ctor_set(v_reuseFailAlloc_1196_, 8, v_infoState_1180_);
lean_ctor_set(v_reuseFailAlloc_1196_, 9, v_snapshotTasks_1181_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_st_ref_put(v___y_1166_, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_traces_1170_);
return v___x_1195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1201_);
lean_dec(v___y_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1216_, lean_object* v_k_1217_, uint8_t v_v_1218_){
_start:
{
lean_object* v_map_1219_; uint8_t v_hasTrace_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1234_; 
v_map_1219_ = lean_ctor_get(v_o_1216_, 0);
v_hasTrace_1220_ = lean_ctor_get_uint8(v_o_1216_, sizeof(void*)*1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_o_1216_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1222_ = v_o_1216_;
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_map_1219_);
lean_dec(v_o_1216_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1224_, 0, v_v_1218_);
lean_inc(v_k_1217_);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1217_, v___x_1224_, v_map_1219_);
if (v_hasTrace_1220_ == 0)
{
lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1229_; 
v___x_1226_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1227_ = l_Lean_Name_isPrefixOf(v___x_1226_, v_k_1217_);
lean_dec(v_k_1217_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1225_);
v___x_1229_ = v___x_1222_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1225_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*1, v___x_1227_);
return v___x_1229_;
}
}
else
{
lean_object* v___x_1232_; 
lean_dec(v_k_1217_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1225_);
v___x_1232_ = v___x_1222_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1233_, sizeof(void*)*1, v_hasTrace_1220_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1235_, lean_object* v_k_1236_, lean_object* v_v_1237_){
_start:
{
uint8_t v_v_boxed_1238_; lean_object* v_res_1239_; 
v_v_boxed_1238_ = lean_unbox(v_v_1237_);
v_res_1239_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1235_, v_k_1236_, v_v_boxed_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1240_, lean_object* v_opt_1241_){
_start:
{
lean_object* v_name_1242_; lean_object* v_defValue_1243_; lean_object* v_map_1244_; lean_object* v___x_1245_; 
v_name_1242_ = lean_ctor_get(v_opt_1241_, 0);
v_defValue_1243_ = lean_ctor_get(v_opt_1241_, 1);
v_map_1244_ = lean_ctor_get(v_opts_1240_, 0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1244_, v_name_1242_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_inc(v_defValue_1243_);
return v_defValue_1243_;
}
else
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1245_, 1);
if (lean_obj_tag(v_val_1246_) == 3)
{
lean_object* v_v_1247_; 
v_v_1247_ = lean_ctor_get(v_val_1246_, 0);
lean_inc(v_v_1247_);
lean_dec_ref_known(v_val_1246_, 1);
return v_v_1247_;
}
else
{
lean_dec(v_val_1246_);
lean_inc(v_defValue_1243_);
return v_defValue_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1248_, lean_object* v_opt_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1248_, v_opt_1249_);
lean_dec_ref(v_opt_1249_);
lean_dec_ref(v_opts_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1251_, lean_object* v_opt_1252_){
_start:
{
lean_object* v_name_1253_; lean_object* v_defValue_1254_; lean_object* v_map_1255_; lean_object* v___x_1256_; 
v_name_1253_ = lean_ctor_get(v_opt_1252_, 0);
v_defValue_1254_ = lean_ctor_get(v_opt_1252_, 1);
v_map_1255_ = lean_ctor_get(v_opts_1251_, 0);
v___x_1256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1255_, v_name_1253_);
if (lean_obj_tag(v___x_1256_) == 0)
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_unbox(v_defValue_1254_);
return v___x_1257_;
}
else
{
lean_object* v_val_1258_; 
v_val_1258_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___x_1256_, 1);
if (lean_obj_tag(v_val_1258_) == 1)
{
uint8_t v_v_1259_; 
v_v_1259_ = lean_ctor_get_uint8(v_val_1258_, 0);
lean_dec_ref_known(v_val_1258_, 0);
return v_v_1259_;
}
else
{
uint8_t v___x_1260_; 
lean_dec(v_val_1258_);
v___x_1260_ = lean_unbox(v_defValue_1254_);
return v___x_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1261_, lean_object* v_opt_1262_){
_start:
{
uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1261_, v_opt_1262_);
lean_dec_ref(v_opt_1262_);
lean_dec_ref(v_opts_1261_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1265_, lean_object* v_lhs_1266_, lean_object* v_rhs_1267_, uint8_t v___x_1268_, lean_object* v___x_1269_, lean_object* v___x_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
if (v___x_1265_ == 0)
{
lean_object* v___x_1295_; lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_a_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
lean_inc(v_lhs_1266_);
v___x_1295_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1266_, v___y_1272_);
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref(v___x_1295_);
v___x_1297_ = l_Lean_Level_normalize(v_a_1296_);
lean_dec(v_a_1296_);
lean_inc(v_rhs_1267_);
v___x_1298_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1267_, v___y_1272_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = l_Lean_Level_normalize(v_a_1299_);
lean_dec(v_a_1299_);
v___x_1301_ = lean_level_eq(v_lhs_1266_, v___x_1297_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
v___x_1302_ = lean_is_level_def_eq(v___x_1297_, v___x_1300_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
return v___x_1302_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_level_eq(v_rhs_1267_, v___x_1300_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
v___x_1304_ = lean_is_level_def_eq(v___x_1297_, v___x_1300_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; 
lean_dec(v___x_1300_);
lean_dec(v___x_1297_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v_rhs_1267_);
lean_inc(v_lhs_1266_);
v___x_1305_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1266_, v_rhs_1267_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1392_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1392_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1392_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
uint8_t v___x_1310_; uint8_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = 2;
v___x_1311_ = lean_unbox(v_a_1306_);
v___x_1312_ = l_Lean_instBEqLBool_beq(v___x_1311_, v___x_1310_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; uint8_t v___x_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v___x_1313_ = 1;
v___x_1314_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
v___x_1315_ = l_Lean_instBEqLBool_beq(v___x_1314_, v___x_1313_);
v___x_1316_ = lean_box(v___x_1315_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1316_);
v___x_1318_ = v___x_1308_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v___x_1320_; 
lean_del_object(v___x_1308_);
lean_dec(v_a_1306_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v_lhs_1266_);
lean_inc(v_rhs_1267_);
v___x_1320_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1267_, v_lhs_1266_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1383_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1383_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1383_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_unbox(v_a_1321_);
v___x_1326_ = l_Lean_instBEqLBool_beq(v___x_1325_, v___x_1310_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; uint8_t v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v___x_1327_ = 1;
v___x_1328_ = lean_unbox(v_a_1321_);
lean_dec(v_a_1321_);
v___x_1329_ = l_Lean_instBEqLBool_beq(v___x_1328_, v___x_1327_);
v___x_1330_ = lean_box(v___x_1329_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1330_);
v___x_1332_ = v___x_1323_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v___x_1334_; 
lean_del_object(v___x_1323_);
lean_dec(v_a_1321_);
lean_inc(v_lhs_1266_);
v___x_1334_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1266_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; uint8_t v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = lean_unbox(v_a_1335_);
lean_dec(v_a_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_inc(v_rhs_1267_);
v___x_1337_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1267_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1382_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1382_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1382_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_unbox(v_a_1338_);
lean_dec(v_a_1338_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; uint8_t v_isDefEqStuckEx_1371_; 
v___x_1370_ = l_Lean_Meta_Context_config(v___y_1271_);
v_isDefEqStuckEx_1371_ = lean_ctor_get_uint8(v___x_1370_, 4);
lean_dec_ref(v___x_1370_);
if (v_isDefEqStuckEx_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v___x_1372_ = lean_box(v___x_1265_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1372_);
v___x_1374_ = v___x_1340_;
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
uint8_t v___x_1376_; 
v___x_1376_ = l_Lean_Level_isMVar(v_lhs_1266_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_Level_isMVar(v_rhs_1267_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v___x_1378_ = lean_box(v___x_1377_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1378_);
v___x_1380_ = v___x_1340_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_del_object(v___x_1340_);
goto v___jp_1342_;
}
}
else
{
lean_del_object(v___x_1340_);
goto v___jp_1342_;
}
}
}
else
{
lean_del_object(v___x_1340_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
goto v___jp_1276_;
}
v___jp_1342_:
{
lean_object* v_toCold_1343_; lean_object* v_options_1344_; uint8_t v_hasTrace_1345_; 
v_toCold_1343_ = lean_ctor_get(v___y_1273_, 0);
v_options_1344_ = lean_ctor_get(v_toCold_1343_, 2);
v_hasTrace_1345_ = lean_ctor_get_uint8(v_options_1344_, sizeof(void*)*1);
if (v_hasTrace_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v___x_1346_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1346_;
}
else
{
lean_object* v_inheritedTraceOptions_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_inheritedTraceOptions_1347_ = lean_ctor_get(v_toCold_1343_, 11);
v___x_1348_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1349_ = l_Lean_Name_mkStr3(v___x_1269_, v___x_1270_, v___x_1348_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1349_);
v___x_1351_ = l_Lean_Name_append(v___x_1350_, v___x_1349_);
v___x_1352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1347_, v_options_1344_, v___x_1351_);
lean_dec(v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v___x_1349_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v___x_1353_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = l_Lean_MessageData_ofLevel(v_lhs_1266_);
v___x_1355_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_MessageData_ofLevel(v_rhs_1267_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1349_, v___x_1358_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1360_; 
lean_dec_ref_known(v___x_1359_, 1);
v___x_1360_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1360_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_a_1361_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1359_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1359_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
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
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
return v___x_1337_;
}
}
else
{
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
goto v___jp_1276_;
}
}
else
{
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v_a_1384_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1320_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1320_);
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
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec(v_rhs_1267_);
lean_dec(v_lhs_1266_);
v_a_1393_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1305_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1305_);
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
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
v___x_1401_ = l_Lean_Level_getOffset(v_lhs_1266_);
lean_dec(v_lhs_1266_);
v___x_1402_ = l_Lean_Level_getOffset(v_rhs_1267_);
lean_dec(v_rhs_1267_);
v___x_1403_ = lean_nat_dec_eq(v___x_1401_, v___x_1402_);
lean_dec(v___x_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
v___jp_1276_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1266_, v_rhs_1267_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1277_, 0);
lean_dec(v_unused_1286_);
v___x_1279_ = v___x_1277_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v___x_1277_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_box(v___x_1268_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1277_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1277_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1406_, lean_object* v_lhs_1407_, lean_object* v_rhs_1408_, lean_object* v___x_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_13576__boxed_1417_; uint8_t v___x_13577__boxed_1418_; lean_object* v_res_1419_; 
v___x_13576__boxed_1417_ = lean_unbox(v___x_1406_);
v___x_13577__boxed_1418_ = lean_unbox(v___x_1409_);
v_res_1419_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13576__boxed_1417_, v_lhs_1407_, v_rhs_1408_, v___x_13577__boxed_1418_, v___x_1410_, v___x_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
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
lean_object* v_toCold_1477_; lean_object* v_currRecDepth_1478_; lean_object* v_ref_1479_; uint16_t v_optionFlags_1480_; uint8_t v_suppressElabErrors_1481_; uint8_t v_checkDeprecated_1482_; uint8_t v_isRecordingDeps_1483_; lean_object* v_ref_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_traceState_1487_; lean_object* v_traces_1488_; lean_object* v___x_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_1492_; lean_object* v_msg_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1533_; 
v_toCold_1477_ = lean_ctor_get(v___y_1474_, 0);
v_currRecDepth_1478_ = lean_ctor_get(v___y_1474_, 1);
v_ref_1479_ = lean_ctor_get(v___y_1474_, 2);
v_optionFlags_1480_ = lean_ctor_get_uint16(v___y_1474_, sizeof(void*)*3);
v_suppressElabErrors_1481_ = lean_ctor_get_uint8(v___y_1474_, sizeof(void*)*3 + 2);
v_checkDeprecated_1482_ = lean_ctor_get_uint8(v___y_1474_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1483_ = lean_ctor_get_uint8(v___y_1474_, sizeof(void*)*3 + 4);
v_ref_1484_ = l_Lean_replaceRef(v_ref_1470_, v_ref_1479_);
lean_inc(v_currRecDepth_1478_);
lean_inc_ref(v_toCold_1477_);
v___x_1485_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1485_, 0, v_toCold_1477_);
lean_ctor_set(v___x_1485_, 1, v_currRecDepth_1478_);
lean_ctor_set(v___x_1485_, 2, v_ref_1484_);
lean_ctor_set_uint16(v___x_1485_, sizeof(void*)*3, v_optionFlags_1480_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 2, v_suppressElabErrors_1481_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 3, v_checkDeprecated_1482_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 4, v_isRecordingDeps_1483_);
v___x_1486_ = lean_st_ref_get(v___y_1475_);
v_traceState_1487_ = lean_ctor_get(v___x_1486_, 4);
lean_inc_ref(v_traceState_1487_);
lean_dec(v___x_1486_);
v_traces_1488_ = lean_ctor_get(v_traceState_1487_, 0);
lean_inc_ref(v_traces_1488_);
lean_dec_ref(v_traceState_1487_);
v___x_1489_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1488_);
lean_dec_ref(v_traces_1488_);
v_sz_1490_ = lean_array_size(v___x_1489_);
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1490_, v___x_1491_, v___x_1489_);
v_msg_1493_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1493_, 0, v_data_1469_);
lean_ctor_set(v_msg_1493_, 1, v_msg_1471_);
lean_ctor_set(v_msg_1493_, 2, v___x_1492_);
v___x_1494_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1493_, v___y_1472_, v___y_1473_, v___x_1485_, v___y_1475_);
lean_dec_ref_known(v___x_1485_, 3);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1533_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1533_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v_traceState_1500_; lean_object* v_env_1501_; lean_object* v_nextMacroScope_1502_; lean_object* v_ngen_1503_; lean_object* v_auxDeclNGen_1504_; lean_object* v_cache_1505_; lean_object* v_recordedDeps_1506_; lean_object* v_messages_1507_; lean_object* v_infoState_1508_; lean_object* v_snapshotTasks_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1532_; 
v___x_1499_ = lean_st_ref_take(v___y_1475_);
v_traceState_1500_ = lean_ctor_get(v___x_1499_, 4);
v_env_1501_ = lean_ctor_get(v___x_1499_, 0);
v_nextMacroScope_1502_ = lean_ctor_get(v___x_1499_, 1);
v_ngen_1503_ = lean_ctor_get(v___x_1499_, 2);
v_auxDeclNGen_1504_ = lean_ctor_get(v___x_1499_, 3);
v_cache_1505_ = lean_ctor_get(v___x_1499_, 5);
v_recordedDeps_1506_ = lean_ctor_get(v___x_1499_, 6);
v_messages_1507_ = lean_ctor_get(v___x_1499_, 7);
v_infoState_1508_ = lean_ctor_get(v___x_1499_, 8);
v_snapshotTasks_1509_ = lean_ctor_get(v___x_1499_, 9);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1511_ = v___x_1499_;
v_isShared_1512_ = v_isSharedCheck_1532_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_snapshotTasks_1509_);
lean_inc(v_infoState_1508_);
lean_inc(v_messages_1507_);
lean_inc(v_recordedDeps_1506_);
lean_inc(v_cache_1505_);
lean_inc(v_traceState_1500_);
lean_inc(v_auxDeclNGen_1504_);
lean_inc(v_ngen_1503_);
lean_inc(v_nextMacroScope_1502_);
lean_inc(v_env_1501_);
lean_dec(v___x_1499_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1532_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
uint64_t v_tid_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1530_; 
v_tid_1513_ = lean_ctor_get_uint64(v_traceState_1500_, sizeof(void*)*1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_traceState_1500_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_traceState_1500_, 0);
lean_dec(v_unused_1531_);
v___x_1515_ = v_traceState_1500_;
v_isShared_1516_ = v_isSharedCheck_1530_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_traceState_1500_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1530_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_ref_1470_);
lean_ctor_set(v___x_1518_, 1, v_a_1495_);
v___x_1519_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1468_, v___x_1518_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1519_);
v___x_1521_ = v___x_1515_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1519_);
lean_ctor_set_uint64(v_reuseFailAlloc_1529_, sizeof(void*)*1, v_tid_1513_);
v___x_1521_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 4, v___x_1521_);
v___x_1523_ = v___x_1511_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_env_1501_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_nextMacroScope_1502_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_ngen_1503_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_auxDeclNGen_1504_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v_cache_1505_);
lean_ctor_set(v_reuseFailAlloc_1528_, 6, v_recordedDeps_1506_);
lean_ctor_set(v_reuseFailAlloc_1528_, 7, v_messages_1507_);
lean_ctor_set(v_reuseFailAlloc_1528_, 8, v_infoState_1508_);
lean_ctor_set(v_reuseFailAlloc_1528_, 9, v_snapshotTasks_1509_);
v___x_1523_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_st_ref_put(v___y_1475_, v___x_1523_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1517_);
v___x_1526_ = v___x_1497_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1517_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1534_, lean_object* v_data_1535_, lean_object* v_ref_1536_, lean_object* v_msg_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1534_, v_data_1535_, v_ref_1536_, v_msg_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1543_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1544_; double v___x_1545_; 
v___x_1544_ = lean_unsigned_to_nat(1000u);
v___x_1545_ = lean_float_of_nat(v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1546_, uint8_t v_collapsed_1547_, lean_object* v_tag_1548_, lean_object* v_opts_1549_, uint8_t v_clsEnabled_1550_, lean_object* v_oldTraces_1551_, lean_object* v_ref_1552_, lean_object* v_msg_1553_, lean_object* v_resStartStop_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v_data_1563_; lean_object* v_fst_1574_; lean_object* v_snd_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; uint8_t v___y_1588_; double v___y_1620_; 
v_fst_1560_ = lean_ctor_get(v_resStartStop_1554_, 0);
lean_inc(v_fst_1560_);
v_snd_1561_ = lean_ctor_get(v_resStartStop_1554_, 1);
lean_inc(v_snd_1561_);
lean_dec_ref(v_resStartStop_1554_);
v_fst_1574_ = lean_ctor_get(v_snd_1561_, 0);
lean_inc(v_fst_1574_);
v_snd_1575_ = lean_ctor_get(v_snd_1561_, 1);
lean_inc(v_snd_1575_);
lean_dec(v_snd_1561_);
v___x_1576_ = l_Lean_trace_profiler;
v___x_1577_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1549_, v___x_1576_);
if (v___x_1577_ == 0)
{
v___y_1588_ = v___x_1577_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1626_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1549_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; double v___x_1629_; double v___x_1630_; double v___x_1631_; 
v___x_1627_ = l_Lean_trace_profiler_threshold;
v___x_1628_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1549_, v___x_1627_);
v___x_1629_ = lean_float_of_nat(v___x_1628_);
v___x_1630_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1631_ = lean_float_div(v___x_1629_, v___x_1630_);
v___y_1620_ = v___x_1631_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; double v___x_1634_; 
v___x_1632_ = l_Lean_trace_profiler_threshold;
v___x_1633_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1549_, v___x_1632_);
v___x_1634_ = lean_float_of_nat(v___x_1633_);
v___y_1620_ = v___x_1634_;
goto v___jp_1619_;
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1551_, v_data_1563_, v_ref_1552_, v_msg_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v___x_1564_, 1);
v___x_1565_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1560_);
return v___x_1565_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_fst_1560_);
v_a_1566_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1564_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
v___jp_1578_:
{
uint8_t v_result_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; double v___x_1582_; lean_object* v_data_1583_; 
v_result_1579_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1560_);
v___x_1580_ = lean_box(v_result_1579_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
v___x_1582_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1548_);
lean_inc_ref(v___x_1581_);
lean_inc(v_cls_1546_);
v_data_1583_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1583_, 0, v_cls_1546_);
lean_ctor_set(v_data_1583_, 1, v___x_1581_);
lean_ctor_set(v_data_1583_, 2, v_tag_1548_);
lean_ctor_set_float(v_data_1583_, sizeof(void*)*3, v___x_1582_);
lean_ctor_set_float(v_data_1583_, sizeof(void*)*3 + 8, v___x_1582_);
lean_ctor_set_uint8(v_data_1583_, sizeof(void*)*3 + 16, v_collapsed_1547_);
if (v___x_1577_ == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
lean_dec(v_snd_1575_);
lean_dec(v_fst_1574_);
lean_dec_ref(v_tag_1548_);
lean_dec(v_cls_1546_);
v_data_1563_ = v_data_1583_;
goto v___jp_1562_;
}
else
{
lean_object* v_data_1584_; double v___x_1585_; double v___x_1586_; 
lean_dec_ref_known(v_data_1583_, 3);
v_data_1584_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1584_, 0, v_cls_1546_);
lean_ctor_set(v_data_1584_, 1, v___x_1581_);
lean_ctor_set(v_data_1584_, 2, v_tag_1548_);
v___x_1585_ = lean_unbox_float(v_fst_1574_);
lean_dec(v_fst_1574_);
lean_ctor_set_float(v_data_1584_, sizeof(void*)*3, v___x_1585_);
v___x_1586_ = lean_unbox_float(v_snd_1575_);
lean_dec(v_snd_1575_);
lean_ctor_set_float(v_data_1584_, sizeof(void*)*3 + 8, v___x_1586_);
lean_ctor_set_uint8(v_data_1584_, sizeof(void*)*3 + 16, v_collapsed_1547_);
v_data_1563_ = v_data_1584_;
goto v___jp_1562_;
}
}
v___jp_1587_:
{
if (v_clsEnabled_1550_ == 0)
{
if (v___y_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v_traceState_1590_; lean_object* v_env_1591_; lean_object* v_nextMacroScope_1592_; lean_object* v_ngen_1593_; lean_object* v_auxDeclNGen_1594_; lean_object* v_cache_1595_; lean_object* v_recordedDeps_1596_; lean_object* v_messages_1597_; lean_object* v_infoState_1598_; lean_object* v_snapshotTasks_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_snd_1575_);
lean_dec(v_fst_1574_);
lean_dec_ref(v_msg_1553_);
lean_dec(v_ref_1552_);
lean_dec_ref(v_tag_1548_);
lean_dec(v_cls_1546_);
v___x_1589_ = lean_st_ref_take(v___y_1558_);
v_traceState_1590_ = lean_ctor_get(v___x_1589_, 4);
v_env_1591_ = lean_ctor_get(v___x_1589_, 0);
v_nextMacroScope_1592_ = lean_ctor_get(v___x_1589_, 1);
v_ngen_1593_ = lean_ctor_get(v___x_1589_, 2);
v_auxDeclNGen_1594_ = lean_ctor_get(v___x_1589_, 3);
v_cache_1595_ = lean_ctor_get(v___x_1589_, 5);
v_recordedDeps_1596_ = lean_ctor_get(v___x_1589_, 6);
v_messages_1597_ = lean_ctor_get(v___x_1589_, 7);
v_infoState_1598_ = lean_ctor_get(v___x_1589_, 8);
v_snapshotTasks_1599_ = lean_ctor_get(v___x_1589_, 9);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1601_ = v___x_1589_;
v_isShared_1602_ = v_isSharedCheck_1618_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snapshotTasks_1599_);
lean_inc(v_infoState_1598_);
lean_inc(v_messages_1597_);
lean_inc(v_recordedDeps_1596_);
lean_inc(v_cache_1595_);
lean_inc(v_traceState_1590_);
lean_inc(v_auxDeclNGen_1594_);
lean_inc(v_ngen_1593_);
lean_inc(v_nextMacroScope_1592_);
lean_inc(v_env_1591_);
lean_dec(v___x_1589_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1618_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
uint64_t v_tid_1603_; lean_object* v_traces_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1617_; 
v_tid_1603_ = lean_ctor_get_uint64(v_traceState_1590_, sizeof(void*)*1);
v_traces_1604_ = lean_ctor_get(v_traceState_1590_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_traceState_1590_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1606_ = v_traceState_1590_;
v_isShared_1607_ = v_isSharedCheck_1617_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_traces_1604_);
lean_dec(v_traceState_1590_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1617_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1551_, v_traces_1604_);
lean_dec_ref(v_traces_1604_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1608_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1608_);
lean_ctor_set_uint64(v_reuseFailAlloc_1616_, sizeof(void*)*1, v_tid_1603_);
v___x_1610_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v___x_1610_);
v___x_1612_ = v___x_1601_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_env_1591_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_nextMacroScope_1592_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_ngen_1593_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_auxDeclNGen_1594_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v_cache_1595_);
lean_ctor_set(v_reuseFailAlloc_1615_, 6, v_recordedDeps_1596_);
lean_ctor_set(v_reuseFailAlloc_1615_, 7, v_messages_1597_);
lean_ctor_set(v_reuseFailAlloc_1615_, 8, v_infoState_1598_);
lean_ctor_set(v_reuseFailAlloc_1615_, 9, v_snapshotTasks_1599_);
v___x_1612_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_st_ref_put(v___y_1558_, v___x_1612_);
v___x_1614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1560_);
return v___x_1614_;
}
}
}
}
}
else
{
goto v___jp_1578_;
}
}
else
{
goto v___jp_1578_;
}
}
v___jp_1619_:
{
double v___x_1621_; double v___x_1622_; double v___x_1623_; uint8_t v___x_1624_; 
v___x_1621_ = lean_unbox_float(v_snd_1575_);
v___x_1622_ = lean_unbox_float(v_fst_1574_);
v___x_1623_ = lean_float_sub(v___x_1621_, v___x_1622_);
v___x_1624_ = lean_float_decLt(v___y_1620_, v___x_1623_);
v___y_1588_ = v___x_1624_;
goto v___jp_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1635_, lean_object* v_collapsed_1636_, lean_object* v_tag_1637_, lean_object* v_opts_1638_, lean_object* v_clsEnabled_1639_, lean_object* v_oldTraces_1640_, lean_object* v_ref_1641_, lean_object* v_msg_1642_, lean_object* v_resStartStop_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_collapsed_boxed_1649_; uint8_t v_clsEnabled_boxed_1650_; lean_object* v_res_1651_; 
v_collapsed_boxed_1649_ = lean_unbox(v_collapsed_1636_);
v_clsEnabled_boxed_1650_ = lean_unbox(v_clsEnabled_1639_);
v_res_1651_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1635_, v_collapsed_boxed_1649_, v_tag_1637_, v_opts_1638_, v_clsEnabled_boxed_1650_, v_oldTraces_1640_, v_ref_1641_, v_msg_1642_, v_resStartStop_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_opts_1638_);
return v_res_1651_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1652_; double v___x_1653_; 
v___x_1652_ = lean_unsigned_to_nat(1000000000u);
v___x_1653_ = lean_float_of_nat(v___x_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1669_ = l_Lean_Name_append(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; lean_object* v___y_1690_; lean_object* v_a_1691_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; uint8_t v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; lean_object* v_a_1714_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; uint16_t v___y_1739_; uint8_t v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v_toCold_1743_; lean_object* v_currRecDepth_1744_; lean_object* v_ref_1745_; uint8_t v_suppressElabErrors_1746_; uint8_t v_checkDeprecated_1747_; uint8_t v_isRecordingDeps_1748_; lean_object* v___y_1749_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; uint8_t v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint16_t v___y_1827_; uint8_t v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint16_t v___y_1852_; uint8_t v___y_1853_; uint8_t v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; uint8_t v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; uint16_t v___y_1892_; uint8_t v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1896_; lean_object* v___y_1898_; lean_object* v___y_1899_; uint8_t v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; uint8_t v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1905_; uint16_t v___y_1906_; uint8_t v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1916_; lean_object* v___y_1917_; lean_object* v_lhs_1939_; lean_object* v_rhs_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; 
if (lean_obj_tag(v_x_1670_) == 1)
{
if (lean_obj_tag(v_x_1671_) == 1)
{
lean_object* v_a_1972_; lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1972_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v_x_1670_, 1);
v_a_1973_ = lean_ctor_get(v_x_1671_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v_x_1671_, 1);
v___x_1974_ = lean_is_level_def_eq(v_a_1972_, v_a_1973_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1974_;
}
else
{
v_lhs_1939_ = v_x_1670_;
v_rhs_1940_ = v_x_1671_;
v___y_1941_ = v_a_1672_;
v___y_1942_ = v_a_1673_;
v___y_1943_ = v_a_1674_;
v___y_1944_ = v_a_1675_;
goto v___jp_1938_;
}
}
else
{
v_lhs_1939_ = v_x_1670_;
v_rhs_1940_ = v_x_1671_;
v___y_1941_ = v_a_1672_;
v___y_1942_ = v_a_1673_;
v___y_1943_ = v_a_1674_;
v___y_1944_ = v_a_1675_;
goto v___jp_1938_;
}
v___jp_1677_:
{
lean_object* v___x_1692_; double v___x_1693_; double v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1692_ = lean_io_get_num_heartbeats();
v___x_1693_ = lean_float_of_nat(v___y_1681_);
v___x_1694_ = lean_float_of_nat(v___x_1692_);
v___x_1695_ = lean_box_float(v___x_1693_);
v___x_1696_ = lean_box_float(v___x_1694_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_a_1691_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
v___x_1699_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1679_, v___y_1689_, v___y_1680_, v___y_1686_, v___y_1683_, v___y_1682_, v___y_1687_, v___y_1690_, v___x_1698_, v___y_1678_, v___y_1688_, v___y_1685_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v___y_1686_);
return v___x_1699_;
}
v___jp_1700_:
{
lean_object* v___x_1715_; double v___x_1716_; double v___x_1717_; double v___x_1718_; double v___x_1719_; double v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1715_ = lean_io_mono_nanos_now();
v___x_1716_ = lean_float_of_nat(v___y_1701_);
v___x_1717_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1718_ = lean_float_div(v___x_1716_, v___x_1717_);
v___x_1719_ = lean_float_of_nat(v___x_1715_);
v___x_1720_ = lean_float_div(v___x_1719_, v___x_1717_);
v___x_1721_ = lean_box_float(v___x_1718_);
v___x_1722_ = lean_box_float(v___x_1720_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_a_1714_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
v___x_1725_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1703_, v___y_1712_, v___y_1704_, v___y_1709_, v___y_1706_, v___y_1705_, v___y_1710_, v___y_1713_, v___x_1724_, v___y_1702_, v___y_1711_, v___y_1708_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v___y_1709_);
return v___x_1725_;
}
v___jp_1726_:
{
lean_object* v_fileName_1750_; lean_object* v_fileMap_1751_; lean_object* v_currNamespace_1752_; lean_object* v_openDecls_1753_; lean_object* v_initHeartbeats_1754_; lean_object* v_maxHeartbeats_1755_; lean_object* v_quotContext_1756_; lean_object* v_currMacroScope_1757_; lean_object* v_cancelTk_x3f_1758_; lean_object* v_inheritedTraceOptions_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1811_; 
v_fileName_1750_ = lean_ctor_get(v_toCold_1743_, 0);
v_fileMap_1751_ = lean_ctor_get(v_toCold_1743_, 1);
v_currNamespace_1752_ = lean_ctor_get(v_toCold_1743_, 4);
v_openDecls_1753_ = lean_ctor_get(v_toCold_1743_, 5);
v_initHeartbeats_1754_ = lean_ctor_get(v_toCold_1743_, 6);
v_maxHeartbeats_1755_ = lean_ctor_get(v_toCold_1743_, 7);
v_quotContext_1756_ = lean_ctor_get(v_toCold_1743_, 8);
v_currMacroScope_1757_ = lean_ctor_get(v_toCold_1743_, 9);
v_cancelTk_x3f_1758_ = lean_ctor_get(v_toCold_1743_, 10);
v_inheritedTraceOptions_1759_ = lean_ctor_get(v_toCold_1743_, 11);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_toCold_1743_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; lean_object* v_unused_1813_; 
v_unused_1812_ = lean_ctor_get(v_toCold_1743_, 3);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v_toCold_1743_, 2);
lean_dec(v_unused_1813_);
v___x_1761_ = v_toCold_1743_;
v_isShared_1762_ = v_isSharedCheck_1811_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_inheritedTraceOptions_1759_);
lean_inc(v_cancelTk_x3f_1758_);
lean_inc(v_currMacroScope_1757_);
lean_inc(v_quotContext_1756_);
lean_inc(v_maxHeartbeats_1755_);
lean_inc(v_initHeartbeats_1754_);
lean_inc(v_openDecls_1753_);
lean_inc(v_currNamespace_1752_);
lean_inc(v_fileMap_1751_);
lean_inc(v_fileName_1750_);
lean_dec(v_toCold_1743_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1811_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = l_Lean_maxRecDepth;
v___x_1764_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1742_, v___x_1763_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 3, v___x_1764_);
lean_ctor_set(v___x_1761_, 2, v___y_1742_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_fileName_1750_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_fileMap_1751_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v___y_1742_);
lean_ctor_set(v_reuseFailAlloc_1810_, 3, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1810_, 4, v_currNamespace_1752_);
lean_ctor_set(v_reuseFailAlloc_1810_, 5, v_openDecls_1753_);
lean_ctor_set(v_reuseFailAlloc_1810_, 6, v_initHeartbeats_1754_);
lean_ctor_set(v_reuseFailAlloc_1810_, 7, v_maxHeartbeats_1755_);
lean_ctor_set(v_reuseFailAlloc_1810_, 8, v_quotContext_1756_);
lean_ctor_set(v_reuseFailAlloc_1810_, 9, v_currMacroScope_1757_);
lean_ctor_set(v_reuseFailAlloc_1810_, 10, v_cancelTk_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1810_, 11, v_inheritedTraceOptions_1759_);
v___x_1766_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v_a_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1767_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_currRecDepth_1744_);
lean_ctor_set(v___x_1767_, 2, v_ref_1745_);
lean_ctor_set_uint16(v___x_1767_, sizeof(void*)*3, v___y_1739_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*3 + 2, v_suppressElabErrors_1746_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*3 + 3, v_checkDeprecated_1747_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*3 + 4, v_isRecordingDeps_1748_);
v___x_1768_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1729_, v___y_1727_, v___y_1736_, v___x_1767_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref_known(v___x_1767_, 3);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1769_, v___y_1727_, v___y_1736_, v___y_1737_, v___y_1732_);
lean_dec_ref(v___y_1737_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1773_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1738_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_io_mono_nanos_now();
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1734_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1727_);
v___x_1775_ = lean_apply_5(v___y_1741_, v___y_1727_, v___y_1736_, v___y_1734_, v___y_1732_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 1);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v___y_1701_ = v___x_1774_;
v___y_1702_ = v___y_1727_;
v___y_1703_ = v___y_1728_;
v___y_1704_ = v___y_1730_;
v___y_1705_ = v___y_1731_;
v___y_1706_ = v___y_1733_;
v___y_1707_ = v___y_1732_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1738_;
v___y_1710_ = v___y_1735_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1740_;
v___y_1713_ = v_a_1771_;
v_a_1714_ = v___x_1781_;
goto v___jp_1700_;
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1775_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1775_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 0);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v___y_1701_ = v___x_1774_;
v___y_1702_ = v___y_1727_;
v___y_1703_ = v___y_1728_;
v___y_1704_ = v___y_1730_;
v___y_1705_ = v___y_1731_;
v___y_1706_ = v___y_1733_;
v___y_1707_ = v___y_1732_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1738_;
v___y_1710_ = v___y_1735_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1740_;
v___y_1713_ = v_a_1771_;
v_a_1714_ = v___x_1789_;
goto v___jp_1700_;
}
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1734_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1727_);
v___x_1793_ = lean_apply_5(v___y_1741_, v___y_1727_, v___y_1736_, v___y_1734_, v___y_1732_, lean_box(0));
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 1);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___y_1728_;
v___y_1680_ = v___y_1730_;
v___y_1681_ = v___x_1792_;
v___y_1682_ = v___y_1731_;
v___y_1683_ = v___y_1733_;
v___y_1684_ = v___y_1732_;
v___y_1685_ = v___y_1734_;
v___y_1686_ = v___y_1738_;
v___y_1687_ = v___y_1735_;
v___y_1688_ = v___y_1736_;
v___y_1689_ = v___y_1740_;
v___y_1690_ = v_a_1771_;
v_a_1691_ = v___x_1799_;
goto v___jp_1677_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
v_a_1802_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1793_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1793_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 0);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___y_1728_;
v___y_1680_ = v___y_1730_;
v___y_1681_ = v___x_1792_;
v___y_1682_ = v___y_1731_;
v___y_1683_ = v___y_1733_;
v___y_1684_ = v___y_1732_;
v___y_1685_ = v___y_1734_;
v___y_1686_ = v___y_1738_;
v___y_1687_ = v___y_1735_;
v___y_1688_ = v___y_1736_;
v___y_1689_ = v___y_1740_;
v___y_1690_ = v_a_1771_;
v_a_1691_ = v___x_1807_;
goto v___jp_1677_;
}
}
}
}
}
}
}
v___jp_1814_:
{
lean_object* v_toCold_1833_; lean_object* v_currRecDepth_1834_; lean_object* v_ref_1835_; uint8_t v_suppressElabErrors_1836_; uint8_t v_checkDeprecated_1837_; uint8_t v_isRecordingDeps_1838_; 
v_toCold_1833_ = lean_ctor_get(v___y_1831_, 0);
lean_inc_ref(v_toCold_1833_);
v_currRecDepth_1834_ = lean_ctor_get(v___y_1831_, 1);
lean_inc(v_currRecDepth_1834_);
v_ref_1835_ = lean_ctor_get(v___y_1831_, 2);
lean_inc(v_ref_1835_);
v_suppressElabErrors_1836_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*3 + 2);
v_checkDeprecated_1837_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1838_ = lean_ctor_get_uint8(v___y_1831_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_1831_);
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
v___y_1742_ = v___y_1830_;
v_toCold_1743_ = v_toCold_1833_;
v_currRecDepth_1744_ = v_currRecDepth_1834_;
v_ref_1745_ = v_ref_1835_;
v_suppressElabErrors_1746_ = v_suppressElabErrors_1836_;
v_checkDeprecated_1747_ = v_checkDeprecated_1837_;
v_isRecordingDeps_1748_ = v_isRecordingDeps_1838_;
v___y_1749_ = v___y_1832_;
goto v___jp_1726_;
}
v___jp_1839_:
{
lean_object* v___x_1857_; lean_object* v_env_1858_; lean_object* v_nextMacroScope_1859_; lean_object* v_ngen_1860_; lean_object* v_auxDeclNGen_1861_; lean_object* v_traceState_1862_; lean_object* v_recordedDeps_1863_; lean_object* v_messages_1864_; lean_object* v_infoState_1865_; lean_object* v_snapshotTasks_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1876_; 
v___x_1857_ = lean_st_ref_take(v___y_1845_);
v_env_1858_ = lean_ctor_get(v___x_1857_, 0);
v_nextMacroScope_1859_ = lean_ctor_get(v___x_1857_, 1);
v_ngen_1860_ = lean_ctor_get(v___x_1857_, 2);
v_auxDeclNGen_1861_ = lean_ctor_get(v___x_1857_, 3);
v_traceState_1862_ = lean_ctor_get(v___x_1857_, 4);
v_recordedDeps_1863_ = lean_ctor_get(v___x_1857_, 6);
v_messages_1864_ = lean_ctor_get(v___x_1857_, 7);
v_infoState_1865_ = lean_ctor_get(v___x_1857_, 8);
v_snapshotTasks_1866_ = lean_ctor_get(v___x_1857_, 9);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v___x_1857_, 5);
lean_dec(v_unused_1877_);
v___x_1868_ = v___x_1857_;
v_isShared_1869_ = v_isSharedCheck_1876_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snapshotTasks_1866_);
lean_inc(v_infoState_1865_);
lean_inc(v_messages_1864_);
lean_inc(v_recordedDeps_1863_);
lean_inc(v_traceState_1862_);
lean_inc(v_auxDeclNGen_1861_);
lean_inc(v_ngen_1860_);
lean_inc(v_nextMacroScope_1859_);
lean_inc(v_env_1858_);
lean_dec(v___x_1857_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1876_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1870_ = l_Lean_Kernel_enableDiag(v_env_1858_, v___y_1854_);
v___x_1871_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 5, v___x_1871_);
lean_ctor_set(v___x_1868_, 0, v___x_1870_);
v___x_1873_ = v___x_1868_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_nextMacroScope_1859_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_ngen_1860_);
lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_auxDeclNGen_1861_);
lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_traceState_1862_);
lean_ctor_set(v_reuseFailAlloc_1875_, 5, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1875_, 6, v_recordedDeps_1863_);
lean_ctor_set(v_reuseFailAlloc_1875_, 7, v_messages_1864_);
lean_ctor_set(v_reuseFailAlloc_1875_, 8, v_infoState_1865_);
lean_ctor_set(v_reuseFailAlloc_1875_, 9, v_snapshotTasks_1866_);
v___x_1873_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_st_ref_put(v___y_1845_, v___x_1873_);
lean_inc_ref(v___y_1849_);
lean_inc(v___y_1845_);
v___y_1815_ = v___y_1840_;
v___y_1816_ = v___y_1841_;
v___y_1817_ = v___y_1842_;
v___y_1818_ = v___y_1843_;
v___y_1819_ = v___y_1844_;
v___y_1820_ = v___y_1845_;
v___y_1821_ = v___y_1846_;
v___y_1822_ = v___y_1847_;
v___y_1823_ = v___y_1850_;
v___y_1824_ = v___y_1851_;
v___y_1825_ = v___y_1849_;
v___y_1826_ = v___y_1848_;
v___y_1827_ = v___y_1852_;
v___y_1828_ = v___y_1853_;
v___y_1829_ = v___y_1856_;
v___y_1830_ = v___y_1855_;
v___y_1831_ = v___y_1849_;
v___y_1832_ = v___y_1845_;
goto v___jp_1814_;
}
}
}
v___jp_1878_:
{
if (v___y_1883_ == 0)
{
lean_inc_ref(v___y_1889_);
lean_inc(v___y_1885_);
v___y_1815_ = v___y_1879_;
v___y_1816_ = v___y_1880_;
v___y_1817_ = v___y_1881_;
v___y_1818_ = v___y_1882_;
v___y_1819_ = v___y_1884_;
v___y_1820_ = v___y_1885_;
v___y_1821_ = v___y_1886_;
v___y_1822_ = v___y_1887_;
v___y_1823_ = v___y_1890_;
v___y_1824_ = v___y_1891_;
v___y_1825_ = v___y_1889_;
v___y_1826_ = v___y_1888_;
v___y_1827_ = v___y_1892_;
v___y_1828_ = v___y_1893_;
v___y_1829_ = v___y_1894_;
v___y_1830_ = v___y_1895_;
v___y_1831_ = v___y_1889_;
v___y_1832_ = v___y_1885_;
goto v___jp_1814_;
}
else
{
v___y_1840_ = v___y_1879_;
v___y_1841_ = v___y_1880_;
v___y_1842_ = v___y_1881_;
v___y_1843_ = v___y_1882_;
v___y_1844_ = v___y_1884_;
v___y_1845_ = v___y_1885_;
v___y_1846_ = v___y_1886_;
v___y_1847_ = v___y_1887_;
v___y_1848_ = v___y_1888_;
v___y_1849_ = v___y_1889_;
v___y_1850_ = v___y_1890_;
v___y_1851_ = v___y_1891_;
v___y_1852_ = v___y_1892_;
v___y_1853_ = v___y_1893_;
v___y_1854_ = v___y_1896_;
v___y_1855_ = v___y_1895_;
v___y_1856_ = v___y_1894_;
goto v___jp_1839_;
}
}
v___jp_1897_:
{
lean_object* v___x_1918_; lean_object* v_a_1919_; lean_object* v_ref_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint16_t v___x_1930_; lean_object* v___x_1931_; lean_object* v_env_1932_; uint8_t v___x_1933_; uint16_t v___x_1934_; uint16_t v___x_1935_; uint16_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1918_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1909_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v_ref_1920_ = l_Lean_replaceRef(v___y_1915_, v___y_1915_);
lean_inc(v_ref_1920_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1911_);
v___x_1921_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1921_, 0, v___y_1911_);
lean_ctor_set(v___x_1921_, 1, v___y_1905_);
lean_ctor_set(v___x_1921_, 2, v_ref_1920_);
lean_ctor_set_uint16(v___x_1921_, sizeof(void*)*3, v___y_1906_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*3 + 2, v___y_1900_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*3 + 3, v___y_1904_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*3 + 4, v___y_1910_);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1923_ = 0;
v___x_1924_ = l_Lean_MessageData_ofLevel(v___y_1901_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l_Lean_MessageData_ofLevel(v___y_1908_);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
lean_inc_ref(v___y_1913_);
v___x_1929_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1913_, v___x_1922_, v___x_1923_);
v___x_1930_ = l_Lean_OptionFlags_ofOptions(v___x_1929_);
v___x_1931_ = lean_st_ref_get(v___y_1909_);
v_env_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_ref(v_env_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1932_);
lean_dec_ref(v_env_1932_);
v___x_1934_ = 512;
v___x_1935_ = lean_uint16_land(v___x_1930_, v___x_1934_);
v___x_1936_ = 0;
v___x_1937_ = lean_uint16_dec_eq(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
if (v___y_1903_ == 0)
{
lean_dec(v_ref_1920_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1905_);
v___y_1879_ = v___y_1898_;
v___y_1880_ = v___y_1899_;
v___y_1881_ = v___x_1928_;
v___y_1882_ = v___y_1902_;
v___y_1883_ = v___x_1933_;
v___y_1884_ = v_a_1919_;
v___y_1885_ = v___y_1909_;
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___x_1921_;
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1914_;
v___y_1892_ = v___x_1930_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___y_1917_;
v___y_1895_ = v___x_1929_;
v___y_1896_ = v___y_1903_;
goto v___jp_1878_;
}
else
{
if (v___x_1933_ == 0)
{
lean_dec(v_ref_1920_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1905_);
v___y_1840_ = v___y_1898_;
v___y_1841_ = v___y_1899_;
v___y_1842_ = v___x_1928_;
v___y_1843_ = v___y_1902_;
v___y_1844_ = v_a_1919_;
v___y_1845_ = v___y_1909_;
v___y_1846_ = v___y_1907_;
v___y_1847_ = v___y_1912_;
v___y_1848_ = v___y_1913_;
v___y_1849_ = v___x_1921_;
v___y_1850_ = v___y_1915_;
v___y_1851_ = v___y_1914_;
v___y_1852_ = v___x_1930_;
v___y_1853_ = v___y_1916_;
v___y_1854_ = v___y_1903_;
v___y_1855_ = v___x_1929_;
v___y_1856_ = v___y_1917_;
goto v___jp_1839_;
}
else
{
lean_inc(v___y_1909_);
v___y_1727_ = v___y_1898_;
v___y_1728_ = v___y_1899_;
v___y_1729_ = v___x_1928_;
v___y_1730_ = v___y_1902_;
v___y_1731_ = v_a_1919_;
v___y_1732_ = v___y_1909_;
v___y_1733_ = v___y_1907_;
v___y_1734_ = v___y_1912_;
v___y_1735_ = v___y_1915_;
v___y_1736_ = v___y_1914_;
v___y_1737_ = v___x_1921_;
v___y_1738_ = v___y_1913_;
v___y_1739_ = v___x_1930_;
v___y_1740_ = v___y_1916_;
v___y_1741_ = v___y_1917_;
v___y_1742_ = v___x_1929_;
v_toCold_1743_ = v___y_1911_;
v_currRecDepth_1744_ = v___y_1905_;
v_ref_1745_ = v_ref_1920_;
v_suppressElabErrors_1746_ = v___y_1900_;
v_checkDeprecated_1747_ = v___y_1904_;
v_isRecordingDeps_1748_ = v___y_1910_;
v___y_1749_ = v___y_1909_;
goto v___jp_1726_;
}
}
}
else
{
lean_dec(v_ref_1920_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1905_);
v___y_1879_ = v___y_1898_;
v___y_1880_ = v___y_1899_;
v___y_1881_ = v___x_1928_;
v___y_1882_ = v___y_1902_;
v___y_1883_ = v___x_1933_;
v___y_1884_ = v_a_1919_;
v___y_1885_ = v___y_1909_;
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___x_1921_;
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1914_;
v___y_1892_ = v___x_1930_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___y_1917_;
v___y_1895_ = v___x_1929_;
v___y_1896_ = v___x_1923_;
goto v___jp_1878_;
}
}
v___jp_1938_:
{
lean_object* v_toCold_1945_; lean_object* v_options_1946_; lean_object* v_currRecDepth_1947_; lean_object* v_ref_1948_; uint16_t v_optionFlags_1949_; uint8_t v_suppressElabErrors_1950_; uint8_t v_checkDeprecated_1951_; uint8_t v_isRecordingDeps_1952_; lean_object* v_inheritedTraceOptions_1953_; uint8_t v_hasTrace_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___y_1963_; 
v_toCold_1945_ = lean_ctor_get(v___y_1943_, 0);
v_options_1946_ = lean_ctor_get(v_toCold_1945_, 2);
v_currRecDepth_1947_ = lean_ctor_get(v___y_1943_, 1);
v_ref_1948_ = lean_ctor_get(v___y_1943_, 2);
v_optionFlags_1949_ = lean_ctor_get_uint16(v___y_1943_, sizeof(void*)*3);
v_suppressElabErrors_1950_ = lean_ctor_get_uint8(v___y_1943_, sizeof(void*)*3 + 2);
v_checkDeprecated_1951_ = lean_ctor_get_uint8(v___y_1943_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1952_ = lean_ctor_get_uint8(v___y_1943_, sizeof(void*)*3 + 4);
v_inheritedTraceOptions_1953_ = lean_ctor_get(v_toCold_1945_, 11);
v_hasTrace_1954_ = lean_ctor_get_uint8(v_options_1946_, sizeof(void*)*1);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1957_ = l_Lean_Level_getLevelOffset(v_lhs_1939_);
v___x_1958_ = l_Lean_Level_getLevelOffset(v_rhs_1940_);
v___x_1959_ = lean_level_eq(v___x_1957_, v___x_1958_);
lean_dec(v___x_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = 1;
v___x_1961_ = lean_box(v___x_1959_);
v___x_1962_ = lean_box(v___x_1960_);
lean_inc(v_rhs_1940_);
lean_inc(v_lhs_1939_);
v___y_1963_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1963_, 0, v___x_1961_);
lean_closure_set(v___y_1963_, 1, v_lhs_1939_);
lean_closure_set(v___y_1963_, 2, v_rhs_1940_);
lean_closure_set(v___y_1963_, 3, v___x_1962_);
lean_closure_set(v___y_1963_, 4, v___x_1955_);
lean_closure_set(v___y_1963_, 5, v___x_1956_);
if (v_hasTrace_1954_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v___y_1963_);
v___x_1964_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1959_, v_lhs_1939_, v_rhs_1940_, v___x_1960_, v___x_1955_, v___x_1956_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1965_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1966_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1967_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1953_, v_options_1946_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = l_Lean_trace_profiler;
v___x_1970_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_options_1946_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref(v___y_1963_);
v___x_1971_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1959_, v_lhs_1939_, v_rhs_1940_, v___x_1960_, v___x_1955_, v___x_1956_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v___x_1971_;
}
else
{
lean_inc(v_ref_1948_);
lean_inc(v_currRecDepth_1947_);
lean_inc_ref(v_options_1946_);
lean_inc_ref(v_toCold_1945_);
v___y_1898_ = v___y_1941_;
v___y_1899_ = v___x_1965_;
v___y_1900_ = v_suppressElabErrors_1950_;
v___y_1901_ = v_lhs_1939_;
v___y_1902_ = v___x_1966_;
v___y_1903_ = v_hasTrace_1954_;
v___y_1904_ = v_checkDeprecated_1951_;
v___y_1905_ = v_currRecDepth_1947_;
v___y_1906_ = v_optionFlags_1949_;
v___y_1907_ = v___x_1968_;
v___y_1908_ = v_rhs_1940_;
v___y_1909_ = v___y_1944_;
v___y_1910_ = v_isRecordingDeps_1952_;
v___y_1911_ = v_toCold_1945_;
v___y_1912_ = v___y_1943_;
v___y_1913_ = v_options_1946_;
v___y_1914_ = v___y_1942_;
v___y_1915_ = v_ref_1948_;
v___y_1916_ = v___x_1960_;
v___y_1917_ = v___y_1963_;
goto v___jp_1897_;
}
}
else
{
lean_inc(v_ref_1948_);
lean_inc(v_currRecDepth_1947_);
lean_inc_ref(v_options_1946_);
lean_inc_ref(v_toCold_1945_);
v___y_1898_ = v___y_1941_;
v___y_1899_ = v___x_1965_;
v___y_1900_ = v_suppressElabErrors_1950_;
v___y_1901_ = v_lhs_1939_;
v___y_1902_ = v___x_1966_;
v___y_1903_ = v_hasTrace_1954_;
v___y_1904_ = v_checkDeprecated_1951_;
v___y_1905_ = v_currRecDepth_1947_;
v___y_1906_ = v_optionFlags_1949_;
v___y_1907_ = v___x_1968_;
v___y_1908_ = v_rhs_1940_;
v___y_1909_ = v___y_1944_;
v___y_1910_ = v_isRecordingDeps_1952_;
v___y_1911_ = v_toCold_1945_;
v___y_1912_ = v___y_1943_;
v___y_1913_ = v_options_1946_;
v___y_1914_ = v___y_1942_;
v___y_1915_ = v_ref_1948_;
v___y_1916_ = v___x_1960_;
v___y_1917_ = v___y_1963_;
goto v___jp_1897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = lean_is_level_def_eq(v_x_1975_, v_x_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1983_, lean_object* v_x_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1984_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1991_, v_x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2055_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2056_ = 0;
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2058_ = l_Lean_registerTraceClass(v___x_2055_, v___x_2056_, v___x_2057_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2058_, 1);
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2060_ = 1;
v___x_2061_ = l_Lean_registerTraceClass(v___x_2059_, v___x_2060_, v___x_2057_);
return v___x_2061_;
}
else
{
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2063_;
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
