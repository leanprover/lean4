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
uint8_t v_a_816_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_875_; lean_object* v___y_889_; 
switch(lean_obj_tag(v_u_808_))
{
case 5:
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v_u_808_, 0);
lean_inc(v_a_902_);
v___x_903_ = l_Lean_LMVarId_isReadOnly(v_a_902_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_1000_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_1000_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_1000_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v___x_908_; 
v___x_908_ = lean_unbox(v_a_904_);
lean_dec(v_a_904_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_del_object(v___x_906_);
lean_inc(v_a_902_);
lean_inc(v_v_809_);
v___x_909_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_809_, v_a_902_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_986_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_986_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_986_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_986_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___x_920_; 
v___x_920_ = lean_unbox(v_a_910_);
lean_dec(v_a_910_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_Level_occurs(v_u_808_, v_v_809_);
if (v___x_921_ == 0)
{
lean_object* v_toCold_922_; lean_object* v_options_923_; uint8_t v_hasTrace_924_; 
lean_del_object(v___x_912_);
v_toCold_922_ = lean_ctor_get(v_a_812_, 0);
v_options_923_ = lean_ctor_get(v_toCold_922_, 2);
v_hasTrace_924_ = lean_ctor_get_uint8(v_options_923_, sizeof(void*)*1);
if (v_hasTrace_924_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_875_ = v_a_811_;
goto v___jp_874_;
}
else
{
lean_object* v_inheritedTraceOptions_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_inheritedTraceOptions_925_ = lean_ctor_get(v_toCold_922_, 11);
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_927_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_928_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_925_, v_options_923_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_875_ = v_a_811_;
goto v___jp_874_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc_ref(v_u_808_);
v___x_929_ = l_Lean_MessageData_ofLevel(v_u_808_);
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
lean_inc(v_v_809_);
v___x_932_ = l_Lean_MessageData_ofLevel(v_v_809_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_926_, v___x_933_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref_known(v___x_934_, 1);
v___y_875_ = v_a_811_;
goto v___jp_874_;
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_811_);
lean_dec(v_v_809_);
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
else
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_Level_isMax(v_v_809_);
if (v___x_943_ == 0)
{
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
goto v___jp_914_;
}
else
{
uint8_t v___x_944_; 
v___x_944_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_808_, v_v_809_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_del_object(v___x_912_);
v___x_945_ = l_Lean_Level_mvarId_x21(v_u_808_);
lean_dec_ref_known(v_u_808_, 1);
v___x_946_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_945_, v_v_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_946_, 0);
lean_dec(v_unused_956_);
v___x_948_ = v___x_946_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_dec(v___x_946_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = 1;
v___x_951_ = lean_box(v___x_950_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_946_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_946_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
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
goto v___jp_914_;
}
}
}
}
else
{
lean_object* v_toCold_965_; lean_object* v_options_966_; uint8_t v_hasTrace_967_; 
lean_del_object(v___x_912_);
v_toCold_965_ = lean_ctor_get(v_a_812_, 0);
v_options_966_ = lean_ctor_get(v_toCold_965_, 2);
v_hasTrace_967_ = lean_ctor_get_uint8(v_options_966_, sizeof(void*)*1);
if (v_hasTrace_967_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_889_ = v_a_811_;
goto v___jp_888_;
}
else
{
lean_object* v_inheritedTraceOptions_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_inheritedTraceOptions_968_ = lean_ctor_get(v_toCold_965_, 11);
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_968_, v_options_966_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
v___y_889_ = v_a_811_;
goto v___jp_888_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc(v_v_809_);
v___x_972_ = l_Lean_MessageData_ofLevel(v_v_809_);
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_inc_ref(v_u_808_);
v___x_975_ = l_Lean_MessageData_ofLevel(v_u_808_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_969_, v___x_976_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec_ref(v_a_810_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_dec_ref_known(v___x_977_, 1);
v___y_889_ = v_a_811_;
goto v___jp_888_;
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_811_);
lean_dec(v_v_809_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
v___jp_914_:
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = 2;
v___x_916_ = lean_box(v___x_915_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_916_);
v___x_918_ = v___x_912_;
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
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v_a_987_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_909_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_909_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v___x_995_ = 2;
v___x_996_ = lean_box(v___x_995_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_996_);
v___x_998_ = v___x_906_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref_known(v_u_808_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v_a_1001_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_903_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_903_);
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
goto v___jp_870_;
}
case 2:
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1009_ = lean_ctor_get(v_v_809_, 0);
lean_inc(v_a_1009_);
v_a_1010_ = lean_ctor_get(v_v_809_, 1);
lean_inc(v_a_1010_);
lean_dec_ref_known(v_v_809_, 2);
lean_inc(v_a_813_);
lean_inc_ref(v_a_812_);
lean_inc(v_a_811_);
lean_inc_ref(v_a_810_);
v___x_1011_ = lean_is_level_def_eq(v_u_808_, v_a_1009_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = lean_unbox(v_a_1012_);
if (v___x_1013_ == 0)
{
uint8_t v___x_1014_; 
lean_dec(v_a_1010_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___x_1014_ = lean_unbox(v_a_1012_);
lean_dec(v_a_1012_);
v_a_816_ = v___x_1014_;
goto v___jp_815_;
}
else
{
lean_object* v___x_1015_; 
lean_dec(v_a_1012_);
v___x_1015_ = lean_is_level_def_eq(v_u_808_, v_a_1010_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; uint8_t v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_unbox(v_a_1016_);
lean_dec(v_a_1016_);
v_a_816_ = v___x_1017_;
goto v___jp_815_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1015_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1015_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_1010_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v_a_1026_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1011_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1011_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
case 3:
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v_v_809_, 1);
lean_inc(v_a_1034_);
lean_dec_ref_known(v_v_809_, 2);
v___x_1035_ = lean_is_level_def_eq(v_u_808_, v_a_1034_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1046_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
uint8_t v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_unbox(v_a_1036_);
lean_dec(v_a_1036_);
v___x_1041_ = l_Lean_Bool_toLBool(v___x_1040_);
v___x_1042_ = lean_box(v___x_1041_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1042_);
v___x_1044_ = v___x_1038_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1035_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1035_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
case 1:
{
uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref_known(v_v_809_, 1);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___x_1055_ = 0;
v___x_1056_ = lean_box(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
default: 
{
v___y_825_ = v_a_810_;
v___y_826_ = v_a_811_;
v___y_827_ = v_a_812_;
v___y_828_ = v_a_813_;
goto v___jp_824_;
}
}
}
case 1:
{
lean_object* v_a_1058_; 
v_a_1058_ = lean_ctor_get(v_u_808_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v_u_808_, 1);
if (lean_obj_tag(v_v_809_) == 5)
{
lean_dec_ref_known(v_v_809_, 1);
lean_dec(v_a_1058_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
goto v___jp_870_;
}
else
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Lean_Level_isParam(v_v_809_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Level_isMVar(v_a_1058_);
if (v___x_1101_ == 0)
{
goto v___jp_1059_;
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = l_Lean_Level_occurs(v_a_1058_, v_v_809_);
if (v___x_1102_ == 0)
{
goto v___jp_1059_;
}
else
{
uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_a_1058_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v___x_1103_ = 2;
v___x_1104_ = lean_box(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
else
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_a_1058_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_v_809_);
v___x_1106_ = 0;
v___x_1107_ = lean_box(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
v___jp_1059_:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Meta_decLevel_x3f(v_v_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1091_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1091_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1091_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
if (lean_obj_tag(v_a_1061_) == 0)
{
uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_dec(v_a_1058_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v___x_1065_ = 2;
v___x_1066_ = lean_box(v___x_1065_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1071_; 
lean_del_object(v___x_1063_);
v_val_1070_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v_a_1061_, 1);
v___x_1071_ = lean_is_level_def_eq(v_a_1058_, v_val_1070_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1082_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1082_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1082_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
uint8_t v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1076_ = lean_unbox(v_a_1072_);
lean_dec(v_a_1072_);
v___x_1077_ = l_Lean_Bool_toLBool(v___x_1076_);
v___x_1078_ = lean_box(v___x_1077_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1078_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1071_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1071_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1058_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
v_a_1092_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1060_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1060_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
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
goto v___jp_870_;
}
else
{
v___y_825_ = v_a_810_;
v___y_826_ = v_a_811_;
v___y_827_ = v_a_812_;
v___y_828_ = v_a_813_;
goto v___jp_824_;
}
}
}
v___jp_815_:
{
uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = l_Lean_Bool_toLBool(v_a_816_);
v___x_818_ = lean_box(v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
v___jp_820_:
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = 2;
v___x_822_ = lean_box(v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
v___jp_824_:
{
uint8_t v_univApprox_829_; 
v_univApprox_829_ = lean_ctor_get_uint8(v___y_825_, sizeof(void*)*7 + 1);
if (v_univApprox_829_ == 0)
{
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_v_809_);
lean_dec(v_u_808_);
goto v___jp_820_;
}
else
{
lean_object* v___x_830_; 
lean_inc(v_v_809_);
lean_inc(v_u_808_);
v___x_830_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_808_, v_v_809_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_861_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_861_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_861_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_861_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
uint8_t v___x_835_; 
v___x_835_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_del_object(v___x_833_);
v___x_836_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_808_, v_v_809_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_847_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; 
v___x_841_ = lean_unbox(v_a_837_);
lean_dec(v_a_837_);
if (v___x_841_ == 0)
{
lean_del_object(v___x_839_);
goto v___jp_820_;
}
else
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = 1;
v___x_843_ = lean_box(v___x_842_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_843_);
v___x_845_ = v___x_839_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_836_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_836_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_v_809_);
lean_dec(v_u_808_);
v___x_856_ = 1;
v___x_857_ = lean_box(v___x_856_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_857_);
v___x_859_ = v___x_833_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_v_809_);
lean_dec(v_u_808_);
v_a_862_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_830_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_830_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
v___jp_870_:
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = 2;
v___x_872_ = lean_box(v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
v___jp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_886_; 
v___x_876_ = l_Lean_Level_mvarId_x21(v_u_808_);
lean_dec(v_u_808_);
v___x_877_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_876_, v_v_809_, v___y_875_);
lean_dec(v___y_875_);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_887_);
v___x_879_ = v___x_877_;
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
else
{
lean_dec(v___x_877_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = 1;
v___x_882_ = lean_box(v___x_881_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
v___jp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_900_; 
v___x_890_ = l_Lean_Level_mvarId_x21(v_v_809_);
lean_dec(v_v_809_);
v___x_891_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_890_, v_u_808_, v___y_889_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1109_, lean_object* v_v_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1109_, v_v_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v_mctx_1121_; lean_object* v___x_1122_; lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1125_; lean_object* v_cache_1126_; lean_object* v_zetaDeltaFVarIds_1127_; lean_object* v_postponed_1128_; lean_object* v_diag_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1138_; 
v___x_1120_ = lean_st_ref_get(v___y_1118_);
v_mctx_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc_ref(v_mctx_1121_);
lean_dec(v___x_1120_);
v___x_1122_ = lean_instantiate_level_mvars(v_mctx_1121_, v_l_1117_);
v_fst_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_fst_1123_);
v_snd_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_snd_1124_);
lean_dec_ref(v___x_1122_);
v___x_1125_ = lean_st_ref_take(v___y_1118_);
v_cache_1126_ = lean_ctor_get(v___x_1125_, 1);
v_zetaDeltaFVarIds_1127_ = lean_ctor_get(v___x_1125_, 2);
v_postponed_1128_ = lean_ctor_get(v___x_1125_, 3);
v_diag_1129_ = lean_ctor_get(v___x_1125_, 4);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1139_);
v___x_1131_ = v___x_1125_;
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_diag_1129_);
lean_inc(v_postponed_1128_);
lean_inc(v_zetaDeltaFVarIds_1127_);
lean_inc(v_cache_1126_);
lean_dec(v___x_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v_fst_1123_);
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_fst_1123_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_cache_1126_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_zetaDeltaFVarIds_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_postponed_1128_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_diag_1129_);
v___x_1134_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_st_ref_put(v___y_1118_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_snd_1124_);
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1140_, v___y_1141_);
lean_dec(v___y_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1144_, v___y_1146_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1157_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(32u);
v___x_1159_ = lean_mk_empty_array_with_capacity(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1161_ = ((size_t)5ULL);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_unsigned_to_nat(32u);
v___x_1164_ = lean_mk_empty_array_with_capacity(v___x_1163_);
v___x_1165_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___x_1164_);
lean_ctor_set(v___x_1166_, 2, v___x_1162_);
lean_ctor_set(v___x_1166_, 3, v___x_1162_);
lean_ctor_set_usize(v___x_1166_, 4, v___x_1161_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_traceState_1170_; lean_object* v_traces_1171_; lean_object* v___x_1172_; lean_object* v_traceState_1173_; lean_object* v_env_1174_; lean_object* v_nextMacroScope_1175_; lean_object* v_ngen_1176_; lean_object* v_auxDeclNGen_1177_; lean_object* v_cache_1178_; lean_object* v_recordedDeps_1179_; lean_object* v_messages_1180_; lean_object* v_infoState_1181_; lean_object* v_snapshotTasks_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1201_; 
v___x_1169_ = lean_st_ref_get(v___y_1167_);
v_traceState_1170_ = lean_ctor_get(v___x_1169_, 4);
lean_inc_ref(v_traceState_1170_);
lean_dec(v___x_1169_);
v_traces_1171_ = lean_ctor_get(v_traceState_1170_, 0);
lean_inc_ref(v_traces_1171_);
lean_dec_ref(v_traceState_1170_);
v___x_1172_ = lean_st_ref_take(v___y_1167_);
v_traceState_1173_ = lean_ctor_get(v___x_1172_, 4);
v_env_1174_ = lean_ctor_get(v___x_1172_, 0);
v_nextMacroScope_1175_ = lean_ctor_get(v___x_1172_, 1);
v_ngen_1176_ = lean_ctor_get(v___x_1172_, 2);
v_auxDeclNGen_1177_ = lean_ctor_get(v___x_1172_, 3);
v_cache_1178_ = lean_ctor_get(v___x_1172_, 5);
v_recordedDeps_1179_ = lean_ctor_get(v___x_1172_, 6);
v_messages_1180_ = lean_ctor_get(v___x_1172_, 7);
v_infoState_1181_ = lean_ctor_get(v___x_1172_, 8);
v_snapshotTasks_1182_ = lean_ctor_get(v___x_1172_, 9);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1184_ = v___x_1172_;
v_isShared_1185_ = v_isSharedCheck_1201_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_snapshotTasks_1182_);
lean_inc(v_infoState_1181_);
lean_inc(v_messages_1180_);
lean_inc(v_recordedDeps_1179_);
lean_inc(v_cache_1178_);
lean_inc(v_traceState_1173_);
lean_inc(v_auxDeclNGen_1177_);
lean_inc(v_ngen_1176_);
lean_inc(v_nextMacroScope_1175_);
lean_inc(v_env_1174_);
lean_dec(v___x_1172_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1201_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
uint64_t v_tid_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1199_; 
v_tid_1186_ = lean_ctor_get_uint64(v_traceState_1173_, sizeof(void*)*1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_traceState_1173_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_traceState_1173_, 0);
lean_dec(v_unused_1200_);
v___x_1188_ = v_traceState_1173_;
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_traceState_1173_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1190_);
lean_ctor_set_uint64(v_reuseFailAlloc_1198_, sizeof(void*)*1, v_tid_1186_);
v___x_1192_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 4, v___x_1192_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_env_1174_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_nextMacroScope_1175_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_ngen_1176_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_auxDeclNGen_1177_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v_cache_1178_);
lean_ctor_set(v_reuseFailAlloc_1197_, 6, v_recordedDeps_1179_);
lean_ctor_set(v_reuseFailAlloc_1197_, 7, v_messages_1180_);
lean_ctor_set(v_reuseFailAlloc_1197_, 8, v_infoState_1181_);
lean_ctor_set(v_reuseFailAlloc_1197_, 9, v_snapshotTasks_1182_);
v___x_1194_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_st_ref_put(v___y_1167_, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_traces_1171_);
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1202_);
lean_dec(v___y_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1217_, lean_object* v_k_1218_, uint8_t v_v_1219_){
_start:
{
lean_object* v_map_1220_; uint8_t v_hasTrace_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1235_; 
v_map_1220_ = lean_ctor_get(v_o_1217_, 0);
v_hasTrace_1221_ = lean_ctor_get_uint8(v_o_1217_, sizeof(void*)*1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_o_1217_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1223_ = v_o_1217_;
v_isShared_1224_ = v_isSharedCheck_1235_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_map_1220_);
lean_dec(v_o_1217_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1235_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1225_, 0, v_v_1219_);
lean_inc(v_k_1218_);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1218_, v___x_1225_, v_map_1220_);
if (v_hasTrace_1221_ == 0)
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1230_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1228_ = l_Lean_Name_isPrefixOf(v___x_1227_, v_k_1218_);
lean_dec(v_k_1218_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1230_ = v___x_1223_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1226_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_ctor_set_uint8(v___x_1230_, sizeof(void*)*1, v___x_1228_);
return v___x_1230_;
}
}
else
{
lean_object* v___x_1233_; 
lean_dec(v_k_1218_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1233_ = v___x_1223_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*1, v_hasTrace_1221_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1236_, lean_object* v_k_1237_, lean_object* v_v_1238_){
_start:
{
uint8_t v_v_boxed_1239_; lean_object* v_res_1240_; 
v_v_boxed_1239_ = lean_unbox(v_v_1238_);
v_res_1240_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1236_, v_k_1237_, v_v_boxed_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1241_, lean_object* v_opt_1242_){
_start:
{
lean_object* v_name_1243_; lean_object* v_defValue_1244_; lean_object* v_map_1245_; lean_object* v___x_1246_; 
v_name_1243_ = lean_ctor_get(v_opt_1242_, 0);
v_defValue_1244_ = lean_ctor_get(v_opt_1242_, 1);
v_map_1245_ = lean_ctor_get(v_opts_1241_, 0);
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1245_, v_name_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_inc(v_defValue_1244_);
return v_defValue_1244_;
}
else
{
lean_object* v_val_1247_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v___x_1246_, 1);
if (lean_obj_tag(v_val_1247_) == 3)
{
lean_object* v_v_1248_; 
v_v_1248_ = lean_ctor_get(v_val_1247_, 0);
lean_inc(v_v_1248_);
lean_dec_ref_known(v_val_1247_, 1);
return v_v_1248_;
}
else
{
lean_dec(v_val_1247_);
lean_inc(v_defValue_1244_);
return v_defValue_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1249_, lean_object* v_opt_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1249_, v_opt_1250_);
lean_dec_ref(v_opt_1250_);
lean_dec_ref(v_opts_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1252_, lean_object* v_opt_1253_){
_start:
{
lean_object* v_name_1254_; lean_object* v_defValue_1255_; lean_object* v_map_1256_; lean_object* v___x_1257_; 
v_name_1254_ = lean_ctor_get(v_opt_1253_, 0);
v_defValue_1255_ = lean_ctor_get(v_opt_1253_, 1);
v_map_1256_ = lean_ctor_get(v_opts_1252_, 0);
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1256_, v_name_1254_);
if (lean_obj_tag(v___x_1257_) == 0)
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_unbox(v_defValue_1255_);
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; 
v_val_1259_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1257_, 1);
if (lean_obj_tag(v_val_1259_) == 1)
{
uint8_t v_v_1260_; 
v_v_1260_ = lean_ctor_get_uint8(v_val_1259_, 0);
lean_dec_ref_known(v_val_1259_, 0);
return v_v_1260_;
}
else
{
uint8_t v___x_1261_; 
lean_dec(v_val_1259_);
v___x_1261_ = lean_unbox(v_defValue_1255_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1262_, lean_object* v_opt_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1262_, v_opt_1263_);
lean_dec_ref(v_opt_1263_);
lean_dec_ref(v_opts_1262_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1266_, lean_object* v_lhs_1267_, lean_object* v_rhs_1268_, uint8_t v___x_1269_, lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
if (v___x_1266_ == 0)
{
lean_object* v___x_1296_; lean_object* v_a_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_a_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
lean_inc(v_lhs_1267_);
v___x_1296_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1267_, v___y_1273_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = l_Lean_Level_normalize(v_a_1297_);
lean_dec(v_a_1297_);
lean_inc(v_rhs_1268_);
v___x_1299_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1268_, v___y_1273_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = l_Lean_Level_normalize(v_a_1300_);
lean_dec(v_a_1300_);
v___x_1302_ = lean_level_eq(v_lhs_1267_, v___x_1298_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
v___x_1303_ = lean_is_level_def_eq(v___x_1298_, v___x_1301_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1303_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_level_eq(v_rhs_1268_, v___x_1301_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
v___x_1305_ = lean_is_level_def_eq(v___x_1298_, v___x_1301_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; 
lean_dec(v___x_1301_);
lean_dec(v___x_1298_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v_rhs_1268_);
lean_inc(v_lhs_1267_);
v___x_1306_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1267_, v_rhs_1268_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1393_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1393_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1393_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
uint8_t v___x_1311_; uint8_t v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = 2;
v___x_1312_ = lean_unbox(v_a_1307_);
v___x_1313_ = l_Lean_instBEqLBool_beq(v___x_1312_, v___x_1311_);
if (v___x_1313_ == 0)
{
uint8_t v___x_1314_; uint8_t v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1314_ = 1;
v___x_1315_ = lean_unbox(v_a_1307_);
lean_dec(v_a_1307_);
v___x_1316_ = l_Lean_instBEqLBool_beq(v___x_1315_, v___x_1314_);
v___x_1317_ = lean_box(v___x_1316_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1317_);
v___x_1319_ = v___x_1309_;
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
lean_object* v___x_1321_; 
lean_del_object(v___x_1309_);
lean_dec(v_a_1307_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v_lhs_1267_);
lean_inc(v_rhs_1268_);
v___x_1321_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1268_, v_lhs_1267_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1384_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1384_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1384_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_unbox(v_a_1322_);
v___x_1327_ = l_Lean_instBEqLBool_beq(v___x_1326_, v___x_1311_);
if (v___x_1327_ == 0)
{
uint8_t v___x_1328_; uint8_t v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1328_ = 1;
v___x_1329_ = lean_unbox(v_a_1322_);
lean_dec(v_a_1322_);
v___x_1330_ = l_Lean_instBEqLBool_beq(v___x_1329_, v___x_1328_);
v___x_1331_ = lean_box(v___x_1330_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1331_);
v___x_1333_ = v___x_1324_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v___x_1335_; 
lean_del_object(v___x_1324_);
lean_dec(v_a_1322_);
lean_inc(v_lhs_1267_);
v___x_1335_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1267_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; uint8_t v___x_1337_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_inc(v_rhs_1268_);
v___x_1338_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1268_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1383_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1383_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1383_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_unbox(v_a_1339_);
lean_dec(v_a_1339_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; uint8_t v_isDefEqStuckEx_1372_; 
v___x_1371_ = l_Lean_Meta_Context_config(v___y_1272_);
v_isDefEqStuckEx_1372_ = lean_ctor_get_uint8(v___x_1371_, 4);
lean_dec_ref(v___x_1371_);
if (v_isDefEqStuckEx_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1373_ = lean_box(v___x_1266_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1373_);
v___x_1375_ = v___x_1341_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_Level_isMVar(v_lhs_1267_);
if (v___x_1377_ == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = l_Lean_Level_isMVar(v_rhs_1268_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1379_ = lean_box(v___x_1378_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1379_);
v___x_1381_ = v___x_1341_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_del_object(v___x_1341_);
goto v___jp_1343_;
}
}
else
{
lean_del_object(v___x_1341_);
goto v___jp_1343_;
}
}
}
else
{
lean_del_object(v___x_1341_);
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
goto v___jp_1277_;
}
v___jp_1343_:
{
lean_object* v_toCold_1344_; lean_object* v_options_1345_; uint8_t v_hasTrace_1346_; 
v_toCold_1344_ = lean_ctor_get(v___y_1274_, 0);
v_options_1345_ = lean_ctor_get(v_toCold_1344_, 2);
v_hasTrace_1346_ = lean_ctor_get_uint8(v_options_1345_, sizeof(void*)*1);
if (v_hasTrace_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1347_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1347_;
}
else
{
lean_object* v_inheritedTraceOptions_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_inheritedTraceOptions_1348_ = lean_ctor_get(v_toCold_1344_, 11);
v___x_1349_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1350_ = l_Lean_Name_mkStr3(v___x_1270_, v___x_1271_, v___x_1349_);
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1350_);
v___x_1352_ = l_Lean_Name_append(v___x_1351_, v___x_1350_);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1348_, v_options_1345_, v___x_1352_);
lean_dec(v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec(v___x_1350_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v___x_1354_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1355_ = l_Lean_MessageData_ofLevel(v_lhs_1267_);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_MessageData_ofLevel(v_rhs_1268_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1350_, v___x_1359_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1361_; 
lean_dec_ref_known(v___x_1360_, 1);
v___x_1361_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1360_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
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
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
return v___x_1338_;
}
}
else
{
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
goto v___jp_1277_;
}
}
else
{
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v_a_1385_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1321_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1321_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec(v_rhs_1268_);
lean_dec(v_lhs_1267_);
v_a_1394_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1306_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1306_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1270_);
v___x_1402_ = l_Lean_Level_getOffset(v_lhs_1267_);
lean_dec(v_lhs_1267_);
v___x_1403_ = l_Lean_Level_getOffset(v_rhs_1268_);
lean_dec(v_rhs_1268_);
v___x_1404_ = lean_nat_dec_eq(v___x_1402_, v___x_1403_);
lean_dec(v___x_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(v___x_1404_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
v___jp_1277_:
{
lean_object* v___x_1278_; 
v___x_1278_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1267_, v_rhs_1268_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1278_, 0);
lean_dec(v_unused_1287_);
v___x_1280_ = v___x_1278_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_dec(v___x_1278_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(v___x_1269_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1278_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1278_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1407_, lean_object* v_lhs_1408_, lean_object* v_rhs_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v___x_13525__boxed_1418_; uint8_t v___x_13526__boxed_1419_; lean_object* v_res_1420_; 
v___x_13525__boxed_1418_ = lean_unbox(v___x_1407_);
v___x_13526__boxed_1419_ = lean_unbox(v___x_1410_);
v_res_1420_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13525__boxed_1418_, v_lhs_1408_, v_rhs_1409_, v___x_13526__boxed_1419_, v___x_1411_, v___x_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1421_){
_start:
{
if (lean_obj_tag(v_e_1421_) == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = 2;
return v___x_1422_;
}
else
{
lean_object* v_a_1423_; uint8_t v___x_1424_; 
v_a_1423_ = lean_ctor_get(v_e_1421_, 0);
v___x_1424_ = lean_unbox(v_a_1423_);
if (v___x_1424_ == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = 1;
return v___x_1425_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1427_);
lean_dec_ref(v_e_1427_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v_x_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v_x_1430_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v_x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 1);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v_x_1430_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1430_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v_x_1430_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v_x_1430_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 0);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1451_, size_t v_i_1452_, lean_object* v_bs_1453_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_lt(v_i_1452_, v_sz_1451_);
if (v___x_1454_ == 0)
{
return v_bs_1453_;
}
else
{
lean_object* v_v_1455_; lean_object* v_msg_1456_; lean_object* v___x_1457_; lean_object* v_bs_x27_1458_; size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v_v_1455_ = lean_array_uget_borrowed(v_bs_1453_, v_i_1452_);
v_msg_1456_ = lean_ctor_get(v_v_1455_, 1);
lean_inc_ref(v_msg_1456_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v_bs_x27_1458_ = lean_array_uset(v_bs_1453_, v_i_1452_, v___x_1457_);
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_add(v_i_1452_, v___x_1459_);
v___x_1461_ = lean_array_uset(v_bs_x27_1458_, v_i_1452_, v_msg_1456_);
v_i_1452_ = v___x_1460_;
v_bs_1453_ = v___x_1461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1463_, lean_object* v_i_1464_, lean_object* v_bs_1465_){
_start:
{
size_t v_sz_boxed_1466_; size_t v_i_boxed_1467_; lean_object* v_res_1468_; 
v_sz_boxed_1466_ = lean_unbox_usize(v_sz_1463_);
lean_dec(v_sz_1463_);
v_i_boxed_1467_ = lean_unbox_usize(v_i_1464_);
lean_dec(v_i_1464_);
v_res_1468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1466_, v_i_boxed_1467_, v_bs_1465_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1469_, lean_object* v_data_1470_, lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_toCold_1478_; lean_object* v_currRecDepth_1479_; lean_object* v_ref_1480_; uint16_t v_optionFlags_1481_; uint8_t v_suppressElabErrors_1482_; uint8_t v_isRecordingDeps_1483_; lean_object* v_ref_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_traceState_1487_; lean_object* v_traces_1488_; lean_object* v___x_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_1492_; lean_object* v_msg_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1533_; 
v_toCold_1478_ = lean_ctor_get(v___y_1475_, 0);
v_currRecDepth_1479_ = lean_ctor_get(v___y_1475_, 1);
v_ref_1480_ = lean_ctor_get(v___y_1475_, 2);
v_optionFlags_1481_ = lean_ctor_get_uint16(v___y_1475_, sizeof(void*)*3);
v_suppressElabErrors_1482_ = lean_ctor_get_uint8(v___y_1475_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1483_ = lean_ctor_get_uint8(v___y_1475_, sizeof(void*)*3 + 3);
v_ref_1484_ = l_Lean_replaceRef(v_ref_1471_, v_ref_1480_);
lean_inc(v_currRecDepth_1479_);
lean_inc_ref(v_toCold_1478_);
v___x_1485_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1485_, 0, v_toCold_1478_);
lean_ctor_set(v___x_1485_, 1, v_currRecDepth_1479_);
lean_ctor_set(v___x_1485_, 2, v_ref_1484_);
lean_ctor_set_uint16(v___x_1485_, sizeof(void*)*3, v_optionFlags_1481_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 2, v_suppressElabErrors_1482_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 3, v_isRecordingDeps_1483_);
v___x_1486_ = lean_st_ref_get(v___y_1476_);
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
lean_ctor_set(v_msg_1493_, 0, v_data_1470_);
lean_ctor_set(v_msg_1493_, 1, v_msg_1472_);
lean_ctor_set(v_msg_1493_, 2, v___x_1492_);
v___x_1494_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1493_, v___y_1473_, v___y_1474_, v___x_1485_, v___y_1476_);
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
v___x_1499_ = lean_st_ref_take(v___y_1476_);
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
lean_ctor_set(v___x_1518_, 0, v_ref_1471_);
lean_ctor_set(v___x_1518_, 1, v_a_1495_);
v___x_1519_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1469_, v___x_1518_);
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
v___x_1524_ = lean_st_ref_put(v___y_1476_, v___x_1523_);
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
uint8_t v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v_a_1691_; uint8_t v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; uint8_t v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v_a_1714_; lean_object* v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; uint16_t v___y_1739_; uint8_t v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v_toCold_1743_; lean_object* v_currRecDepth_1744_; lean_object* v_ref_1745_; uint8_t v_suppressElabErrors_1746_; uint8_t v_isRecordingDeps_1747_; lean_object* v___y_1748_; lean_object* v___y_1814_; uint8_t v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint16_t v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint16_t v___y_1850_; uint8_t v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1877_; uint8_t v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; uint16_t v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; uint8_t v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; uint8_t v___y_1899_; lean_object* v___y_1900_; uint8_t v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint16_t v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_lhs_1936_; lean_object* v_rhs_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; 
if (lean_obj_tag(v_x_1670_) == 1)
{
if (lean_obj_tag(v_x_1671_) == 1)
{
lean_object* v_a_1968_; lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v_x_1670_, 1);
v_a_1969_ = lean_ctor_get(v_x_1671_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v_x_1671_, 1);
v___x_1970_ = lean_is_level_def_eq(v_a_1968_, v_a_1969_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1970_;
}
else
{
v_lhs_1936_ = v_x_1670_;
v_rhs_1937_ = v_x_1671_;
v___y_1938_ = v_a_1672_;
v___y_1939_ = v_a_1673_;
v___y_1940_ = v_a_1674_;
v___y_1941_ = v_a_1675_;
goto v___jp_1935_;
}
}
else
{
v_lhs_1936_ = v_x_1670_;
v_rhs_1937_ = v_x_1671_;
v___y_1938_ = v_a_1672_;
v___y_1939_ = v_a_1673_;
v___y_1940_ = v_a_1674_;
v___y_1941_ = v_a_1675_;
goto v___jp_1935_;
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
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1689_);
v___x_1699_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1689_, v___y_1688_, v___y_1687_, v___y_1682_, v___y_1678_, v___y_1684_, v___y_1680_, v___y_1690_, v___x_1698_, v___y_1683_, v___y_1685_, v___y_1679_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v___x_1699_;
}
v___jp_1700_:
{
lean_object* v___x_1715_; double v___x_1716_; double v___x_1717_; double v___x_1718_; double v___x_1719_; double v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1715_ = lean_io_mono_nanos_now();
v___x_1716_ = lean_float_of_nat(v___y_1702_);
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
lean_inc_ref(v___y_1710_);
lean_inc(v___y_1712_);
v___x_1725_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1712_, v___y_1711_, v___y_1710_, v___y_1705_, v___y_1701_, v___y_1707_, v___y_1704_, v___y_1713_, v___x_1724_, v___y_1706_, v___y_1708_, v___y_1703_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v___x_1725_;
}
v___jp_1726_:
{
lean_object* v_fileName_1749_; lean_object* v_fileMap_1750_; lean_object* v_currNamespace_1751_; lean_object* v_openDecls_1752_; lean_object* v_initHeartbeats_1753_; lean_object* v_maxHeartbeats_1754_; lean_object* v_quotContext_1755_; lean_object* v_currMacroScope_1756_; lean_object* v_cancelTk_x3f_1757_; lean_object* v_inheritedTraceOptions_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1810_; 
v_fileName_1749_ = lean_ctor_get(v_toCold_1743_, 0);
v_fileMap_1750_ = lean_ctor_get(v_toCold_1743_, 1);
v_currNamespace_1751_ = lean_ctor_get(v_toCold_1743_, 4);
v_openDecls_1752_ = lean_ctor_get(v_toCold_1743_, 5);
v_initHeartbeats_1753_ = lean_ctor_get(v_toCold_1743_, 6);
v_maxHeartbeats_1754_ = lean_ctor_get(v_toCold_1743_, 7);
v_quotContext_1755_ = lean_ctor_get(v_toCold_1743_, 8);
v_currMacroScope_1756_ = lean_ctor_get(v_toCold_1743_, 9);
v_cancelTk_x3f_1757_ = lean_ctor_get(v_toCold_1743_, 10);
v_inheritedTraceOptions_1758_ = lean_ctor_get(v_toCold_1743_, 11);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_toCold_1743_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; lean_object* v_unused_1812_; 
v_unused_1811_ = lean_ctor_get(v_toCold_1743_, 3);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_toCold_1743_, 2);
lean_dec(v_unused_1812_);
v___x_1760_ = v_toCold_1743_;
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
lean_dec(v_toCold_1743_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1810_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = l_Lean_maxRecDepth;
v___x_1763_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1742_, v___x_1762_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 3, v___x_1763_);
lean_ctor_set(v___x_1760_, 2, v___y_1742_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_fileName_1749_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_fileMap_1750_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v___y_1742_);
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
v___x_1766_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v_currRecDepth_1744_);
lean_ctor_set(v___x_1766_, 2, v_ref_1745_);
lean_ctor_set_uint16(v___x_1766_, sizeof(void*)*3, v___y_1739_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*3 + 2, v_suppressElabErrors_1746_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*3 + 3, v_isRecordingDeps_1747_);
v___x_1767_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1727_, v___y_1734_, v___y_1736_, v___x_1766_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref_known(v___x_1766_, 3);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1768_, v___y_1734_, v___y_1736_, v___y_1731_, v___y_1737_);
lean_dec_ref(v___y_1731_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1772_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1733_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_io_mono_nanos_now();
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1734_);
v___x_1774_ = lean_apply_5(v___y_1732_, v___y_1734_, v___y_1736_, v___y_1729_, v___y_1737_, lean_box(0));
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
v___y_1701_ = v___y_1728_;
v___y_1702_ = v___x_1773_;
v___y_1703_ = v___y_1729_;
v___y_1704_ = v___y_1730_;
v___y_1705_ = v___y_1733_;
v___y_1706_ = v___y_1734_;
v___y_1707_ = v___y_1735_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1737_;
v___y_1710_ = v___y_1738_;
v___y_1711_ = v___y_1740_;
v___y_1712_ = v___y_1741_;
v___y_1713_ = v_a_1770_;
v_a_1714_ = v___x_1780_;
goto v___jp_1700_;
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
v___y_1701_ = v___y_1728_;
v___y_1702_ = v___x_1773_;
v___y_1703_ = v___y_1729_;
v___y_1704_ = v___y_1730_;
v___y_1705_ = v___y_1733_;
v___y_1706_ = v___y_1734_;
v___y_1707_ = v___y_1735_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1737_;
v___y_1710_ = v___y_1738_;
v___y_1711_ = v___y_1740_;
v___y_1712_ = v___y_1741_;
v___y_1713_ = v_a_1770_;
v_a_1714_ = v___x_1788_;
goto v___jp_1700_;
}
}
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1734_);
v___x_1792_ = lean_apply_5(v___y_1732_, v___y_1734_, v___y_1736_, v___y_1729_, v___y_1737_, lean_box(0));
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
v___y_1678_ = v___y_1728_;
v___y_1679_ = v___y_1729_;
v___y_1680_ = v___y_1730_;
v___y_1681_ = v___x_1791_;
v___y_1682_ = v___y_1733_;
v___y_1683_ = v___y_1734_;
v___y_1684_ = v___y_1735_;
v___y_1685_ = v___y_1736_;
v___y_1686_ = v___y_1737_;
v___y_1687_ = v___y_1738_;
v___y_1688_ = v___y_1740_;
v___y_1689_ = v___y_1741_;
v___y_1690_ = v_a_1770_;
v_a_1691_ = v___x_1798_;
goto v___jp_1677_;
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
v___y_1678_ = v___y_1728_;
v___y_1679_ = v___y_1729_;
v___y_1680_ = v___y_1730_;
v___y_1681_ = v___x_1791_;
v___y_1682_ = v___y_1733_;
v___y_1683_ = v___y_1734_;
v___y_1684_ = v___y_1735_;
v___y_1685_ = v___y_1736_;
v___y_1686_ = v___y_1737_;
v___y_1687_ = v___y_1738_;
v___y_1688_ = v___y_1740_;
v___y_1689_ = v___y_1741_;
v___y_1690_ = v_a_1770_;
v_a_1691_ = v___x_1806_;
goto v___jp_1677_;
}
}
}
}
}
}
}
v___jp_1813_:
{
lean_object* v_toCold_1832_; lean_object* v_currRecDepth_1833_; lean_object* v_ref_1834_; uint8_t v_suppressElabErrors_1835_; uint8_t v_isRecordingDeps_1836_; 
v_toCold_1832_ = lean_ctor_get(v___y_1830_, 0);
lean_inc_ref(v_toCold_1832_);
v_currRecDepth_1833_ = lean_ctor_get(v___y_1830_, 1);
lean_inc(v_currRecDepth_1833_);
v_ref_1834_ = lean_ctor_get(v___y_1830_, 2);
lean_inc(v_ref_1834_);
v_suppressElabErrors_1835_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1836_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_1830_);
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
v___y_1742_ = v___y_1829_;
v_toCold_1743_ = v_toCold_1832_;
v_currRecDepth_1744_ = v_currRecDepth_1833_;
v_ref_1745_ = v_ref_1834_;
v_suppressElabErrors_1746_ = v_suppressElabErrors_1835_;
v_isRecordingDeps_1747_ = v_isRecordingDeps_1836_;
v___y_1748_ = v___y_1831_;
goto v___jp_1726_;
}
v___jp_1837_:
{
lean_object* v___x_1855_; lean_object* v_env_1856_; lean_object* v_nextMacroScope_1857_; lean_object* v_ngen_1858_; lean_object* v_auxDeclNGen_1859_; lean_object* v_traceState_1860_; lean_object* v_recordedDeps_1861_; lean_object* v_messages_1862_; lean_object* v_infoState_1863_; lean_object* v_snapshotTasks_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1874_; 
v___x_1855_ = lean_st_ref_take(v___y_1848_);
v_env_1856_ = lean_ctor_get(v___x_1855_, 0);
v_nextMacroScope_1857_ = lean_ctor_get(v___x_1855_, 1);
v_ngen_1858_ = lean_ctor_get(v___x_1855_, 2);
v_auxDeclNGen_1859_ = lean_ctor_get(v___x_1855_, 3);
v_traceState_1860_ = lean_ctor_get(v___x_1855_, 4);
v_recordedDeps_1861_ = lean_ctor_get(v___x_1855_, 6);
v_messages_1862_ = lean_ctor_get(v___x_1855_, 7);
v_infoState_1863_ = lean_ctor_get(v___x_1855_, 8);
v_snapshotTasks_1864_ = lean_ctor_get(v___x_1855_, 9);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1874_ == 0)
{
lean_object* v_unused_1875_; 
v_unused_1875_ = lean_ctor_get(v___x_1855_, 5);
lean_dec(v_unused_1875_);
v___x_1866_ = v___x_1855_;
v_isShared_1867_ = v_isSharedCheck_1874_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_snapshotTasks_1864_);
lean_inc(v_infoState_1863_);
lean_inc(v_messages_1862_);
lean_inc(v_recordedDeps_1861_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1859_);
lean_inc(v_ngen_1858_);
lean_inc(v_nextMacroScope_1857_);
lean_inc(v_env_1856_);
lean_dec(v___x_1855_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1874_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1868_ = l_Lean_Kernel_enableDiag(v_env_1856_, v___y_1851_);
v___x_1869_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 5, v___x_1869_);
lean_ctor_set(v___x_1866_, 0, v___x_1868_);
v___x_1871_ = v___x_1866_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_nextMacroScope_1857_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_ngen_1858_);
lean_ctor_set(v_reuseFailAlloc_1873_, 3, v_auxDeclNGen_1859_);
lean_ctor_set(v_reuseFailAlloc_1873_, 4, v_traceState_1860_);
lean_ctor_set(v_reuseFailAlloc_1873_, 5, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1873_, 6, v_recordedDeps_1861_);
lean_ctor_set(v_reuseFailAlloc_1873_, 7, v_messages_1862_);
lean_ctor_set(v_reuseFailAlloc_1873_, 8, v_infoState_1863_);
lean_ctor_set(v_reuseFailAlloc_1873_, 9, v_snapshotTasks_1864_);
v___x_1871_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_st_ref_put(v___y_1848_, v___x_1871_);
lean_inc(v___y_1848_);
lean_inc_ref(v___y_1842_);
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
v___y_1829_ = v___y_1854_;
v___y_1830_ = v___y_1842_;
v___y_1831_ = v___y_1848_;
goto v___jp_1813_;
}
}
}
v___jp_1876_:
{
if (v___y_1884_ == 0)
{
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1881_);
v___y_1814_ = v___y_1877_;
v___y_1815_ = v___y_1878_;
v___y_1816_ = v___y_1879_;
v___y_1817_ = v___y_1880_;
v___y_1818_ = v___y_1881_;
v___y_1819_ = v___y_1882_;
v___y_1820_ = v___y_1883_;
v___y_1821_ = v___y_1885_;
v___y_1822_ = v___y_1886_;
v___y_1823_ = v___y_1887_;
v___y_1824_ = v___y_1888_;
v___y_1825_ = v___y_1889_;
v___y_1826_ = v___y_1890_;
v___y_1827_ = v___y_1891_;
v___y_1828_ = v___y_1892_;
v___y_1829_ = v___y_1893_;
v___y_1830_ = v___y_1881_;
v___y_1831_ = v___y_1888_;
goto v___jp_1813_;
}
else
{
v___y_1838_ = v___y_1877_;
v___y_1839_ = v___y_1878_;
v___y_1840_ = v___y_1879_;
v___y_1841_ = v___y_1880_;
v___y_1842_ = v___y_1881_;
v___y_1843_ = v___y_1882_;
v___y_1844_ = v___y_1883_;
v___y_1845_ = v___y_1885_;
v___y_1846_ = v___y_1886_;
v___y_1847_ = v___y_1887_;
v___y_1848_ = v___y_1888_;
v___y_1849_ = v___y_1889_;
v___y_1850_ = v___y_1890_;
v___y_1851_ = v___y_1894_;
v___y_1852_ = v___y_1891_;
v___y_1853_ = v___y_1892_;
v___y_1854_ = v___y_1893_;
goto v___jp_1837_;
}
}
v___jp_1895_:
{
lean_object* v___x_1915_; lean_object* v_a_1916_; lean_object* v_ref_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint16_t v___x_1927_; lean_object* v___x_1928_; lean_object* v_env_1929_; uint8_t v___x_1930_; uint16_t v___x_1931_; uint16_t v___x_1932_; uint16_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1915_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1908_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v_ref_1917_ = l_Lean_replaceRef(v___y_1898_, v___y_1898_);
lean_inc(v_ref_1917_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1914_);
v___x_1918_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1918_, 0, v___y_1914_);
lean_ctor_set(v___x_1918_, 1, v___y_1905_);
lean_ctor_set(v___x_1918_, 2, v_ref_1917_);
lean_ctor_set_uint16(v___x_1918_, sizeof(void*)*3, v___y_1911_);
lean_ctor_set_uint8(v___x_1918_, sizeof(void*)*3 + 2, v___y_1899_);
lean_ctor_set_uint8(v___x_1918_, sizeof(void*)*3 + 3, v___y_1901_);
v___x_1919_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1920_ = 0;
v___x_1921_ = l_Lean_MessageData_ofLevel(v___y_1902_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_MessageData_ofLevel(v___y_1906_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
lean_inc_ref(v___y_1903_);
v___x_1926_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1903_, v___x_1919_, v___x_1920_);
v___x_1927_ = l_Lean_OptionFlags_ofOptions(v___x_1926_);
v___x_1928_ = lean_st_ref_get(v___y_1908_);
v_env_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_ref(v_env_1929_);
lean_dec(v___x_1928_);
v___x_1930_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1929_);
lean_dec_ref(v_env_1929_);
v___x_1931_ = 512;
v___x_1932_ = lean_uint16_land(v___x_1927_, v___x_1931_);
v___x_1933_ = 0;
v___x_1934_ = lean_uint16_dec_eq(v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
if (v___y_1912_ == 0)
{
lean_dec(v_ref_1917_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1905_);
v___y_1877_ = v___x_1925_;
v___y_1878_ = v___y_1896_;
v___y_1879_ = v___y_1897_;
v___y_1880_ = v___y_1898_;
v___y_1881_ = v___x_1918_;
v___y_1882_ = v___y_1900_;
v___y_1883_ = v___y_1903_;
v___y_1884_ = v___x_1930_;
v___y_1885_ = v___y_1904_;
v___y_1886_ = v_a_1916_;
v___y_1887_ = v___y_1907_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v___y_1909_;
v___y_1890_ = v___x_1927_;
v___y_1891_ = v___y_1910_;
v___y_1892_ = v___y_1913_;
v___y_1893_ = v___x_1926_;
v___y_1894_ = v___y_1912_;
goto v___jp_1876_;
}
else
{
if (v___x_1930_ == 0)
{
lean_dec(v_ref_1917_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1905_);
v___y_1838_ = v___x_1925_;
v___y_1839_ = v___y_1896_;
v___y_1840_ = v___y_1897_;
v___y_1841_ = v___y_1898_;
v___y_1842_ = v___x_1918_;
v___y_1843_ = v___y_1900_;
v___y_1844_ = v___y_1903_;
v___y_1845_ = v___y_1904_;
v___y_1846_ = v_a_1916_;
v___y_1847_ = v___y_1907_;
v___y_1848_ = v___y_1908_;
v___y_1849_ = v___y_1909_;
v___y_1850_ = v___x_1927_;
v___y_1851_ = v___y_1912_;
v___y_1852_ = v___y_1910_;
v___y_1853_ = v___y_1913_;
v___y_1854_ = v___x_1926_;
goto v___jp_1837_;
}
else
{
lean_inc(v___y_1908_);
v___y_1727_ = v___x_1925_;
v___y_1728_ = v___y_1896_;
v___y_1729_ = v___y_1897_;
v___y_1730_ = v___y_1898_;
v___y_1731_ = v___x_1918_;
v___y_1732_ = v___y_1900_;
v___y_1733_ = v___y_1903_;
v___y_1734_ = v___y_1904_;
v___y_1735_ = v_a_1916_;
v___y_1736_ = v___y_1907_;
v___y_1737_ = v___y_1908_;
v___y_1738_ = v___y_1909_;
v___y_1739_ = v___x_1927_;
v___y_1740_ = v___y_1910_;
v___y_1741_ = v___y_1913_;
v___y_1742_ = v___x_1926_;
v_toCold_1743_ = v___y_1914_;
v_currRecDepth_1744_ = v___y_1905_;
v_ref_1745_ = v_ref_1917_;
v_suppressElabErrors_1746_ = v___y_1899_;
v_isRecordingDeps_1747_ = v___y_1901_;
v___y_1748_ = v___y_1908_;
goto v___jp_1726_;
}
}
}
else
{
lean_dec(v_ref_1917_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1905_);
v___y_1877_ = v___x_1925_;
v___y_1878_ = v___y_1896_;
v___y_1879_ = v___y_1897_;
v___y_1880_ = v___y_1898_;
v___y_1881_ = v___x_1918_;
v___y_1882_ = v___y_1900_;
v___y_1883_ = v___y_1903_;
v___y_1884_ = v___x_1930_;
v___y_1885_ = v___y_1904_;
v___y_1886_ = v_a_1916_;
v___y_1887_ = v___y_1907_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v___y_1909_;
v___y_1890_ = v___x_1927_;
v___y_1891_ = v___y_1910_;
v___y_1892_ = v___y_1913_;
v___y_1893_ = v___x_1926_;
v___y_1894_ = v___x_1920_;
goto v___jp_1876_;
}
}
v___jp_1935_:
{
lean_object* v_toCold_1942_; lean_object* v_options_1943_; lean_object* v_currRecDepth_1944_; lean_object* v_ref_1945_; uint16_t v_optionFlags_1946_; uint8_t v_suppressElabErrors_1947_; uint8_t v_isRecordingDeps_1948_; lean_object* v_inheritedTraceOptions_1949_; uint8_t v_hasTrace_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___y_1959_; 
v_toCold_1942_ = lean_ctor_get(v___y_1940_, 0);
v_options_1943_ = lean_ctor_get(v_toCold_1942_, 2);
v_currRecDepth_1944_ = lean_ctor_get(v___y_1940_, 1);
v_ref_1945_ = lean_ctor_get(v___y_1940_, 2);
v_optionFlags_1946_ = lean_ctor_get_uint16(v___y_1940_, sizeof(void*)*3);
v_suppressElabErrors_1947_ = lean_ctor_get_uint8(v___y_1940_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1948_ = lean_ctor_get_uint8(v___y_1940_, sizeof(void*)*3 + 3);
v_inheritedTraceOptions_1949_ = lean_ctor_get(v_toCold_1942_, 11);
v_hasTrace_1950_ = lean_ctor_get_uint8(v_options_1943_, sizeof(void*)*1);
v___x_1951_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1953_ = l_Lean_Level_getLevelOffset(v_lhs_1936_);
v___x_1954_ = l_Lean_Level_getLevelOffset(v_rhs_1937_);
v___x_1955_ = lean_level_eq(v___x_1953_, v___x_1954_);
lean_dec(v___x_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = 1;
v___x_1957_ = lean_box(v___x_1955_);
v___x_1958_ = lean_box(v___x_1956_);
lean_inc(v_rhs_1937_);
lean_inc(v_lhs_1936_);
v___y_1959_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1959_, 0, v___x_1957_);
lean_closure_set(v___y_1959_, 1, v_lhs_1936_);
lean_closure_set(v___y_1959_, 2, v_rhs_1937_);
lean_closure_set(v___y_1959_, 3, v___x_1958_);
lean_closure_set(v___y_1959_, 4, v___x_1951_);
lean_closure_set(v___y_1959_, 5, v___x_1952_);
if (v_hasTrace_1950_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v___y_1959_);
v___x_1960_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1955_, v_lhs_1936_, v_rhs_1937_, v___x_1956_, v___x_1951_, v___x_1952_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1961_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1962_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1963_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1949_, v_options_1943_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = l_Lean_trace_profiler;
v___x_1966_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_options_1943_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec_ref(v___y_1959_);
v___x_1967_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1955_, v_lhs_1936_, v_rhs_1937_, v___x_1956_, v___x_1951_, v___x_1952_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v___x_1967_;
}
else
{
lean_inc(v_ref_1945_);
lean_inc(v_currRecDepth_1944_);
lean_inc_ref(v_options_1943_);
lean_inc_ref(v_toCold_1942_);
v___y_1896_ = v___x_1964_;
v___y_1897_ = v___y_1940_;
v___y_1898_ = v_ref_1945_;
v___y_1899_ = v_suppressElabErrors_1947_;
v___y_1900_ = v___y_1959_;
v___y_1901_ = v_isRecordingDeps_1948_;
v___y_1902_ = v_lhs_1936_;
v___y_1903_ = v_options_1943_;
v___y_1904_ = v___y_1938_;
v___y_1905_ = v_currRecDepth_1944_;
v___y_1906_ = v_rhs_1937_;
v___y_1907_ = v___y_1939_;
v___y_1908_ = v___y_1941_;
v___y_1909_ = v___x_1962_;
v___y_1910_ = v___x_1956_;
v___y_1911_ = v_optionFlags_1946_;
v___y_1912_ = v_hasTrace_1950_;
v___y_1913_ = v___x_1961_;
v___y_1914_ = v_toCold_1942_;
goto v___jp_1895_;
}
}
else
{
lean_inc(v_ref_1945_);
lean_inc(v_currRecDepth_1944_);
lean_inc_ref(v_options_1943_);
lean_inc_ref(v_toCold_1942_);
v___y_1896_ = v___x_1964_;
v___y_1897_ = v___y_1940_;
v___y_1898_ = v_ref_1945_;
v___y_1899_ = v_suppressElabErrors_1947_;
v___y_1900_ = v___y_1959_;
v___y_1901_ = v_isRecordingDeps_1948_;
v___y_1902_ = v_lhs_1936_;
v___y_1903_ = v_options_1943_;
v___y_1904_ = v___y_1938_;
v___y_1905_ = v_currRecDepth_1944_;
v___y_1906_ = v_rhs_1937_;
v___y_1907_ = v___y_1939_;
v___y_1908_ = v___y_1941_;
v___y_1909_ = v___x_1962_;
v___y_1910_ = v___x_1956_;
v___y_1911_ = v_optionFlags_1946_;
v___y_1912_ = v_hasTrace_1950_;
v___y_1913_ = v___x_1961_;
v___y_1914_ = v_toCold_1942_;
goto v___jp_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = lean_is_level_def_eq(v_x_1971_, v_x_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1979_, lean_object* v_x_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1980_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1987_, v_x_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2051_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2052_ = 0;
v___x_2053_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2054_ = l_Lean_registerTraceClass(v___x_2051_, v___x_2052_, v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref_known(v___x_2054_, 1);
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2056_ = 1;
v___x_2057_ = l_Lean_registerTraceClass(v___x_2055_, v___x_2056_, v___x_2053_);
return v___x_2057_;
}
else
{
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2059_;
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
