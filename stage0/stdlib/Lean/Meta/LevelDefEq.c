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
size_t v_x_2691__boxed_196_; size_t v_x_2692__boxed_197_; lean_object* v_res_198_; 
v_x_2691__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_x_2692__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_191_, v_x_2691__boxed_196_, v_x_2692__boxed_197_, v_x_194_, v_x_195_);
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
lean_object* v___x_256_; lean_object* v_env_257_; lean_object* v___x_258_; lean_object* v_toCold_259_; lean_object* v_mctx_260_; lean_object* v_lctx_261_; lean_object* v_options_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_256_ = lean_st_ref_get(v___y_254_);
v_env_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_env_257_);
lean_dec(v___x_256_);
v___x_258_ = lean_st_ref_get(v___y_252_);
v_toCold_259_ = lean_ctor_get(v___y_253_, 0);
v_mctx_260_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_mctx_260_);
lean_dec(v___x_258_);
v_lctx_261_ = lean_ctor_get(v___y_251_, 2);
v_options_262_ = lean_ctor_get(v_toCold_259_, 2);
lean_inc_ref(v_options_262_);
lean_inc_ref(v_lctx_261_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_257_);
lean_ctor_set(v___x_263_, 1, v_mctx_260_);
lean_ctor_set(v___x_263_, 2, v_lctx_261_);
lean_ctor_set(v___x_263_, 3, v_options_262_);
v___x_264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_msgData_250_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_273_; double v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_float_of_nat(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_278_, lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_ref_285_; lean_object* v___x_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_332_; 
v_ref_285_ = lean_ctor_get(v___y_282_, 2);
v___x_286_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_332_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_332_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_332_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v_traceState_292_; lean_object* v_env_293_; lean_object* v_nextMacroScope_294_; lean_object* v_ngen_295_; lean_object* v_auxDeclNGen_296_; lean_object* v_cache_297_; lean_object* v_recordedDeps_298_; lean_object* v_messages_299_; lean_object* v_infoState_300_; lean_object* v_snapshotTasks_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_331_; 
v___x_291_ = lean_st_ref_take(v___y_283_);
v_traceState_292_ = lean_ctor_get(v___x_291_, 4);
v_env_293_ = lean_ctor_get(v___x_291_, 0);
v_nextMacroScope_294_ = lean_ctor_get(v___x_291_, 1);
v_ngen_295_ = lean_ctor_get(v___x_291_, 2);
v_auxDeclNGen_296_ = lean_ctor_get(v___x_291_, 3);
v_cache_297_ = lean_ctor_get(v___x_291_, 5);
v_recordedDeps_298_ = lean_ctor_get(v___x_291_, 6);
v_messages_299_ = lean_ctor_get(v___x_291_, 7);
v_infoState_300_ = lean_ctor_get(v___x_291_, 8);
v_snapshotTasks_301_ = lean_ctor_get(v___x_291_, 9);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_331_ == 0)
{
v___x_303_ = v___x_291_;
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snapshotTasks_301_);
lean_inc(v_infoState_300_);
lean_inc(v_messages_299_);
lean_inc(v_recordedDeps_298_);
lean_inc(v_cache_297_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_296_);
lean_inc(v_ngen_295_);
lean_inc(v_nextMacroScope_294_);
lean_inc(v_env_293_);
lean_dec(v___x_291_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
uint64_t v_tid_305_; lean_object* v_traces_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_330_; 
v_tid_305_ = lean_ctor_get_uint64(v_traceState_292_, sizeof(void*)*1);
v_traces_306_ = lean_ctor_get(v_traceState_292_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_traceState_292_);
if (v_isSharedCheck_330_ == 0)
{
v___x_308_ = v_traceState_292_;
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_traces_306_);
lean_dec(v_traceState_292_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; double v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_box(0);
v___x_312_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_313_ = 0;
v___x_314_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_315_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_315_, 0, v_cls_278_);
lean_ctor_set(v___x_315_, 1, v___x_311_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
lean_ctor_set_float(v___x_315_, sizeof(void*)*3, v___x_312_);
lean_ctor_set_float(v___x_315_, sizeof(void*)*3 + 8, v___x_312_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*3 + 16, v___x_313_);
v___x_316_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_317_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v_a_287_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
lean_inc(v_ref_285_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_ref_285_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_PersistentArray_push___redArg(v_traces_306_, v___x_318_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_319_);
v___x_321_ = v___x_308_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_319_);
lean_ctor_set_uint64(v_reuseFailAlloc_329_, sizeof(void*)*1, v_tid_305_);
v___x_321_ = v_reuseFailAlloc_329_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 4, v___x_321_);
v___x_323_ = v___x_303_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_env_293_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_nextMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_ngen_295_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_auxDeclNGen_296_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_cache_297_);
lean_ctor_set(v_reuseFailAlloc_328_, 6, v_recordedDeps_298_);
lean_ctor_set(v_reuseFailAlloc_328_, 7, v_messages_299_);
lean_ctor_set(v_reuseFailAlloc_328_, 8, v_infoState_300_);
lean_ctor_set(v_reuseFailAlloc_328_, 9, v_snapshotTasks_301_);
v___x_323_ = v_reuseFailAlloc_328_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_st_ref_put(v___y_283_, v___x_323_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_310_);
v___x_326_ = v___x_289_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_310_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_333_, lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_333_, v_msg_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = lean_unsigned_to_nat(39u);
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_349_ = l_mkPanicMessageWithDecl(v___x_348_, v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_362_ = l_Lean_Name_append(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_369_, lean_object* v_v_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_Level_isMax(v_v_370_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_v_370_);
lean_dec(v_mvarId_369_);
v___x_377_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_378_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_377_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_mkFreshLevelMVar(v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_toCold_380_; lean_object* v_options_381_; lean_object* v_a_382_; lean_object* v_inheritedTraceOptions_383_; uint8_t v_hasTrace_384_; lean_object* v___x_385_; 
v_toCold_380_ = lean_ctor_get(v_a_373_, 0);
v_options_381_ = lean_ctor_get(v_toCold_380_, 2);
v_a_382_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_379_, 1);
v_inheritedTraceOptions_383_ = lean_ctor_get(v_toCold_380_, 11);
v_hasTrace_384_ = lean_ctor_get_uint8(v_options_381_, sizeof(void*)*1);
v___x_385_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_369_, v_v_370_, v_a_382_);
if (v_hasTrace_384_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_369_, v___x_385_, v_a_372_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_383_, v_options_381_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_369_, v___x_385_, v_a_372_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_369_);
v___x_392_ = l_Lean_mkLevelMVar(v_mvarId_369_);
v___x_393_ = l_Lean_MessageData_ofLevel(v___x_392_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_391_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
lean_inc(v___x_385_);
v___x_397_ = l_Lean_MessageData_ofLevel(v___x_385_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_387_, v___x_398_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_400_; 
lean_dec_ref_known(v___x_399_, 1);
v___x_400_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_369_, v___x_385_, v_a_372_);
return v___x_400_;
}
else
{
lean_dec(v___x_385_);
lean_dec(v_mvarId_369_);
return v___x_399_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_v_370_);
lean_dec(v_mvarId_369_);
v_a_401_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_379_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_379_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_409_, lean_object* v_v_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_409_, v_v_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_417_, lean_object* v_val_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_417_, v_val_418_, v___y_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_425_, lean_object* v_val_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_425_, v_val_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_434_, v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, size_t v_x_440_, size_t v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_439_, v_x_440_, v_x_441_, v_x_442_, v_x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
size_t v_x_3199__boxed_451_; size_t v_x_3200__boxed_452_; lean_object* v_res_453_; 
v_x_3199__boxed_451_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_x_3200__boxed_452_ = lean_unbox_usize(v_x_448_);
lean_dec(v_x_448_);
v_res_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_445_, v_x_446_, v_x_3199__boxed_451_, v_x_3200__boxed_452_, v_x_449_, v_x_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_454_, lean_object* v_n_455_, lean_object* v_k_456_, lean_object* v_v_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_455_, v_k_456_, v_v_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_459_, size_t v_depth_460_, lean_object* v_keys_461_, lean_object* v_vals_462_, lean_object* v_heq_463_, lean_object* v_i_464_, lean_object* v_entries_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_460_, v_keys_461_, v_vals_462_, v_i_464_, v_entries_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_467_, lean_object* v_depth_468_, lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_heq_471_, lean_object* v_i_472_, lean_object* v_entries_473_){
_start:
{
size_t v_depth_boxed_474_; lean_object* v_res_475_; 
v_depth_boxed_474_ = lean_unbox_usize(v_depth_468_);
lean_dec(v_depth_468_);
v_res_475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_467_, v_depth_boxed_474_, v_keys_469_, v_vals_470_, v_heq_471_, v_i_472_, v_entries_473_);
lean_dec_ref(v_vals_470_);
lean_dec_ref(v_keys_469_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_477_, v_x_478_, v_x_479_, v_x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_485_, lean_object* v_v_x27_486_, lean_object* v_mvarId_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
uint8_t v___x_493_; lean_object* v___y_495_; 
v___x_493_ = lean_level_eq(v_u_485_, v_v_x27_486_);
if (v___x_493_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_mvarId_487_);
lean_dec(v_u_485_);
v___x_506_ = lean_box(v___x_493_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v_toCold_508_; lean_object* v_options_509_; uint8_t v_hasTrace_510_; 
v_toCold_508_ = lean_ctor_get(v_a_490_, 0);
v_options_509_ = lean_ctor_get(v_toCold_508_, 2);
v_hasTrace_510_ = lean_ctor_get_uint8(v_options_509_, sizeof(void*)*1);
if (v_hasTrace_510_ == 0)
{
v___y_495_ = v_a_489_;
goto v___jp_494_;
}
else
{
lean_object* v_inheritedTraceOptions_511_; lean_object* v_cls_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_inheritedTraceOptions_511_ = lean_ctor_get(v_toCold_508_, 11);
v_cls_512_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_513_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_511_, v_options_509_, v___x_513_);
if (v___x_514_ == 0)
{
v___y_495_ = v_a_489_;
goto v___jp_494_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_487_);
v___x_516_ = l_Lean_mkLevelMVar(v_mvarId_487_);
v___x_517_ = l_Lean_MessageData_ofLevel(v___x_516_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
lean_inc(v_u_485_);
v___x_521_ = l_Lean_MessageData_ofLevel(v_u_485_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_512_, v___x_522_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_dec_ref_known(v___x_523_, 1);
v___y_495_ = v_a_489_;
goto v___jp_494_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_mvarId_487_);
lean_dec(v_u_485_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
v___jp_494_:
{
lean_object* v___x_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v___x_496_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_487_, v_u_485_, v___y_495_);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_496_, 0);
lean_dec(v_unused_505_);
v___x_498_ = v___x_496_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_dec(v___x_496_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_box(v___x_493_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_532_, lean_object* v_v_x27_533_, lean_object* v_mvarId_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_532_, v_v_x27_533_, v_mvarId_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_v_x27_533_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_541_, lean_object* v_v_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
if (lean_obj_tag(v_v_542_) == 2)
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v_v_542_, 1);
lean_inc(v_a_552_);
if (lean_obj_tag(v_a_552_) == 5)
{
lean_object* v_a_553_; lean_object* v_a_554_; lean_object* v___x_555_; 
v_a_553_ = lean_ctor_get(v_v_542_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v_v_542_, 2);
v_a_554_ = lean_ctor_get(v_a_552_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v_a_552_, 1);
v___x_555_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_541_, v_a_553_, v_a_554_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_553_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v_v_542_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v_v_542_, 2);
if (lean_obj_tag(v_a_556_) == 5)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v_a_556_, 1);
v___x_558_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_541_, v_a_552_, v_a_557_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_552_);
return v___x_558_;
}
else
{
lean_dec(v_a_556_);
lean_dec(v_a_552_);
lean_dec(v_u_541_);
goto v___jp_548_;
}
}
}
else
{
lean_dec(v_v_542_);
lean_dec(v_u_541_);
goto v___jp_548_;
}
v___jp_548_:
{
uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = 0;
v___x_550_ = lean_box(v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_559_, lean_object* v_v_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_559_, v_v_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
return v_res_566_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_570_, lean_object* v_u_u2082_571_, lean_object* v_v_x27_572_, lean_object* v_mvarId_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
uint8_t v___x_579_; uint8_t v___x_580_; lean_object* v___y_582_; lean_object* v___y_594_; 
v___x_579_ = lean_level_eq(v_u_u2081_570_, v_v_x27_572_);
v___x_580_ = 1;
if (v___x_579_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = lean_level_eq(v_u_u2082_571_, v_v_x27_572_);
lean_dec(v_u_u2082_571_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v_mvarId_573_);
lean_dec(v_u_u2081_570_);
v___x_606_ = lean_box(v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v_toCold_608_; lean_object* v_options_609_; uint8_t v_hasTrace_610_; 
v_toCold_608_ = lean_ctor_get(v_a_576_, 0);
v_options_609_ = lean_ctor_get(v_toCold_608_, 2);
v_hasTrace_610_ = lean_ctor_get_uint8(v_options_609_, sizeof(void*)*1);
if (v_hasTrace_610_ == 0)
{
v___y_594_ = v_a_575_;
goto v___jp_593_;
}
else
{
lean_object* v_inheritedTraceOptions_611_; lean_object* v_cls_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_inheritedTraceOptions_611_ = lean_ctor_get(v_toCold_608_, 11);
v_cls_612_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_613_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_614_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_611_, v_options_609_, v___x_613_);
if (v___x_614_ == 0)
{
v___y_594_ = v_a_575_;
goto v___jp_593_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_615_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_573_);
v___x_616_ = l_Lean_mkLevelMVar(v_mvarId_573_);
v___x_617_ = l_Lean_MessageData_ofLevel(v___x_616_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_615_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
lean_inc(v_u_u2081_570_);
v___x_621_ = l_Lean_MessageData_ofLevel(v_u_u2081_570_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_612_, v___x_622_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_dec_ref_known(v___x_623_, 1);
v___y_594_ = v_a_575_;
goto v___jp_593_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_mvarId_573_);
lean_dec(v_u_u2081_570_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_632_; lean_object* v_options_633_; uint8_t v_hasTrace_634_; 
lean_dec(v_u_u2081_570_);
v_toCold_632_ = lean_ctor_get(v_a_576_, 0);
v_options_633_ = lean_ctor_get(v_toCold_632_, 2);
v_hasTrace_634_ = lean_ctor_get_uint8(v_options_633_, sizeof(void*)*1);
if (v_hasTrace_634_ == 0)
{
v___y_582_ = v_a_575_;
goto v___jp_581_;
}
else
{
lean_object* v_inheritedTraceOptions_635_; lean_object* v_cls_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_inheritedTraceOptions_635_ = lean_ctor_get(v_toCold_632_, 11);
v_cls_636_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_637_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_635_, v_options_633_, v___x_637_);
if (v___x_638_ == 0)
{
v___y_582_ = v_a_575_;
goto v___jp_581_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_639_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_573_);
v___x_640_ = l_Lean_mkLevelMVar(v_mvarId_573_);
v___x_641_ = l_Lean_MessageData_ofLevel(v___x_640_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_inc(v_u_u2082_571_);
v___x_645_ = l_Lean_MessageData_ofLevel(v_u_u2082_571_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_636_, v___x_646_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v___y_582_ = v_a_575_;
goto v___jp_581_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_mvarId_573_);
lean_dec(v_u_u2082_571_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v___x_583_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_573_, v_u_u2082_571_, v___y_582_);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_592_);
v___x_585_ = v___x_583_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_dec(v___x_583_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_box(v___x_580_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
v___x_595_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_573_, v_u_u2081_570_, v___y_594_);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_604_);
v___x_597_ = v___x_595_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_dec(v___x_595_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_box(v___x_580_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_656_, lean_object* v_u_u2082_657_, lean_object* v_v_x27_658_, lean_object* v_mvarId_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_656_, v_u_u2082_657_, v_v_x27_658_, v_mvarId_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_v_x27_658_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_666_, lean_object* v_v_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
if (lean_obj_tag(v_u_666_) == 2)
{
if (lean_obj_tag(v_v_667_) == 2)
{
lean_object* v_a_677_; 
v_a_677_ = lean_ctor_get(v_v_667_, 1);
lean_inc(v_a_677_);
if (lean_obj_tag(v_a_677_) == 5)
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_678_ = lean_ctor_get(v_u_666_, 0);
lean_inc(v_a_678_);
v_a_679_ = lean_ctor_get(v_u_666_, 1);
lean_inc(v_a_679_);
lean_dec_ref_known(v_u_666_, 2);
v_a_680_ = lean_ctor_get(v_v_667_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v_v_667_, 2);
v_a_681_ = lean_ctor_get(v_a_677_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v_a_677_, 1);
v___x_682_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_680_);
return v___x_682_;
}
else
{
lean_object* v_a_683_; 
v_a_683_ = lean_ctor_get(v_v_667_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v_v_667_, 2);
if (lean_obj_tag(v_a_683_) == 5)
{
lean_object* v_a_684_; lean_object* v_a_685_; lean_object* v_a_686_; lean_object* v___x_687_; 
v_a_684_ = lean_ctor_get(v_u_666_, 0);
lean_inc(v_a_684_);
v_a_685_ = lean_ctor_get(v_u_666_, 1);
lean_inc(v_a_685_);
lean_dec_ref_known(v_u_666_, 2);
v_a_686_ = lean_ctor_get(v_a_683_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v_a_683_, 1);
v___x_687_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_684_, v_a_685_, v_a_677_, v_a_686_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_677_);
return v___x_687_;
}
else
{
lean_dec(v_a_683_);
lean_dec(v_a_677_);
lean_dec_ref_known(v_u_666_, 2);
goto v___jp_673_;
}
}
}
else
{
lean_dec_ref_known(v_u_666_, 2);
lean_dec(v_v_667_);
goto v___jp_673_;
}
}
else
{
lean_dec(v_v_667_);
lean_dec(v_u_666_);
goto v___jp_673_;
}
v___jp_673_:
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = 0;
v___x_675_ = lean_box(v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_688_, lean_object* v_v_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_688_, v_v_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
return v_res_695_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_703_ = l_Lean_Name_append(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_707_, lean_object* v_rhs_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_toCold_714_; lean_object* v_ref_715_; lean_object* v___y_717_; lean_object* v_options_737_; uint8_t v_hasTrace_738_; 
v_toCold_714_ = lean_ctor_get(v_a_711_, 0);
v_ref_715_ = lean_ctor_get(v_a_711_, 2);
v_options_737_ = lean_ctor_get(v_toCold_714_, 2);
v_hasTrace_738_ = lean_ctor_get_uint8(v_options_737_, sizeof(void*)*1);
if (v_hasTrace_738_ == 0)
{
v___y_717_ = v_a_710_;
goto v___jp_716_;
}
else
{
lean_object* v_inheritedTraceOptions_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_inheritedTraceOptions_739_ = lean_ctor_get(v_toCold_714_, 11);
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_739_, v_options_737_, v___x_741_);
if (v___x_742_ == 0)
{
v___y_717_ = v_a_710_;
goto v___jp_716_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_inc(v_lhs_707_);
v___x_743_ = l_Lean_MessageData_ofLevel(v_lhs_707_);
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v_rhs_708_);
v___x_746_ = l_Lean_MessageData_ofLevel(v_rhs_708_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_740_, v___x_747_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
v___y_717_ = v_a_710_;
goto v___jp_716_;
}
else
{
lean_dec(v_rhs_708_);
lean_dec(v_lhs_707_);
return v___x_748_;
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v_mctx_719_; lean_object* v_cache_720_; lean_object* v_zetaDeltaFVarIds_721_; lean_object* v_postponed_722_; lean_object* v_diag_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_736_; 
v___x_718_ = lean_st_ref_take(v___y_717_);
v_mctx_719_ = lean_ctor_get(v___x_718_, 0);
v_cache_720_ = lean_ctor_get(v___x_718_, 1);
v_zetaDeltaFVarIds_721_ = lean_ctor_get(v___x_718_, 2);
v_postponed_722_ = lean_ctor_get(v___x_718_, 3);
v_diag_723_ = lean_ctor_get(v___x_718_, 4);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_736_ == 0)
{
v___x_725_ = v___x_718_;
v_isShared_726_ = v_isSharedCheck_736_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_diag_723_);
lean_inc(v_postponed_722_);
lean_inc(v_zetaDeltaFVarIds_721_);
lean_inc(v_cache_720_);
lean_inc(v_mctx_719_);
lean_dec(v___x_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_736_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_defEqCtx_x3f_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v_defEqCtx_x3f_727_ = lean_ctor_get(v_a_709_, 4);
v___x_728_ = lean_box(0);
lean_inc(v_defEqCtx_x3f_727_);
lean_inc(v_ref_715_);
v___x_729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_729_, 0, v_ref_715_);
lean_ctor_set(v___x_729_, 1, v_lhs_707_);
lean_ctor_set(v___x_729_, 2, v_rhs_708_);
lean_ctor_set(v___x_729_, 3, v_defEqCtx_x3f_727_);
v___x_730_ = l_Lean_PersistentArray_push___redArg(v_postponed_722_, v___x_729_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 3, v___x_730_);
v___x_732_ = v___x_725_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_mctx_719_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_cache_720_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_zetaDeltaFVarIds_721_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_diag_723_);
v___x_732_ = v_reuseFailAlloc_735_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_st_ref_put(v___y_717_, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_728_);
return v___x_734_;
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
lean_dec_ref_known(v_v_757_, 1);
v___x_765_ = l_Lean_LMVarId_getLevel(v_a_764_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
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
lean_object* v___y_813_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_888_; lean_object* v___y_902_; 
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
uint8_t v___x_933_; 
v___x_933_ = lean_unbox(v_a_923_);
lean_dec(v_a_923_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; 
v___x_934_ = l_Lean_Level_occurs(v_u_805_, v_v_806_);
if (v___x_934_ == 0)
{
lean_object* v_toCold_935_; lean_object* v_options_936_; uint8_t v_hasTrace_937_; 
lean_del_object(v___x_925_);
v_toCold_935_ = lean_ctor_get(v_a_809_, 0);
v_options_936_ = lean_ctor_get(v_toCold_935_, 2);
v_hasTrace_937_ = lean_ctor_get_uint8(v_options_936_, sizeof(void*)*1);
if (v_hasTrace_937_ == 0)
{
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
v___y_888_ = v_a_808_;
goto v___jp_887_;
}
else
{
lean_object* v_inheritedTraceOptions_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_inheritedTraceOptions_938_ = lean_ctor_get(v_toCold_935_, 11);
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_938_, v_options_936_, v___x_940_);
if (v___x_941_ == 0)
{
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
v___y_888_ = v_a_808_;
goto v___jp_887_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_inc_ref(v_u_805_);
v___x_942_ = l_Lean_MessageData_ofLevel(v_u_805_);
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
lean_inc(v_v_806_);
v___x_945_ = l_Lean_MessageData_ofLevel(v_v_806_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_939_, v___x_946_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_807_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_dec_ref_known(v___x_947_, 1);
v___y_888_ = v_a_808_;
goto v___jp_887_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref_known(v_u_805_, 1);
lean_dec(v_a_808_);
lean_dec(v_v_806_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
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
else
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_Level_isMax(v_v_806_);
if (v___x_956_ == 0)
{
lean_dec_ref_known(v_u_805_, 1);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
goto v___jp_927_;
}
else
{
uint8_t v___x_957_; 
v___x_957_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_805_, v_v_806_);
if (v___x_957_ == 0)
{
if (v___x_956_ == 0)
{
lean_dec_ref_known(v_u_805_, 1);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_v_806_);
goto v___jp_927_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_del_object(v___x_925_);
v___x_958_ = l_Lean_Level_mvarId_x21(v_u_805_);
lean_dec_ref_known(v_u_805_, 1);
v___x_959_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_958_, v_v_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_959_, 0);
lean_dec(v_unused_969_);
v___x_961_ = v___x_959_;
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
else
{
lean_dec(v___x_959_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_963_ = 1;
v___x_964_ = lean_box(v___x_963_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_964_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_959_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_959_);
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
else
{
lean_dec_ref_known(v_u_805_, 1);
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
lean_object* v_toCold_978_; lean_object* v_options_979_; uint8_t v_hasTrace_980_; 
lean_del_object(v___x_925_);
v_toCold_978_ = lean_ctor_get(v_a_809_, 0);
v_options_979_ = lean_ctor_get(v_toCold_978_, 2);
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
v_inheritedTraceOptions_981_ = lean_ctor_get(v_toCold_978_, 11);
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
lean_dec_ref_known(v___x_990_, 1);
v___y_902_ = v_a_808_;
goto v___jp_901_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref_known(v_u_805_, 1);
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
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref_known(v_u_805_, 1);
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
lean_dec_ref_known(v_u_805_, 1);
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
lean_dec_ref_known(v_u_805_, 1);
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
lean_dec_ref_known(v_v_806_, 1);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
goto v___jp_883_;
}
case 2:
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v_v_806_, 0);
lean_inc(v_a_1022_);
v_a_1023_ = lean_ctor_get(v_v_806_, 1);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_v_806_, 2);
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
lean_dec_ref_known(v___x_1024_, 1);
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
lean_dec_ref_known(v_v_806_, 2);
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
v___x_1035_ = l_Lean_Bool_toLBool(v___x_1034_);
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
lean_dec_ref_known(v_v_806_, 1);
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
v___y_838_ = v_a_807_;
v___y_839_ = v_a_808_;
v___y_840_ = v_a_809_;
v___y_841_ = v_a_810_;
goto v___jp_837_;
}
}
}
case 1:
{
lean_object* v_a_1052_; uint8_t v___y_1054_; 
v_a_1052_ = lean_ctor_get(v_u_805_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v_u_805_, 1);
if (lean_obj_tag(v_v_806_) == 5)
{
lean_dec_ref_known(v_v_806_, 1);
lean_dec(v_a_1052_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
goto v___jp_883_;
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
v___y_1054_ = v___x_1098_;
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
lean_dec_ref_known(v_a_1056_, 1);
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
v___x_1072_ = l_Lean_Bool_toLBool(v___x_1071_);
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
lean_dec_ref_known(v_v_806_, 1);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_u_805_);
goto v___jp_883_;
}
else
{
v___y_838_ = v_a_807_;
v___y_839_ = v_a_808_;
v___y_840_ = v_a_809_;
v___y_841_ = v_a_810_;
goto v___jp_837_;
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
v___x_819_ = l_Lean_Bool_toLBool(v___x_818_);
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
uint8_t v_univApprox_842_; 
v_univApprox_842_ = lean_ctor_get_uint8(v___y_838_, sizeof(void*)*7 + 1);
if (v_univApprox_842_ == 0)
{
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v_v_806_);
lean_dec(v_u_805_);
goto v___jp_833_;
}
else
{
lean_object* v___x_843_; 
lean_inc(v_v_806_);
lean_inc(v_u_805_);
v___x_843_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_805_, v_v_806_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_874_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_874_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_874_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_874_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v___x_848_; 
v___x_848_ = lean_unbox(v_a_844_);
lean_dec(v_a_844_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_del_object(v___x_846_);
v___x_849_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_805_, v_v_806_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_860_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; 
v___x_854_ = lean_unbox(v_a_850_);
lean_dec(v_a_850_);
if (v___x_854_ == 0)
{
lean_del_object(v___x_852_);
goto v___jp_833_;
}
else
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = 1;
v___x_856_ = lean_box(v___x_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
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
v_a_861_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_849_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_849_);
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
else
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v_v_806_);
lean_dec(v_u_805_);
v___x_869_ = 1;
v___x_870_ = lean_box(v___x_869_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_870_);
v___x_872_ = v___x_846_;
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
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v_v_806_);
lean_dec(v_u_805_);
v_a_875_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_843_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_843_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
v___jp_883_:
{
uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = 2;
v___x_885_ = lean_box(v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
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
v___x_1130_ = lean_st_ref_put(v___y_1113_, v___x_1129_);
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
lean_object* v___x_1164_; lean_object* v_traceState_1165_; lean_object* v_traces_1166_; lean_object* v___x_1167_; lean_object* v_traceState_1168_; lean_object* v_env_1169_; lean_object* v_nextMacroScope_1170_; lean_object* v_ngen_1171_; lean_object* v_auxDeclNGen_1172_; lean_object* v_cache_1173_; lean_object* v_recordedDeps_1174_; lean_object* v_messages_1175_; lean_object* v_infoState_1176_; lean_object* v_snapshotTasks_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1196_; 
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
v_recordedDeps_1174_ = lean_ctor_get(v___x_1167_, 6);
v_messages_1175_ = lean_ctor_get(v___x_1167_, 7);
v_infoState_1176_ = lean_ctor_get(v___x_1167_, 8);
v_snapshotTasks_1177_ = lean_ctor_get(v___x_1167_, 9);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1179_ = v___x_1167_;
v_isShared_1180_ = v_isSharedCheck_1196_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snapshotTasks_1177_);
lean_inc(v_infoState_1176_);
lean_inc(v_messages_1175_);
lean_inc(v_recordedDeps_1174_);
lean_inc(v_cache_1173_);
lean_inc(v_traceState_1168_);
lean_inc(v_auxDeclNGen_1172_);
lean_inc(v_ngen_1171_);
lean_inc(v_nextMacroScope_1170_);
lean_inc(v_env_1169_);
lean_dec(v___x_1167_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1196_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint64_t v_tid_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1194_; 
v_tid_1181_ = lean_ctor_get_uint64(v_traceState_1168_, sizeof(void*)*1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_traceState_1168_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_traceState_1168_, 0);
lean_dec(v_unused_1195_);
v___x_1183_ = v_traceState_1168_;
v_isShared_1184_ = v_isSharedCheck_1194_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v_traceState_1168_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1194_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1185_);
lean_ctor_set_uint64(v_reuseFailAlloc_1193_, sizeof(void*)*1, v_tid_1181_);
v___x_1187_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 4, v___x_1187_);
v___x_1189_ = v___x_1179_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_env_1169_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_nextMacroScope_1170_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_ngen_1171_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_auxDeclNGen_1172_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1192_, 5, v_cache_1173_);
lean_ctor_set(v_reuseFailAlloc_1192_, 6, v_recordedDeps_1174_);
lean_ctor_set(v_reuseFailAlloc_1192_, 7, v_messages_1175_);
lean_ctor_set(v_reuseFailAlloc_1192_, 8, v_infoState_1176_);
lean_ctor_set(v_reuseFailAlloc_1192_, 9, v_snapshotTasks_1177_);
v___x_1189_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_st_ref_put(v___y_1162_, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_traces_1166_);
return v___x_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1197_);
lean_dec(v___y_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1212_, lean_object* v_k_1213_, uint8_t v_v_1214_){
_start:
{
lean_object* v_map_1215_; uint8_t v_hasTrace_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1230_; 
v_map_1215_ = lean_ctor_get(v_o_1212_, 0);
v_hasTrace_1216_ = lean_ctor_get_uint8(v_o_1212_, sizeof(void*)*1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_o_1212_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1218_ = v_o_1212_;
v_isShared_1219_ = v_isSharedCheck_1230_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_map_1215_);
lean_dec(v_o_1212_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1230_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1220_, 0, v_v_1214_);
lean_inc(v_k_1213_);
v___x_1221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1213_, v___x_1220_, v_map_1215_);
if (v_hasTrace_1216_ == 0)
{
lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1225_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1223_ = l_Lean_Name_isPrefixOf(v___x_1222_, v_k_1213_);
lean_dec(v_k_1213_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1221_);
v___x_1225_ = v___x_1218_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1221_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*1, v___x_1223_);
return v___x_1225_;
}
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_k_1213_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1221_);
v___x_1228_ = v___x_1218_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*1, v_hasTrace_1216_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1231_, lean_object* v_k_1232_, lean_object* v_v_1233_){
_start:
{
uint8_t v_v_boxed_1234_; lean_object* v_res_1235_; 
v_v_boxed_1234_ = lean_unbox(v_v_1233_);
v_res_1235_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1231_, v_k_1232_, v_v_boxed_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1236_, lean_object* v_opt_1237_){
_start:
{
lean_object* v_name_1238_; lean_object* v_defValue_1239_; lean_object* v_map_1240_; lean_object* v___x_1241_; 
v_name_1238_ = lean_ctor_get(v_opt_1237_, 0);
v_defValue_1239_ = lean_ctor_get(v_opt_1237_, 1);
v_map_1240_ = lean_ctor_get(v_opts_1236_, 0);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1240_, v_name_1238_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_inc(v_defValue_1239_);
return v_defValue_1239_;
}
else
{
lean_object* v_val_1242_; 
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v___x_1241_, 1);
if (lean_obj_tag(v_val_1242_) == 3)
{
lean_object* v_v_1243_; 
v_v_1243_ = lean_ctor_get(v_val_1242_, 0);
lean_inc(v_v_1243_);
lean_dec_ref_known(v_val_1242_, 1);
return v_v_1243_;
}
else
{
lean_dec(v_val_1242_);
lean_inc(v_defValue_1239_);
return v_defValue_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1244_, lean_object* v_opt_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1244_, v_opt_1245_);
lean_dec_ref(v_opt_1245_);
lean_dec_ref(v_opts_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1247_, lean_object* v_opt_1248_){
_start:
{
lean_object* v_name_1249_; lean_object* v_defValue_1250_; lean_object* v_map_1251_; lean_object* v___x_1252_; 
v_name_1249_ = lean_ctor_get(v_opt_1248_, 0);
v_defValue_1250_ = lean_ctor_get(v_opt_1248_, 1);
v_map_1251_ = lean_ctor_get(v_opts_1247_, 0);
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1251_, v_name_1249_);
if (lean_obj_tag(v___x_1252_) == 0)
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_unbox(v_defValue_1250_);
return v___x_1253_;
}
else
{
lean_object* v_val_1254_; 
v_val_1254_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v___x_1252_, 1);
if (lean_obj_tag(v_val_1254_) == 1)
{
uint8_t v_v_1255_; 
v_v_1255_ = lean_ctor_get_uint8(v_val_1254_, 0);
lean_dec_ref_known(v_val_1254_, 0);
return v_v_1255_;
}
else
{
uint8_t v___x_1256_; 
lean_dec(v_val_1254_);
v___x_1256_ = lean_unbox(v_defValue_1250_);
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1257_, lean_object* v_opt_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1257_, v_opt_1258_);
lean_dec_ref(v_opt_1258_);
lean_dec_ref(v_opts_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v_lhs_1264_, lean_object* v_rhs_1265_, uint8_t v___x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___y_1300_; 
if (v___x_1261_ == 0)
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
lean_inc(v_lhs_1264_);
v___x_1337_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1264_, v___y_1268_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Lean_Level_normalize(v_a_1338_);
lean_dec(v_a_1338_);
lean_inc(v_rhs_1265_);
v___x_1340_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1265_, v___y_1268_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = l_Lean_Level_normalize(v_a_1341_);
lean_dec(v_a_1341_);
v___x_1343_ = lean_level_eq(v_lhs_1264_, v___x_1339_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
v___x_1344_ = lean_is_level_def_eq(v___x_1339_, v___x_1342_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1344_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_level_eq(v_rhs_1265_, v___x_1342_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
v___x_1346_ = lean_is_level_def_eq(v___x_1339_, v___x_1342_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v___x_1342_);
lean_dec(v___x_1339_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v_rhs_1265_);
lean_inc(v_lhs_1264_);
v___x_1347_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1264_, v_rhs_1265_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
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
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
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
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v_lhs_1264_);
lean_inc(v_rhs_1265_);
v___x_1362_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1265_, v_lhs_1264_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
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
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
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
lean_inc(v_lhs_1264_);
v___x_1376_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1264_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
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
lean_dec_ref_known(v___x_1376_, 1);
lean_inc(v_rhs_1265_);
v___x_1379_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1265_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
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
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
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
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
v___x_1398_ = l_Lean_Level_getOffset(v_lhs_1264_);
lean_dec(v_lhs_1264_);
v___x_1399_ = l_Lean_Level_getOffset(v_rhs_1265_);
lean_dec(v_rhs_1265_);
v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
lean_dec(v___x_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
v___jp_1272_:
{
lean_object* v_toCold_1273_; lean_object* v_options_1274_; uint8_t v_hasTrace_1275_; 
v_toCold_1273_ = lean_ctor_get(v___y_1269_, 0);
v_options_1274_ = lean_ctor_get(v_toCold_1273_, 2);
v_hasTrace_1275_ = lean_ctor_get_uint8(v_options_1274_, sizeof(void*)*1);
if (v_hasTrace_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
v___x_1276_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1276_;
}
else
{
lean_object* v_inheritedTraceOptions_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_inheritedTraceOptions_1277_ = lean_ctor_get(v_toCold_1273_, 11);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1279_ = l_Lean_Name_mkStr3(v___x_1262_, v___x_1263_, v___x_1278_);
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1279_);
v___x_1281_ = l_Lean_Name_append(v___x_1280_, v___x_1279_);
v___x_1282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1277_, v_options_1274_, v___x_1281_);
lean_dec(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v___x_1279_);
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
v___x_1283_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1284_ = l_Lean_MessageData_ofLevel(v_lhs_1264_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_MessageData_ofLevel(v_rhs_1265_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1279_, v___x_1288_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref_known(v___x_1289_, 1);
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
v___x_1306_ = l_Lean_Meta_Context_config(v___y_1267_);
v_isDefEqStuckEx_1307_ = lean_ctor_get_uint8(v___x_1306_, 4);
lean_dec_ref(v___x_1306_);
if (v_isDefEqStuckEx_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
v___x_1308_ = lean_box(v___x_1261_);
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
v___x_1312_ = l_Lean_Level_isMVar(v_lhs_1264_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_Level_isMVar(v_rhs_1265_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
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
goto v___jp_1272_;
}
}
else
{
lean_del_object(v___x_1303_);
goto v___jp_1272_;
}
}
}
else
{
lean_object* v___x_1318_; 
lean_del_object(v___x_1303_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
v___x_1318_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1264_, v_rhs_1265_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
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
v___x_1322_ = lean_box(v___x_1266_);
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
lean_dec(v_rhs_1265_);
lean_dec(v_lhs_1264_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
return v___y_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v_lhs_1406_, lean_object* v_rhs_1407_, lean_object* v___x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___x_13333__boxed_1414_; uint8_t v___x_13336__boxed_1415_; lean_object* v_res_1416_; 
v___x_13333__boxed_1414_ = lean_unbox(v___x_1403_);
v___x_13336__boxed_1415_ = lean_unbox(v___x_1408_);
v_res_1416_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13333__boxed_1414_, v___x_1404_, v___x_1405_, v_lhs_1406_, v_rhs_1407_, v___x_13336__boxed_1415_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1417_){
_start:
{
if (lean_obj_tag(v_e_1417_) == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = 2;
return v___x_1418_;
}
else
{
lean_object* v_a_1419_; uint8_t v___x_1420_; 
v_a_1419_ = lean_ctor_get(v_e_1417_, 0);
v___x_1420_ = lean_unbox(v_a_1419_);
if (v___x_1420_ == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = 1;
return v___x_1421_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = 0;
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1423_);
lean_dec_ref(v_e_1423_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1426_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v_x_1426_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_x_1426_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v_x_1426_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v_x_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 1);
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v_x_1426_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1426_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v_x_1426_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v_x_1426_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 0);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1447_, size_t v_i_1448_, lean_object* v_bs_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
if (v___x_1450_ == 0)
{
return v_bs_1449_;
}
else
{
lean_object* v_v_1451_; lean_object* v_msg_1452_; lean_object* v___x_1453_; lean_object* v_bs_x27_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v_v_1451_ = lean_array_uget_borrowed(v_bs_1449_, v_i_1448_);
v_msg_1452_ = lean_ctor_get(v_v_1451_, 1);
lean_inc_ref(v_msg_1452_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v_bs_x27_1454_ = lean_array_uset(v_bs_1449_, v_i_1448_, v___x_1453_);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1448_, v___x_1455_);
v___x_1457_ = lean_array_uset(v_bs_x27_1454_, v_i_1448_, v_msg_1452_);
v_i_1448_ = v___x_1456_;
v_bs_1449_ = v___x_1457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_bs_1461_){
_start:
{
size_t v_sz_boxed_1462_; size_t v_i_boxed_1463_; lean_object* v_res_1464_; 
v_sz_boxed_1462_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1463_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1462_, v_i_boxed_1463_, v_bs_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1465_, lean_object* v_data_1466_, lean_object* v_ref_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_toCold_1474_; lean_object* v_currRecDepth_1475_; lean_object* v_ref_1476_; uint16_t v_optionFlags_1477_; uint8_t v_suppressElabErrors_1478_; uint8_t v_isRecordingDeps_1479_; lean_object* v_ref_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v_traceState_1483_; lean_object* v_traces_1484_; lean_object* v___x_1485_; size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v_msg_1489_; lean_object* v___x_1490_; lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1529_; 
v_toCold_1474_ = lean_ctor_get(v___y_1471_, 0);
v_currRecDepth_1475_ = lean_ctor_get(v___y_1471_, 1);
v_ref_1476_ = lean_ctor_get(v___y_1471_, 2);
v_optionFlags_1477_ = lean_ctor_get_uint16(v___y_1471_, sizeof(void*)*3);
v_suppressElabErrors_1478_ = lean_ctor_get_uint8(v___y_1471_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1479_ = lean_ctor_get_uint8(v___y_1471_, sizeof(void*)*3 + 3);
v_ref_1480_ = l_Lean_replaceRef(v_ref_1467_, v_ref_1476_);
lean_inc(v_currRecDepth_1475_);
lean_inc_ref(v_toCold_1474_);
v___x_1481_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1481_, 0, v_toCold_1474_);
lean_ctor_set(v___x_1481_, 1, v_currRecDepth_1475_);
lean_ctor_set(v___x_1481_, 2, v_ref_1480_);
lean_ctor_set_uint16(v___x_1481_, sizeof(void*)*3, v_optionFlags_1477_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3 + 2, v_suppressElabErrors_1478_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3 + 3, v_isRecordingDeps_1479_);
v___x_1482_ = lean_st_ref_get(v___y_1472_);
v_traceState_1483_ = lean_ctor_get(v___x_1482_, 4);
lean_inc_ref(v_traceState_1483_);
lean_dec(v___x_1482_);
v_traces_1484_ = lean_ctor_get(v_traceState_1483_, 0);
lean_inc_ref(v_traces_1484_);
lean_dec_ref(v_traceState_1483_);
v___x_1485_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1484_);
lean_dec_ref(v_traces_1484_);
v_sz_1486_ = lean_array_size(v___x_1485_);
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1486_, v___x_1487_, v___x_1485_);
v_msg_1489_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1489_, 0, v_data_1466_);
lean_ctor_set(v_msg_1489_, 1, v_msg_1468_);
lean_ctor_set(v_msg_1489_, 2, v___x_1488_);
v___x_1490_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1489_, v___y_1469_, v___y_1470_, v___x_1481_, v___y_1472_);
lean_dec_ref_known(v___x_1481_, 3);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1529_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1529_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v_traceState_1496_; lean_object* v_env_1497_; lean_object* v_nextMacroScope_1498_; lean_object* v_ngen_1499_; lean_object* v_auxDeclNGen_1500_; lean_object* v_cache_1501_; lean_object* v_recordedDeps_1502_; lean_object* v_messages_1503_; lean_object* v_infoState_1504_; lean_object* v_snapshotTasks_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1528_; 
v___x_1495_ = lean_st_ref_take(v___y_1472_);
v_traceState_1496_ = lean_ctor_get(v___x_1495_, 4);
v_env_1497_ = lean_ctor_get(v___x_1495_, 0);
v_nextMacroScope_1498_ = lean_ctor_get(v___x_1495_, 1);
v_ngen_1499_ = lean_ctor_get(v___x_1495_, 2);
v_auxDeclNGen_1500_ = lean_ctor_get(v___x_1495_, 3);
v_cache_1501_ = lean_ctor_get(v___x_1495_, 5);
v_recordedDeps_1502_ = lean_ctor_get(v___x_1495_, 6);
v_messages_1503_ = lean_ctor_get(v___x_1495_, 7);
v_infoState_1504_ = lean_ctor_get(v___x_1495_, 8);
v_snapshotTasks_1505_ = lean_ctor_get(v___x_1495_, 9);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1507_ = v___x_1495_;
v_isShared_1508_ = v_isSharedCheck_1528_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snapshotTasks_1505_);
lean_inc(v_infoState_1504_);
lean_inc(v_messages_1503_);
lean_inc(v_recordedDeps_1502_);
lean_inc(v_cache_1501_);
lean_inc(v_traceState_1496_);
lean_inc(v_auxDeclNGen_1500_);
lean_inc(v_ngen_1499_);
lean_inc(v_nextMacroScope_1498_);
lean_inc(v_env_1497_);
lean_dec(v___x_1495_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1528_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
uint64_t v_tid_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1526_; 
v_tid_1509_ = lean_ctor_get_uint64(v_traceState_1496_, sizeof(void*)*1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_traceState_1496_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_traceState_1496_, 0);
lean_dec(v_unused_1527_);
v___x_1511_ = v_traceState_1496_;
v_isShared_1512_ = v_isSharedCheck_1526_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_traceState_1496_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1526_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_ref_1467_);
lean_ctor_set(v___x_1514_, 1, v_a_1491_);
v___x_1515_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1465_, v___x_1514_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1515_);
v___x_1517_ = v___x_1511_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1515_);
lean_ctor_set_uint64(v_reuseFailAlloc_1525_, sizeof(void*)*1, v_tid_1509_);
v___x_1517_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v___x_1517_);
v___x_1519_ = v___x_1507_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_env_1497_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextMacroScope_1498_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_ngen_1499_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_auxDeclNGen_1500_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v_cache_1501_);
lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_recordedDeps_1502_);
lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_messages_1503_);
lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_infoState_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 9, v_snapshotTasks_1505_);
v___x_1519_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_st_ref_put(v___y_1472_, v___x_1519_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1513_);
v___x_1522_ = v___x_1493_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1513_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1530_, lean_object* v_data_1531_, lean_object* v_ref_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1530_, v_data_1531_, v_ref_1532_, v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1539_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1540_; double v___x_1541_; 
v___x_1540_ = lean_unsigned_to_nat(1000u);
v___x_1541_ = lean_float_of_nat(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1542_, uint8_t v_collapsed_1543_, lean_object* v_tag_1544_, lean_object* v_opts_1545_, uint8_t v_clsEnabled_1546_, lean_object* v_oldTraces_1547_, lean_object* v_ref_1548_, lean_object* v_msg_1549_, lean_object* v_resStartStop_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_fst_1556_; lean_object* v_snd_1557_; lean_object* v_data_1559_; lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; uint8_t v___y_1584_; double v___y_1616_; 
v_fst_1556_ = lean_ctor_get(v_resStartStop_1550_, 0);
lean_inc(v_fst_1556_);
v_snd_1557_ = lean_ctor_get(v_resStartStop_1550_, 1);
lean_inc(v_snd_1557_);
lean_dec_ref(v_resStartStop_1550_);
v_fst_1570_ = lean_ctor_get(v_snd_1557_, 0);
lean_inc(v_fst_1570_);
v_snd_1571_ = lean_ctor_get(v_snd_1557_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_snd_1557_);
v___x_1572_ = l_Lean_trace_profiler;
v___x_1573_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1545_, v___x_1572_);
if (v___x_1573_ == 0)
{
v___y_1584_ = v___x_1573_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1622_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1545_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; double v___x_1625_; double v___x_1626_; double v___x_1627_; 
v___x_1623_ = l_Lean_trace_profiler_threshold;
v___x_1624_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1545_, v___x_1623_);
v___x_1625_ = lean_float_of_nat(v___x_1624_);
v___x_1626_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1627_ = lean_float_div(v___x_1625_, v___x_1626_);
v___y_1616_ = v___x_1627_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; double v___x_1630_; 
v___x_1628_ = l_Lean_trace_profiler_threshold;
v___x_1629_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1545_, v___x_1628_);
v___x_1630_ = lean_float_of_nat(v___x_1629_);
v___y_1616_ = v___x_1630_;
goto v___jp_1615_;
}
}
v___jp_1558_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1547_, v_data_1559_, v_ref_1548_, v_msg_1549_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; 
lean_dec_ref_known(v___x_1560_, 1);
v___x_1561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1556_);
return v___x_1561_;
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_fst_1556_);
v_a_1562_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1560_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
v___jp_1574_:
{
uint8_t v_result_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; double v___x_1578_; lean_object* v_data_1579_; 
v_result_1575_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1556_);
v___x_1576_ = lean_box(v_result_1575_);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
v___x_1578_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1544_);
lean_inc_ref(v___x_1577_);
lean_inc(v_cls_1542_);
v_data_1579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1579_, 0, v_cls_1542_);
lean_ctor_set(v_data_1579_, 1, v___x_1577_);
lean_ctor_set(v_data_1579_, 2, v_tag_1544_);
lean_ctor_set_float(v_data_1579_, sizeof(void*)*3, v___x_1578_);
lean_ctor_set_float(v_data_1579_, sizeof(void*)*3 + 8, v___x_1578_);
lean_ctor_set_uint8(v_data_1579_, sizeof(void*)*3 + 16, v_collapsed_1543_);
if (v___x_1573_ == 0)
{
lean_dec_ref_known(v___x_1577_, 1);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec_ref(v_tag_1544_);
lean_dec(v_cls_1542_);
v_data_1559_ = v_data_1579_;
goto v___jp_1558_;
}
else
{
lean_object* v_data_1580_; double v___x_1581_; double v___x_1582_; 
lean_dec_ref_known(v_data_1579_, 3);
v_data_1580_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1580_, 0, v_cls_1542_);
lean_ctor_set(v_data_1580_, 1, v___x_1577_);
lean_ctor_set(v_data_1580_, 2, v_tag_1544_);
v___x_1581_ = lean_unbox_float(v_fst_1570_);
lean_dec(v_fst_1570_);
lean_ctor_set_float(v_data_1580_, sizeof(void*)*3, v___x_1581_);
v___x_1582_ = lean_unbox_float(v_snd_1571_);
lean_dec(v_snd_1571_);
lean_ctor_set_float(v_data_1580_, sizeof(void*)*3 + 8, v___x_1582_);
lean_ctor_set_uint8(v_data_1580_, sizeof(void*)*3 + 16, v_collapsed_1543_);
v_data_1559_ = v_data_1580_;
goto v___jp_1558_;
}
}
v___jp_1583_:
{
if (v_clsEnabled_1546_ == 0)
{
if (v___y_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v_traceState_1586_; lean_object* v_env_1587_; lean_object* v_nextMacroScope_1588_; lean_object* v_ngen_1589_; lean_object* v_auxDeclNGen_1590_; lean_object* v_cache_1591_; lean_object* v_recordedDeps_1592_; lean_object* v_messages_1593_; lean_object* v_infoState_1594_; lean_object* v_snapshotTasks_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec_ref(v_msg_1549_);
lean_dec(v_ref_1548_);
lean_dec_ref(v_tag_1544_);
lean_dec(v_cls_1542_);
v___x_1585_ = lean_st_ref_take(v___y_1554_);
v_traceState_1586_ = lean_ctor_get(v___x_1585_, 4);
v_env_1587_ = lean_ctor_get(v___x_1585_, 0);
v_nextMacroScope_1588_ = lean_ctor_get(v___x_1585_, 1);
v_ngen_1589_ = lean_ctor_get(v___x_1585_, 2);
v_auxDeclNGen_1590_ = lean_ctor_get(v___x_1585_, 3);
v_cache_1591_ = lean_ctor_get(v___x_1585_, 5);
v_recordedDeps_1592_ = lean_ctor_get(v___x_1585_, 6);
v_messages_1593_ = lean_ctor_get(v___x_1585_, 7);
v_infoState_1594_ = lean_ctor_get(v___x_1585_, 8);
v_snapshotTasks_1595_ = lean_ctor_get(v___x_1585_, 9);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1597_ = v___x_1585_;
v_isShared_1598_ = v_isSharedCheck_1614_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_snapshotTasks_1595_);
lean_inc(v_infoState_1594_);
lean_inc(v_messages_1593_);
lean_inc(v_recordedDeps_1592_);
lean_inc(v_cache_1591_);
lean_inc(v_traceState_1586_);
lean_inc(v_auxDeclNGen_1590_);
lean_inc(v_ngen_1589_);
lean_inc(v_nextMacroScope_1588_);
lean_inc(v_env_1587_);
lean_dec(v___x_1585_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1614_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
uint64_t v_tid_1599_; lean_object* v_traces_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1613_; 
v_tid_1599_ = lean_ctor_get_uint64(v_traceState_1586_, sizeof(void*)*1);
v_traces_1600_ = lean_ctor_get(v_traceState_1586_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_traceState_1586_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1602_ = v_traceState_1586_;
v_isShared_1603_ = v_isSharedCheck_1613_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_traces_1600_);
lean_dec(v_traceState_1586_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1613_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1547_, v_traces_1600_);
lean_dec_ref(v_traces_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1604_);
lean_ctor_set_uint64(v_reuseFailAlloc_1612_, sizeof(void*)*1, v_tid_1599_);
v___x_1606_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 4, v___x_1606_);
v___x_1608_ = v___x_1597_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_env_1587_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_nextMacroScope_1588_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_ngen_1589_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_auxDeclNGen_1590_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1611_, 5, v_cache_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 6, v_recordedDeps_1592_);
lean_ctor_set(v_reuseFailAlloc_1611_, 7, v_messages_1593_);
lean_ctor_set(v_reuseFailAlloc_1611_, 8, v_infoState_1594_);
lean_ctor_set(v_reuseFailAlloc_1611_, 9, v_snapshotTasks_1595_);
v___x_1608_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_st_ref_put(v___y_1554_, v___x_1608_);
v___x_1610_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1556_);
return v___x_1610_;
}
}
}
}
}
else
{
goto v___jp_1574_;
}
}
else
{
goto v___jp_1574_;
}
}
v___jp_1615_:
{
double v___x_1617_; double v___x_1618_; double v___x_1619_; uint8_t v___x_1620_; 
v___x_1617_ = lean_unbox_float(v_snd_1571_);
v___x_1618_ = lean_unbox_float(v_fst_1570_);
v___x_1619_ = lean_float_sub(v___x_1617_, v___x_1618_);
v___x_1620_ = lean_float_decLt(v___y_1616_, v___x_1619_);
v___y_1584_ = v___x_1620_;
goto v___jp_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1631_, lean_object* v_collapsed_1632_, lean_object* v_tag_1633_, lean_object* v_opts_1634_, lean_object* v_clsEnabled_1635_, lean_object* v_oldTraces_1636_, lean_object* v_ref_1637_, lean_object* v_msg_1638_, lean_object* v_resStartStop_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
uint8_t v_collapsed_boxed_1645_; uint8_t v_clsEnabled_boxed_1646_; lean_object* v_res_1647_; 
v_collapsed_boxed_1645_ = lean_unbox(v_collapsed_1632_);
v_clsEnabled_boxed_1646_ = lean_unbox(v_clsEnabled_1635_);
v_res_1647_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1631_, v_collapsed_boxed_1645_, v_tag_1633_, v_opts_1634_, v_clsEnabled_boxed_1646_, v_oldTraces_1636_, v_ref_1637_, v_msg_1638_, v_resStartStop_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_opts_1634_);
return v_res_1647_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1648_; double v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(1000000000u);
v___x_1649_ = lean_float_of_nat(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1665_ = l_Lean_Name_append(v___x_1664_, v___x_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___y_1674_; lean_object* v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; uint8_t v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v_a_1687_; lean_object* v___y_1697_; lean_object* v___y_1698_; uint8_t v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; uint8_t v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v_a_1710_; lean_object* v___y_1723_; lean_object* v___y_1724_; uint8_t v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; lean_object* v___y_1732_; uint16_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v_toCold_1739_; lean_object* v_currRecDepth_1740_; lean_object* v_ref_1741_; uint8_t v_suppressElabErrors_1742_; uint8_t v_isRecordingDeps_1743_; lean_object* v___y_1744_; lean_object* v___y_1810_; lean_object* v___y_1811_; uint8_t v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; uint8_t v___y_1818_; lean_object* v___y_1819_; uint16_t v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1834_; lean_object* v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; uint8_t v___y_1842_; lean_object* v___y_1843_; uint16_t v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1873_; lean_object* v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; uint16_t v___y_1883_; lean_object* v___y_1884_; uint8_t v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; uint8_t v___y_1890_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1907_; uint16_t v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_lhs_1932_; lean_object* v_rhs_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; 
if (lean_obj_tag(v_x_1666_) == 1)
{
if (lean_obj_tag(v_x_1667_) == 1)
{
lean_object* v_a_1964_; lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1964_ = lean_ctor_get(v_x_1666_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v_x_1666_, 1);
v_a_1965_ = lean_ctor_get(v_x_1667_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v_x_1667_, 1);
v___x_1966_ = lean_is_level_def_eq(v_a_1964_, v_a_1965_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
return v___x_1966_;
}
else
{
v_lhs_1932_ = v_x_1666_;
v_rhs_1933_ = v_x_1667_;
v___y_1934_ = v_a_1668_;
v___y_1935_ = v_a_1669_;
v___y_1936_ = v_a_1670_;
v___y_1937_ = v_a_1671_;
goto v___jp_1931_;
}
}
else
{
v_lhs_1932_ = v_x_1666_;
v_rhs_1933_ = v_x_1667_;
v___y_1934_ = v_a_1668_;
v___y_1935_ = v_a_1669_;
v___y_1936_ = v_a_1670_;
v___y_1937_ = v_a_1671_;
goto v___jp_1931_;
}
v___jp_1673_:
{
lean_object* v___x_1688_; double v___x_1689_; double v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1688_ = lean_io_get_num_heartbeats();
v___x_1689_ = lean_float_of_nat(v___y_1683_);
v___x_1690_ = lean_float_of_nat(v___x_1688_);
v___x_1691_ = lean_box_float(v___x_1689_);
v___x_1692_ = lean_box_float(v___x_1690_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1687_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1686_);
v___x_1695_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1686_, v___y_1676_, v___y_1674_, v___y_1680_, v___y_1681_, v___y_1684_, v___y_1685_, v___y_1677_, v___x_1694_, v___y_1679_, v___y_1675_, v___y_1682_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1679_);
lean_dec_ref(v___y_1680_);
return v___x_1695_;
}
v___jp_1696_:
{
lean_object* v___x_1711_; double v___x_1712_; double v___x_1713_; double v___x_1714_; double v___x_1715_; double v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1711_ = lean_io_mono_nanos_now();
v___x_1712_ = lean_float_of_nat(v___y_1706_);
v___x_1713_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1714_ = lean_float_div(v___x_1712_, v___x_1713_);
v___x_1715_ = lean_float_of_nat(v___x_1711_);
v___x_1716_ = lean_float_div(v___x_1715_, v___x_1713_);
v___x_1717_ = lean_box_float(v___x_1714_);
v___x_1718_ = lean_box_float(v___x_1716_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_a_1710_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1709_);
v___x_1721_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1709_, v___y_1699_, v___y_1697_, v___y_1703_, v___y_1704_, v___y_1707_, v___y_1708_, v___y_1700_, v___x_1720_, v___y_1702_, v___y_1698_, v___y_1705_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v___y_1703_);
return v___x_1721_;
}
v___jp_1722_:
{
lean_object* v_fileName_1745_; lean_object* v_fileMap_1746_; lean_object* v_currNamespace_1747_; lean_object* v_openDecls_1748_; lean_object* v_initHeartbeats_1749_; lean_object* v_maxHeartbeats_1750_; lean_object* v_quotContext_1751_; lean_object* v_currMacroScope_1752_; lean_object* v_cancelTk_x3f_1753_; lean_object* v_inheritedTraceOptions_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1806_; 
v_fileName_1745_ = lean_ctor_get(v_toCold_1739_, 0);
v_fileMap_1746_ = lean_ctor_get(v_toCold_1739_, 1);
v_currNamespace_1747_ = lean_ctor_get(v_toCold_1739_, 4);
v_openDecls_1748_ = lean_ctor_get(v_toCold_1739_, 5);
v_initHeartbeats_1749_ = lean_ctor_get(v_toCold_1739_, 6);
v_maxHeartbeats_1750_ = lean_ctor_get(v_toCold_1739_, 7);
v_quotContext_1751_ = lean_ctor_get(v_toCold_1739_, 8);
v_currMacroScope_1752_ = lean_ctor_get(v_toCold_1739_, 9);
v_cancelTk_x3f_1753_ = lean_ctor_get(v_toCold_1739_, 10);
v_inheritedTraceOptions_1754_ = lean_ctor_get(v_toCold_1739_, 11);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_toCold_1739_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; lean_object* v_unused_1808_; 
v_unused_1807_ = lean_ctor_get(v_toCold_1739_, 3);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_toCold_1739_, 2);
lean_dec(v_unused_1808_);
v___x_1756_ = v_toCold_1739_;
v_isShared_1757_ = v_isSharedCheck_1806_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_inheritedTraceOptions_1754_);
lean_inc(v_cancelTk_x3f_1753_);
lean_inc(v_currMacroScope_1752_);
lean_inc(v_quotContext_1751_);
lean_inc(v_maxHeartbeats_1750_);
lean_inc(v_initHeartbeats_1749_);
lean_inc(v_openDecls_1748_);
lean_inc(v_currNamespace_1747_);
lean_inc(v_fileMap_1746_);
lean_inc(v_fileName_1745_);
lean_dec(v_toCold_1739_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1806_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1758_ = l_Lean_maxRecDepth;
v___x_1759_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1734_, v___x_1758_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 3, v___x_1759_);
lean_ctor_set(v___x_1756_, 2, v___y_1734_);
v___x_1761_ = v___x_1756_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_fileName_1745_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_fileMap_1746_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v___y_1734_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1805_, 4, v_currNamespace_1747_);
lean_ctor_set(v_reuseFailAlloc_1805_, 5, v_openDecls_1748_);
lean_ctor_set(v_reuseFailAlloc_1805_, 6, v_initHeartbeats_1749_);
lean_ctor_set(v_reuseFailAlloc_1805_, 7, v_maxHeartbeats_1750_);
lean_ctor_set(v_reuseFailAlloc_1805_, 8, v_quotContext_1751_);
lean_ctor_set(v_reuseFailAlloc_1805_, 9, v_currMacroScope_1752_);
lean_ctor_set(v_reuseFailAlloc_1805_, 10, v_cancelTk_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1805_, 11, v_inheritedTraceOptions_1754_);
v___x_1761_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v_a_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1762_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v_currRecDepth_1740_);
lean_ctor_set(v___x_1762_, 2, v_ref_1741_);
lean_ctor_set_uint16(v___x_1762_, sizeof(void*)*3, v___y_1733_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*3 + 2, v_suppressElabErrors_1742_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*3 + 3, v_isRecordingDeps_1743_);
v___x_1763_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1726_, v___y_1729_, v___y_1724_, v___x_1762_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref_known(v___x_1762_, 3);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1764_, v___y_1729_, v___y_1724_, v___y_1738_, v___y_1727_);
lean_dec_ref(v___y_1738_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1768_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1730_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_io_mono_nanos_now();
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1729_);
v___x_1770_ = lean_apply_5(v___y_1728_, v___y_1729_, v___y_1724_, v___y_1732_, v___y_1727_, lean_box(0));
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 1);
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
v___y_1697_ = v___y_1723_;
v___y_1698_ = v___y_1724_;
v___y_1699_ = v___y_1725_;
v___y_1700_ = v_a_1766_;
v___y_1701_ = v___y_1727_;
v___y_1702_ = v___y_1729_;
v___y_1703_ = v___y_1730_;
v___y_1704_ = v___y_1731_;
v___y_1705_ = v___y_1732_;
v___y_1706_ = v___x_1769_;
v___y_1707_ = v___y_1736_;
v___y_1708_ = v___y_1735_;
v___y_1709_ = v___y_1737_;
v_a_1710_ = v___x_1776_;
goto v___jp_1696_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1770_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1770_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 0);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v___y_1697_ = v___y_1723_;
v___y_1698_ = v___y_1724_;
v___y_1699_ = v___y_1725_;
v___y_1700_ = v_a_1766_;
v___y_1701_ = v___y_1727_;
v___y_1702_ = v___y_1729_;
v___y_1703_ = v___y_1730_;
v___y_1704_ = v___y_1731_;
v___y_1705_ = v___y_1732_;
v___y_1706_ = v___x_1769_;
v___y_1707_ = v___y_1736_;
v___y_1708_ = v___y_1735_;
v___y_1709_ = v___y_1737_;
v_a_1710_ = v___x_1784_;
goto v___jp_1696_;
}
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1729_);
v___x_1788_ = lean_apply_5(v___y_1728_, v___y_1729_, v___y_1724_, v___y_1732_, v___y_1727_, lean_box(0));
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 1);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v___y_1674_ = v___y_1723_;
v___y_1675_ = v___y_1724_;
v___y_1676_ = v___y_1725_;
v___y_1677_ = v_a_1766_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___y_1729_;
v___y_1680_ = v___y_1730_;
v___y_1681_ = v___y_1731_;
v___y_1682_ = v___y_1732_;
v___y_1683_ = v___x_1787_;
v___y_1684_ = v___y_1736_;
v___y_1685_ = v___y_1735_;
v___y_1686_ = v___y_1737_;
v_a_1687_ = v___x_1794_;
goto v___jp_1673_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1788_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1788_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 0);
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
v___y_1674_ = v___y_1723_;
v___y_1675_ = v___y_1724_;
v___y_1676_ = v___y_1725_;
v___y_1677_ = v_a_1766_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v___y_1729_;
v___y_1680_ = v___y_1730_;
v___y_1681_ = v___y_1731_;
v___y_1682_ = v___y_1732_;
v___y_1683_ = v___x_1787_;
v___y_1684_ = v___y_1736_;
v___y_1685_ = v___y_1735_;
v___y_1686_ = v___y_1737_;
v_a_1687_ = v___x_1802_;
goto v___jp_1673_;
}
}
}
}
}
}
}
v___jp_1809_:
{
lean_object* v_toCold_1828_; lean_object* v_currRecDepth_1829_; lean_object* v_ref_1830_; uint8_t v_suppressElabErrors_1831_; uint8_t v_isRecordingDeps_1832_; 
v_toCold_1828_ = lean_ctor_get(v___y_1826_, 0);
lean_inc_ref(v_toCold_1828_);
v_currRecDepth_1829_ = lean_ctor_get(v___y_1826_, 1);
lean_inc(v_currRecDepth_1829_);
v_ref_1830_ = lean_ctor_get(v___y_1826_, 2);
lean_inc(v_ref_1830_);
v_suppressElabErrors_1831_ = lean_ctor_get_uint8(v___y_1826_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1832_ = lean_ctor_get_uint8(v___y_1826_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_1826_);
v___y_1723_ = v___y_1810_;
v___y_1724_ = v___y_1811_;
v___y_1725_ = v___y_1812_;
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
v_toCold_1739_ = v_toCold_1828_;
v_currRecDepth_1740_ = v_currRecDepth_1829_;
v_ref_1741_ = v_ref_1830_;
v_suppressElabErrors_1742_ = v_suppressElabErrors_1831_;
v_isRecordingDeps_1743_ = v_isRecordingDeps_1832_;
v___y_1744_ = v___y_1827_;
goto v___jp_1722_;
}
v___jp_1833_:
{
lean_object* v___x_1851_; lean_object* v_env_1852_; lean_object* v_nextMacroScope_1853_; lean_object* v_ngen_1854_; lean_object* v_auxDeclNGen_1855_; lean_object* v_traceState_1856_; lean_object* v_recordedDeps_1857_; lean_object* v_messages_1858_; lean_object* v_infoState_1859_; lean_object* v_snapshotTasks_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1870_; 
v___x_1851_ = lean_st_ref_take(v___y_1838_);
v_env_1852_ = lean_ctor_get(v___x_1851_, 0);
v_nextMacroScope_1853_ = lean_ctor_get(v___x_1851_, 1);
v_ngen_1854_ = lean_ctor_get(v___x_1851_, 2);
v_auxDeclNGen_1855_ = lean_ctor_get(v___x_1851_, 3);
v_traceState_1856_ = lean_ctor_get(v___x_1851_, 4);
v_recordedDeps_1857_ = lean_ctor_get(v___x_1851_, 6);
v_messages_1858_ = lean_ctor_get(v___x_1851_, 7);
v_infoState_1859_ = lean_ctor_get(v___x_1851_, 8);
v_snapshotTasks_1860_ = lean_ctor_get(v___x_1851_, 9);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v___x_1851_, 5);
lean_dec(v_unused_1871_);
v___x_1862_ = v___x_1851_;
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snapshotTasks_1860_);
lean_inc(v_infoState_1859_);
lean_inc(v_messages_1858_);
lean_inc(v_recordedDeps_1857_);
lean_inc(v_traceState_1856_);
lean_inc(v_auxDeclNGen_1855_);
lean_inc(v_ngen_1854_);
lean_inc(v_nextMacroScope_1853_);
lean_inc(v_env_1852_);
lean_dec(v___x_1851_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1864_ = l_Lean_Kernel_enableDiag(v_env_1852_, v___y_1848_);
v___x_1865_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 5, v___x_1865_);
lean_ctor_set(v___x_1862_, 0, v___x_1864_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_nextMacroScope_1853_);
lean_ctor_set(v_reuseFailAlloc_1869_, 2, v_ngen_1854_);
lean_ctor_set(v_reuseFailAlloc_1869_, 3, v_auxDeclNGen_1855_);
lean_ctor_set(v_reuseFailAlloc_1869_, 4, v_traceState_1856_);
lean_ctor_set(v_reuseFailAlloc_1869_, 5, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1869_, 6, v_recordedDeps_1857_);
lean_ctor_set(v_reuseFailAlloc_1869_, 7, v_messages_1858_);
lean_ctor_set(v_reuseFailAlloc_1869_, 8, v_infoState_1859_);
lean_ctor_set(v_reuseFailAlloc_1869_, 9, v_snapshotTasks_1860_);
v___x_1867_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_st_ref_put(v___y_1838_, v___x_1867_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1838_);
v___y_1810_ = v___y_1834_;
v___y_1811_ = v___y_1835_;
v___y_1812_ = v___y_1836_;
v___y_1813_ = v___y_1837_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1839_;
v___y_1816_ = v___y_1840_;
v___y_1817_ = v___y_1841_;
v___y_1818_ = v___y_1842_;
v___y_1819_ = v___y_1843_;
v___y_1820_ = v___y_1844_;
v___y_1821_ = v___y_1845_;
v___y_1822_ = v___y_1847_;
v___y_1823_ = v___y_1846_;
v___y_1824_ = v___y_1849_;
v___y_1825_ = v___y_1850_;
v___y_1826_ = v___y_1850_;
v___y_1827_ = v___y_1838_;
goto v___jp_1809_;
}
}
}
v___jp_1872_:
{
if (v___y_1885_ == 0)
{
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1877_);
v___y_1810_ = v___y_1873_;
v___y_1811_ = v___y_1874_;
v___y_1812_ = v___y_1875_;
v___y_1813_ = v___y_1876_;
v___y_1814_ = v___y_1877_;
v___y_1815_ = v___y_1878_;
v___y_1816_ = v___y_1879_;
v___y_1817_ = v___y_1880_;
v___y_1818_ = v___y_1881_;
v___y_1819_ = v___y_1882_;
v___y_1820_ = v___y_1883_;
v___y_1821_ = v___y_1884_;
v___y_1822_ = v___y_1886_;
v___y_1823_ = v___y_1887_;
v___y_1824_ = v___y_1889_;
v___y_1825_ = v___y_1888_;
v___y_1826_ = v___y_1888_;
v___y_1827_ = v___y_1877_;
goto v___jp_1809_;
}
else
{
v___y_1834_ = v___y_1873_;
v___y_1835_ = v___y_1874_;
v___y_1836_ = v___y_1875_;
v___y_1837_ = v___y_1876_;
v___y_1838_ = v___y_1877_;
v___y_1839_ = v___y_1878_;
v___y_1840_ = v___y_1879_;
v___y_1841_ = v___y_1880_;
v___y_1842_ = v___y_1881_;
v___y_1843_ = v___y_1882_;
v___y_1844_ = v___y_1883_;
v___y_1845_ = v___y_1884_;
v___y_1846_ = v___y_1887_;
v___y_1847_ = v___y_1886_;
v___y_1848_ = v___y_1890_;
v___y_1849_ = v___y_1889_;
v___y_1850_ = v___y_1888_;
goto v___jp_1833_;
}
}
v___jp_1891_:
{
lean_object* v___x_1911_; lean_object* v_a_1912_; lean_object* v_ref_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; uint16_t v___x_1923_; lean_object* v___x_1924_; lean_object* v_env_1925_; uint8_t v___x_1926_; uint16_t v___x_1927_; uint16_t v___x_1928_; uint16_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1898_);
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v_ref_1913_ = l_Lean_replaceRef(v___y_1909_, v___y_1909_);
lean_inc(v_ref_1913_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1906_);
v___x_1914_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1914_, 0, v___y_1906_);
lean_ctor_set(v___x_1914_, 1, v___y_1903_);
lean_ctor_set(v___x_1914_, 2, v_ref_1913_);
lean_ctor_set_uint16(v___x_1914_, sizeof(void*)*3, v___y_1908_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*3 + 2, v___y_1907_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*3 + 3, v___y_1904_);
v___x_1915_ = l_Lean_MessageData_ofLevel(v___y_1895_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_MessageData_ofLevel(v___y_1897_);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1921_ = 0;
lean_inc_ref(v___y_1901_);
v___x_1922_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1901_, v___x_1920_, v___x_1921_);
v___x_1923_ = l_Lean_OptionFlags_ofOptions(v___x_1922_);
v___x_1924_ = lean_st_ref_get(v___y_1898_);
v_env_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_env_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1925_);
lean_dec_ref(v_env_1925_);
v___x_1927_ = 512;
v___x_1928_ = lean_uint16_land(v___x_1923_, v___x_1927_);
v___x_1929_ = 0;
v___x_1930_ = lean_uint16_dec_eq(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
if (v___y_1896_ == 0)
{
lean_dec(v_ref_1913_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1903_);
v___y_1873_ = v___y_1892_;
v___y_1874_ = v___y_1893_;
v___y_1875_ = v___y_1894_;
v___y_1876_ = v___x_1919_;
v___y_1877_ = v___y_1898_;
v___y_1878_ = v___y_1899_;
v___y_1879_ = v___y_1900_;
v___y_1880_ = v___y_1901_;
v___y_1881_ = v___y_1902_;
v___y_1882_ = v___y_1905_;
v___y_1883_ = v___x_1923_;
v___y_1884_ = v___x_1922_;
v___y_1885_ = v___x_1926_;
v___y_1886_ = v___y_1909_;
v___y_1887_ = v_a_1912_;
v___y_1888_ = v___x_1914_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___y_1896_;
goto v___jp_1872_;
}
else
{
if (v___x_1926_ == 0)
{
lean_dec(v_ref_1913_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1903_);
v___y_1834_ = v___y_1892_;
v___y_1835_ = v___y_1893_;
v___y_1836_ = v___y_1894_;
v___y_1837_ = v___x_1919_;
v___y_1838_ = v___y_1898_;
v___y_1839_ = v___y_1899_;
v___y_1840_ = v___y_1900_;
v___y_1841_ = v___y_1901_;
v___y_1842_ = v___y_1902_;
v___y_1843_ = v___y_1905_;
v___y_1844_ = v___x_1923_;
v___y_1845_ = v___x_1922_;
v___y_1846_ = v_a_1912_;
v___y_1847_ = v___y_1909_;
v___y_1848_ = v___y_1896_;
v___y_1849_ = v___y_1910_;
v___y_1850_ = v___x_1914_;
goto v___jp_1833_;
}
else
{
lean_inc(v___y_1898_);
v___y_1723_ = v___y_1892_;
v___y_1724_ = v___y_1893_;
v___y_1725_ = v___y_1894_;
v___y_1726_ = v___x_1919_;
v___y_1727_ = v___y_1898_;
v___y_1728_ = v___y_1899_;
v___y_1729_ = v___y_1900_;
v___y_1730_ = v___y_1901_;
v___y_1731_ = v___y_1902_;
v___y_1732_ = v___y_1905_;
v___y_1733_ = v___x_1923_;
v___y_1734_ = v___x_1922_;
v___y_1735_ = v___y_1909_;
v___y_1736_ = v_a_1912_;
v___y_1737_ = v___y_1910_;
v___y_1738_ = v___x_1914_;
v_toCold_1739_ = v___y_1906_;
v_currRecDepth_1740_ = v___y_1903_;
v_ref_1741_ = v_ref_1913_;
v_suppressElabErrors_1742_ = v___y_1907_;
v_isRecordingDeps_1743_ = v___y_1904_;
v___y_1744_ = v___y_1898_;
goto v___jp_1722_;
}
}
}
else
{
lean_dec(v_ref_1913_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1903_);
v___y_1873_ = v___y_1892_;
v___y_1874_ = v___y_1893_;
v___y_1875_ = v___y_1894_;
v___y_1876_ = v___x_1919_;
v___y_1877_ = v___y_1898_;
v___y_1878_ = v___y_1899_;
v___y_1879_ = v___y_1900_;
v___y_1880_ = v___y_1901_;
v___y_1881_ = v___y_1902_;
v___y_1882_ = v___y_1905_;
v___y_1883_ = v___x_1923_;
v___y_1884_ = v___x_1922_;
v___y_1885_ = v___x_1926_;
v___y_1886_ = v___y_1909_;
v___y_1887_ = v_a_1912_;
v___y_1888_ = v___x_1914_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___x_1921_;
goto v___jp_1872_;
}
}
v___jp_1931_:
{
lean_object* v_toCold_1938_; lean_object* v_options_1939_; lean_object* v_currRecDepth_1940_; lean_object* v_ref_1941_; uint16_t v_optionFlags_1942_; uint8_t v_suppressElabErrors_1943_; uint8_t v_isRecordingDeps_1944_; lean_object* v_inheritedTraceOptions_1945_; uint8_t v_hasTrace_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___y_1955_; 
v_toCold_1938_ = lean_ctor_get(v___y_1936_, 0);
v_options_1939_ = lean_ctor_get(v_toCold_1938_, 2);
v_currRecDepth_1940_ = lean_ctor_get(v___y_1936_, 1);
v_ref_1941_ = lean_ctor_get(v___y_1936_, 2);
v_optionFlags_1942_ = lean_ctor_get_uint16(v___y_1936_, sizeof(void*)*3);
v_suppressElabErrors_1943_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1944_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3 + 3);
v_inheritedTraceOptions_1945_ = lean_ctor_get(v_toCold_1938_, 11);
v_hasTrace_1946_ = lean_ctor_get_uint8(v_options_1939_, sizeof(void*)*1);
v___x_1947_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1948_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1949_ = l_Lean_Level_getLevelOffset(v_lhs_1932_);
v___x_1950_ = l_Lean_Level_getLevelOffset(v_rhs_1933_);
v___x_1951_ = lean_level_eq(v___x_1949_, v___x_1950_);
lean_dec(v___x_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = 1;
v___x_1953_ = lean_box(v___x_1951_);
v___x_1954_ = lean_box(v___x_1952_);
lean_inc(v_rhs_1933_);
lean_inc(v_lhs_1932_);
v___y_1955_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1955_, 0, v___x_1953_);
lean_closure_set(v___y_1955_, 1, v___x_1947_);
lean_closure_set(v___y_1955_, 2, v___x_1948_);
lean_closure_set(v___y_1955_, 3, v_lhs_1932_);
lean_closure_set(v___y_1955_, 4, v_rhs_1933_);
lean_closure_set(v___y_1955_, 5, v___x_1954_);
if (v_hasTrace_1946_ == 0)
{
lean_object* v___x_1956_; 
lean_dec_ref(v___y_1955_);
v___x_1956_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1951_, v___x_1947_, v___x_1948_, v_lhs_1932_, v_rhs_1933_, v___x_1952_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1957_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1958_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1959_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1945_, v_options_1939_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = l_Lean_trace_profiler;
v___x_1962_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_options_1939_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref(v___y_1955_);
v___x_1963_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1951_, v___x_1947_, v___x_1948_, v_lhs_1932_, v_rhs_1933_, v___x_1952_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v___x_1963_;
}
else
{
lean_inc(v_ref_1941_);
lean_inc(v_currRecDepth_1940_);
lean_inc_ref(v_options_1939_);
lean_inc_ref(v_toCold_1938_);
v___y_1892_ = v___x_1958_;
v___y_1893_ = v___y_1935_;
v___y_1894_ = v___x_1952_;
v___y_1895_ = v_lhs_1932_;
v___y_1896_ = v_hasTrace_1946_;
v___y_1897_ = v_rhs_1933_;
v___y_1898_ = v___y_1937_;
v___y_1899_ = v___y_1955_;
v___y_1900_ = v___y_1934_;
v___y_1901_ = v_options_1939_;
v___y_1902_ = v___x_1960_;
v___y_1903_ = v_currRecDepth_1940_;
v___y_1904_ = v_isRecordingDeps_1944_;
v___y_1905_ = v___y_1936_;
v___y_1906_ = v_toCold_1938_;
v___y_1907_ = v_suppressElabErrors_1943_;
v___y_1908_ = v_optionFlags_1942_;
v___y_1909_ = v_ref_1941_;
v___y_1910_ = v___x_1957_;
goto v___jp_1891_;
}
}
else
{
lean_inc(v_ref_1941_);
lean_inc(v_currRecDepth_1940_);
lean_inc_ref(v_options_1939_);
lean_inc_ref(v_toCold_1938_);
v___y_1892_ = v___x_1958_;
v___y_1893_ = v___y_1935_;
v___y_1894_ = v___x_1952_;
v___y_1895_ = v_lhs_1932_;
v___y_1896_ = v_hasTrace_1946_;
v___y_1897_ = v_rhs_1933_;
v___y_1898_ = v___y_1937_;
v___y_1899_ = v___y_1955_;
v___y_1900_ = v___y_1934_;
v___y_1901_ = v_options_1939_;
v___y_1902_ = v___x_1960_;
v___y_1903_ = v_currRecDepth_1940_;
v___y_1904_ = v_isRecordingDeps_1944_;
v___y_1905_ = v___y_1936_;
v___y_1906_ = v_toCold_1938_;
v___y_1907_ = v_suppressElabErrors_1943_;
v___y_1908_ = v_optionFlags_1942_;
v___y_1909_ = v_ref_1941_;
v___y_1910_ = v___x_1957_;
goto v___jp_1891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = lean_is_level_def_eq(v_x_1967_, v_x_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1976_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_x_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1983_, v_x_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2048_ = 0;
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2050_ = l_Lean_registerTraceClass(v___x_2047_, v___x_2048_, v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref_known(v___x_2050_, 1);
v___x_2051_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2052_ = 1;
v___x_2053_ = l_Lean_registerTraceClass(v___x_2051_, v___x_2052_, v___x_2049_);
return v___x_2053_;
}
else
{
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2055_;
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
