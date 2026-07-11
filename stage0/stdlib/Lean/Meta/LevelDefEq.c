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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
uint8_t l_Lean_Bool_toLBool(uint8_t);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object*);
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
uint8_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_level_eq(v_a_2_, v_lvl_1_);
v___x_8_ = lean_bool_not(v___x_7_);
if (v___x_8_ == 0)
{
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = l_Lean_Level_occurs(v_lvl_1_, v_a_2_);
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
lean_object* v_a_32_; uint8_t v___x_33_; uint8_t v___x_34_; 
v_a_32_ = lean_ctor_get(v_x_26_, 0);
v___x_33_ = l_Lean_instBEqLevelMVarId_beq(v_a_32_, v_mvarId_25_);
v___x_34_ = lean_bool_not(v___x_33_);
if (v___x_34_ == 0)
{
lean_dec_ref_known(v_x_26_, 1);
return v_x_27_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_mkLevelMax_x27(v_x_27_, v_x_26_);
return v___x_35_;
}
}
default: 
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_mkLevelMax_x27(v_x_27_, v_x_26_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* v_mvarId_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_37_, v_x_38_, v_x_39_);
lean_dec(v_mvarId_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object* v_msg_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_1320__overap_49_; lean_object* v___x_50_; 
v___f_48_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_1320__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_42_);
lean_inc(v___y_46_);
lean_inc_ref(v___y_45_);
lean_inc(v___y_44_);
lean_inc_ref(v___y_43_);
v___x_50_ = lean_apply_5(v___x_1320__overap_49_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, lean_box(0));
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_x_58_, lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_ks_62_; lean_object* v_vs_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_87_; 
v_ks_62_ = lean_ctor_get(v_x_58_, 0);
v_vs_63_ = lean_ctor_get(v_x_58_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_87_ == 0)
{
v___x_65_ = v_x_58_;
v_isShared_66_ = v_isSharedCheck_87_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_vs_63_);
lean_inc(v_ks_62_);
lean_dec(v_x_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_87_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_array_get_size(v_ks_62_);
v___x_68_ = lean_nat_dec_lt(v_x_59_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
lean_dec(v_x_59_);
v___x_69_ = lean_array_push(v_ks_62_, v_x_60_);
v___x_70_ = lean_array_push(v_vs_63_, v_x_61_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_70_);
lean_ctor_set(v___x_65_, 0, v___x_69_);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
else
{
lean_object* v_k_x27_74_; uint8_t v___x_75_; 
v_k_x27_74_ = lean_array_fget_borrowed(v_ks_62_, v_x_59_);
v___x_75_ = l_Lean_instBEqLevelMVarId_beq(v_x_60_, v_k_x27_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_77_; 
if (v_isShared_66_ == 0)
{
v___x_77_ = v___x_65_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_ks_62_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_vs_63_);
v___x_77_ = v_reuseFailAlloc_81_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_x_59_, v___x_78_);
lean_dec(v_x_59_);
v_x_58_ = v___x_77_;
v_x_59_ = v___x_79_;
goto _start;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_82_ = lean_array_fset(v_ks_62_, v_x_59_, v_x_60_);
v___x_83_ = lean_array_fset(v_vs_63_, v_x_59_, v_x_61_);
lean_dec(v_x_59_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_83_);
lean_ctor_set(v___x_65_, 0, v___x_82_);
v___x_85_ = v___x_65_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_n_88_, lean_object* v_k_89_, lean_object* v_v_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_n_88_, v___x_91_, v_k_89_, v_v_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(lean_object* v_x_94_, size_t v_x_95_, size_t v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v_es_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v_j_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_es_99_ = lean_ctor_get(v_x_94_, 0);
v___x_100_ = ((size_t)31ULL);
v___x_101_ = lean_usize_land(v_x_95_, v___x_100_);
v_j_102_ = lean_usize_to_nat(v___x_101_);
v___x_103_ = lean_array_get_size(v_es_99_);
v___x_104_ = lean_nat_dec_lt(v_j_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_dec(v_j_102_);
lean_dec(v_x_98_);
lean_dec(v_x_97_);
return v_x_94_;
}
else
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_143_; 
lean_inc_ref(v_es_99_);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v_x_94_, 0);
lean_dec(v_unused_144_);
v___x_106_ = v_x_94_;
v_isShared_107_ = v_isSharedCheck_143_;
goto v_resetjp_105_;
}
else
{
lean_dec(v_x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_143_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_v_108_; lean_object* v___x_109_; lean_object* v_xs_x27_110_; lean_object* v___y_112_; 
v_v_108_ = lean_array_fget(v_es_99_, v_j_102_);
v___x_109_ = lean_box(0);
v_xs_x27_110_ = lean_array_fset(v_es_99_, v_j_102_, v___x_109_);
switch(lean_obj_tag(v_v_108_))
{
case 0:
{
lean_object* v_key_117_; lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_key_117_ = lean_ctor_get(v_v_108_, 0);
v_val_118_ = lean_ctor_get(v_v_108_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_v_108_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_inc(v_key_117_);
lean_dec(v_v_108_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_instBEqLevelMVarId_beq(v_x_97_, v_key_117_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_del_object(v___x_120_);
v___x_123_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_117_, v_val_118_, v_x_97_, v_x_98_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v___y_112_ = v___x_124_;
goto v___jp_111_;
}
else
{
lean_object* v___x_126_; 
lean_dec(v_val_118_);
lean_dec(v_key_117_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v_x_98_);
lean_ctor_set(v___x_120_, 0, v_x_97_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_x_97_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_x_98_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v___y_112_ = v___x_126_;
goto v___jp_111_;
}
}
}
}
case 1:
{
lean_object* v_node_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_141_; 
v_node_129_ = lean_ctor_get(v_v_108_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_141_ == 0)
{
v___x_131_ = v_v_108_;
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_node_129_);
lean_dec(v_v_108_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_133_ = ((size_t)5ULL);
v___x_134_ = lean_usize_shift_right(v_x_95_, v___x_133_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_add(v_x_96_, v___x_135_);
v___x_137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_node_129_, v___x_134_, v___x_136_, v_x_97_, v_x_98_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_137_);
v___x_139_ = v___x_131_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
v___y_112_ = v___x_139_;
goto v___jp_111_;
}
}
}
default: 
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_x_97_);
lean_ctor_set(v___x_142_, 1, v_x_98_);
v___y_112_ = v___x_142_;
goto v___jp_111_;
}
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_array_fset(v_xs_x27_110_, v_j_102_, v___y_112_);
lean_dec(v_j_102_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_113_);
v___x_115_ = v___x_106_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_ks_145_; lean_object* v_vs_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_166_; 
v_ks_145_ = lean_ctor_get(v_x_94_, 0);
v_vs_146_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_166_ == 0)
{
v___x_148_ = v_x_94_;
v_isShared_149_ = v_isSharedCheck_166_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_vs_146_);
lean_inc(v_ks_145_);
lean_dec(v_x_94_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_166_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_ks_145_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_vs_146_);
v___x_151_ = v_reuseFailAlloc_165_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v_newNode_152_; uint8_t v___y_154_; size_t v___x_160_; uint8_t v___x_161_; 
v_newNode_152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v___x_151_, v_x_97_, v_x_98_);
v___x_160_ = ((size_t)7ULL);
v___x_161_ = lean_usize_dec_le(v___x_160_, v_x_96_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_162_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_152_);
v___x_163_ = lean_unsigned_to_nat(4u);
v___x_164_ = lean_nat_dec_lt(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
v___y_154_ = v___x_164_;
goto v___jp_153_;
}
else
{
v___y_154_ = v___x_161_;
goto v___jp_153_;
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
lean_object* v_ks_155_; lean_object* v_vs_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_ks_155_ = lean_ctor_get(v_newNode_152_, 0);
lean_inc_ref(v_ks_155_);
v_vs_156_ = lean_ctor_get(v_newNode_152_, 1);
lean_inc_ref(v_vs_156_);
lean_dec_ref(v_newNode_152_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_x_96_, v_ks_155_, v_vs_156_, v___x_157_, v___x_158_);
lean_dec_ref(v_vs_156_);
lean_dec_ref(v_ks_155_);
return v___x_159_;
}
else
{
return v_newNode_152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(size_t v_depth_167_, lean_object* v_keys_168_, lean_object* v_vals_169_, lean_object* v_i_170_, lean_object* v_entries_171_){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_array_get_size(v_keys_168_);
v___x_173_ = lean_nat_dec_lt(v_i_170_, v___x_172_);
if (v___x_173_ == 0)
{
lean_dec(v_i_170_);
return v_entries_171_;
}
else
{
lean_object* v_k_174_; lean_object* v_v_175_; uint64_t v___x_176_; size_t v_h_177_; size_t v___x_178_; lean_object* v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v_h_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_k_174_ = lean_array_fget_borrowed(v_keys_168_, v_i_170_);
v_v_175_ = lean_array_fget_borrowed(v_vals_169_, v_i_170_);
v___x_176_ = l_Lean_instHashableLevelMVarId_hash(v_k_174_);
v_h_177_ = lean_uint64_to_usize(v___x_176_);
v___x_178_ = ((size_t)5ULL);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_sub(v_depth_167_, v___x_180_);
v___x_182_ = lean_usize_mul(v___x_178_, v___x_181_);
v_h_183_ = lean_usize_shift_right(v_h_177_, v___x_182_);
v___x_184_ = lean_nat_add(v_i_170_, v___x_179_);
lean_dec(v_i_170_);
lean_inc(v_v_175_);
lean_inc(v_k_174_);
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_entries_171_, v_h_183_, v_depth_167_, v_k_174_, v_v_175_);
v_i_170_ = v___x_184_;
v_entries_171_ = v___x_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_187_, lean_object* v_keys_188_, lean_object* v_vals_189_, lean_object* v_i_190_, lean_object* v_entries_191_){
_start:
{
size_t v_depth_boxed_192_; lean_object* v_res_193_; 
v_depth_boxed_192_ = lean_unbox_usize(v_depth_187_);
lean_dec(v_depth_187_);
v_res_193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_boxed_192_, v_keys_188_, v_vals_189_, v_i_190_, v_entries_191_);
lean_dec_ref(v_vals_189_);
lean_dec_ref(v_keys_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_3029__boxed_199_; size_t v_x_3030__boxed_200_; lean_object* v_res_201_; 
v_x_3029__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_x_3030__boxed_200_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_res_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_194_, v_x_3029__boxed_199_, v_x_3030__boxed_200_, v_x_197_, v_x_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
uint64_t v___x_205_; size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; 
v___x_205_ = l_Lean_instHashableLevelMVarId_hash(v_x_203_);
v___x_206_ = lean_uint64_to_usize(v___x_205_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_202_, v___x_206_, v___x_207_, v_x_203_, v_x_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object* v_mvarId_209_, lean_object* v_val_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_mctx_214_; lean_object* v_cache_215_; lean_object* v_zetaDeltaFVarIds_216_; lean_object* v_postponed_217_; lean_object* v_diag_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_246_; 
v___x_213_ = lean_st_ref_take(v___y_211_);
v_mctx_214_ = lean_ctor_get(v___x_213_, 0);
v_cache_215_ = lean_ctor_get(v___x_213_, 1);
v_zetaDeltaFVarIds_216_ = lean_ctor_get(v___x_213_, 2);
v_postponed_217_ = lean_ctor_get(v___x_213_, 3);
v_diag_218_ = lean_ctor_get(v___x_213_, 4);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_246_ == 0)
{
v___x_220_ = v___x_213_;
v_isShared_221_ = v_isSharedCheck_246_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_diag_218_);
lean_inc(v_postponed_217_);
lean_inc(v_zetaDeltaFVarIds_216_);
lean_inc(v_cache_215_);
lean_inc(v_mctx_214_);
lean_dec(v___x_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_246_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_depth_222_; lean_object* v_levelAssignDepth_223_; lean_object* v_lmvarCounter_224_; lean_object* v_mvarCounter_225_; lean_object* v_lDecls_226_; lean_object* v_decls_227_; lean_object* v_userNames_228_; lean_object* v_lAssignment_229_; lean_object* v_eAssignment_230_; lean_object* v_dAssignment_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_245_; 
v_depth_222_ = lean_ctor_get(v_mctx_214_, 0);
v_levelAssignDepth_223_ = lean_ctor_get(v_mctx_214_, 1);
v_lmvarCounter_224_ = lean_ctor_get(v_mctx_214_, 2);
v_mvarCounter_225_ = lean_ctor_get(v_mctx_214_, 3);
v_lDecls_226_ = lean_ctor_get(v_mctx_214_, 4);
v_decls_227_ = lean_ctor_get(v_mctx_214_, 5);
v_userNames_228_ = lean_ctor_get(v_mctx_214_, 6);
v_lAssignment_229_ = lean_ctor_get(v_mctx_214_, 7);
v_eAssignment_230_ = lean_ctor_get(v_mctx_214_, 8);
v_dAssignment_231_ = lean_ctor_get(v_mctx_214_, 9);
v_isSharedCheck_245_ = !lean_is_exclusive(v_mctx_214_);
if (v_isSharedCheck_245_ == 0)
{
v___x_233_ = v_mctx_214_;
v_isShared_234_ = v_isSharedCheck_245_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_dAssignment_231_);
lean_inc(v_eAssignment_230_);
lean_inc(v_lAssignment_229_);
lean_inc(v_userNames_228_);
lean_inc(v_decls_227_);
lean_inc(v_lDecls_226_);
lean_inc(v_mvarCounter_225_);
lean_inc(v_lmvarCounter_224_);
lean_inc(v_levelAssignDepth_223_);
lean_inc(v_depth_222_);
lean_dec(v_mctx_214_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_245_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_229_, v_mvarId_209_, v_val_210_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 7, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_depth_222_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_levelAssignDepth_223_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_lmvarCounter_224_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_mvarCounter_225_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v_lDecls_226_);
lean_ctor_set(v_reuseFailAlloc_244_, 5, v_decls_227_);
lean_ctor_set(v_reuseFailAlloc_244_, 6, v_userNames_228_);
lean_ctor_set(v_reuseFailAlloc_244_, 7, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 8, v_eAssignment_230_);
lean_ctor_set(v_reuseFailAlloc_244_, 9, v_dAssignment_231_);
v___x_237_ = v_reuseFailAlloc_244_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_237_);
v___x_239_ = v___x_220_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_cache_215_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_zetaDeltaFVarIds_216_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_postponed_217_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_diag_218_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_st_ref_set(v___y_211_, v___x_239_);
v___x_241_ = lean_box(0);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* v_mvarId_247_, lean_object* v_val_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_247_, v_val_248_, v___y_249_);
lean_dec(v___y_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(lean_object* v_msgData_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_env_259_; lean_object* v___x_260_; lean_object* v_mctx_261_; lean_object* v_lctx_262_; lean_object* v_options_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_258_ = lean_st_ref_get(v___y_256_);
v_env_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_258_);
v___x_260_ = lean_st_ref_get(v___y_254_);
v_mctx_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_mctx_261_);
lean_dec(v___x_260_);
v_lctx_262_ = lean_ctor_get(v___y_253_, 2);
v_options_263_ = lean_ctor_get(v___y_255_, 2);
lean_inc_ref(v_options_263_);
lean_inc_ref(v_lctx_262_);
v___x_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_264_, 0, v_env_259_);
lean_ctor_set(v___x_264_, 1, v_mctx_261_);
lean_ctor_set(v___x_264_, 2, v_lctx_262_);
lean_ctor_set(v___x_264_, 3, v_options_263_);
v___x_265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_msgData_252_);
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
lean_object* v_ref_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_332_; 
v_ref_286_ = lean_ctor_get(v___y_283_, 5);
v___x_287_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_332_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_332_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_332_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v_traceState_293_; lean_object* v_env_294_; lean_object* v_nextMacroScope_295_; lean_object* v_ngen_296_; lean_object* v_auxDeclNGen_297_; lean_object* v_cache_298_; lean_object* v_messages_299_; lean_object* v_infoState_300_; lean_object* v_snapshotTasks_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_331_; 
v___x_292_ = lean_st_ref_take(v___y_284_);
v_traceState_293_ = lean_ctor_get(v___x_292_, 4);
v_env_294_ = lean_ctor_get(v___x_292_, 0);
v_nextMacroScope_295_ = lean_ctor_get(v___x_292_, 1);
v_ngen_296_ = lean_ctor_get(v___x_292_, 2);
v_auxDeclNGen_297_ = lean_ctor_get(v___x_292_, 3);
v_cache_298_ = lean_ctor_get(v___x_292_, 5);
v_messages_299_ = lean_ctor_get(v___x_292_, 6);
v_infoState_300_ = lean_ctor_get(v___x_292_, 7);
v_snapshotTasks_301_ = lean_ctor_get(v___x_292_, 8);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_331_ == 0)
{
v___x_303_ = v___x_292_;
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snapshotTasks_301_);
lean_inc(v_infoState_300_);
lean_inc(v_messages_299_);
lean_inc(v_cache_298_);
lean_inc(v_traceState_293_);
lean_inc(v_auxDeclNGen_297_);
lean_inc(v_ngen_296_);
lean_inc(v_nextMacroScope_295_);
lean_inc(v_env_294_);
lean_dec(v___x_292_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
uint64_t v_tid_305_; lean_object* v_traces_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_330_; 
v_tid_305_ = lean_ctor_get_uint64(v_traceState_293_, sizeof(void*)*1);
v_traces_306_ = lean_ctor_get(v_traceState_293_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_traceState_293_);
if (v_isSharedCheck_330_ == 0)
{
v___x_308_ = v_traceState_293_;
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_traces_306_);
lean_dec(v_traceState_293_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; double v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_312_ = 0;
v___x_313_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_314_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_314_, 0, v_cls_279_);
lean_ctor_set(v___x_314_, 1, v___x_310_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_ctor_set_float(v___x_314_, sizeof(void*)*3, v___x_311_);
lean_ctor_set_float(v___x_314_, sizeof(void*)*3 + 8, v___x_311_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*3 + 16, v___x_312_);
v___x_315_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_316_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v_a_288_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
lean_inc(v_ref_286_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_ref_286_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_PersistentArray_push___redArg(v_traces_306_, v___x_317_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_318_);
v___x_320_ = v___x_308_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_318_);
lean_ctor_set_uint64(v_reuseFailAlloc_329_, sizeof(void*)*1, v_tid_305_);
v___x_320_ = v_reuseFailAlloc_329_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 4, v___x_320_);
v___x_322_ = v___x_303_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_env_294_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_nextMacroScope_295_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_ngen_296_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_auxDeclNGen_297_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_cache_298_);
lean_ctor_set(v_reuseFailAlloc_328_, 6, v_messages_299_);
lean_ctor_set(v_reuseFailAlloc_328_, 7, v_infoState_300_);
lean_ctor_set(v_reuseFailAlloc_328_, 8, v_snapshotTasks_301_);
v___x_322_ = v_reuseFailAlloc_328_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_st_ref_set(v___y_284_, v___x_322_);
v___x_324_ = lean_box(0);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_324_);
v___x_326_ = v___x_290_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
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
lean_object* v_options_380_; lean_object* v_a_381_; lean_object* v_inheritedTraceOptions_382_; uint8_t v_hasTrace_383_; lean_object* v___x_384_; 
v_options_380_ = lean_ctor_get(v_a_373_, 2);
v_a_381_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_379_, 1);
v_inheritedTraceOptions_382_ = lean_ctor_get(v_a_373_, 13);
v_hasTrace_383_ = lean_ctor_get_uint8(v_options_380_, sizeof(void*)*1);
v___x_384_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_369_, v_v_370_, v_a_381_);
if (v_hasTrace_383_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_369_, v___x_384_, v_a_372_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_387_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_388_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_382_, v_options_380_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_369_, v___x_384_, v_a_372_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_369_);
v___x_391_ = l_Lean_mkLevelMVar(v_mvarId_369_);
v___x_392_ = l_Lean_MessageData_ofLevel(v___x_391_);
v___x_393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_390_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_inc(v___x_384_);
v___x_396_ = l_Lean_MessageData_ofLevel(v___x_384_);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_386_, v___x_397_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_369_, v___x_384_, v_a_372_);
return v___x_399_;
}
else
{
lean_dec(v___x_384_);
lean_dec(v_mvarId_369_);
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_v_370_);
lean_dec(v_mvarId_369_);
v_a_400_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_379_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_379_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_408_, lean_object* v_v_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_408_, v_v_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_416_, lean_object* v_val_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_416_, v_val_417_, v___y_419_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_424_, lean_object* v_val_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_424_, v_val_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_433_, v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_437_, lean_object* v_x_438_, size_t v_x_439_, size_t v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_438_, v_x_439_, v_x_440_, v_x_441_, v_x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
size_t v_x_3541__boxed_450_; size_t v_x_3542__boxed_451_; lean_object* v_res_452_; 
v_x_3541__boxed_450_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_x_3542__boxed_451_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_res_452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_444_, v_x_445_, v_x_3541__boxed_450_, v_x_3542__boxed_451_, v_x_448_, v_x_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_453_, lean_object* v_n_454_, lean_object* v_k_455_, lean_object* v_v_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_454_, v_k_455_, v_v_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_458_, size_t v_depth_459_, lean_object* v_keys_460_, lean_object* v_vals_461_, lean_object* v_heq_462_, lean_object* v_i_463_, lean_object* v_entries_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_459_, v_keys_460_, v_vals_461_, v_i_463_, v_entries_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_466_, lean_object* v_depth_467_, lean_object* v_keys_468_, lean_object* v_vals_469_, lean_object* v_heq_470_, lean_object* v_i_471_, lean_object* v_entries_472_){
_start:
{
size_t v_depth_boxed_473_; lean_object* v_res_474_; 
v_depth_boxed_473_ = lean_unbox_usize(v_depth_467_);
lean_dec(v_depth_467_);
v_res_474_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_466_, v_depth_boxed_473_, v_keys_468_, v_vals_469_, v_heq_470_, v_i_471_, v_entries_472_);
lean_dec_ref(v_vals_469_);
lean_dec_ref(v_keys_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_476_, v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_484_, lean_object* v_v_x27_485_, lean_object* v_mvarId_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
uint8_t v___x_492_; lean_object* v___y_494_; 
v___x_492_ = lean_level_eq(v_u_484_, v_v_x27_485_);
if (v___x_492_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_mvarId_486_);
lean_dec(v_u_484_);
v___x_505_ = lean_box(v___x_492_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v_options_507_; uint8_t v_hasTrace_508_; 
v_options_507_ = lean_ctor_get(v_a_489_, 2);
v_hasTrace_508_ = lean_ctor_get_uint8(v_options_507_, sizeof(void*)*1);
if (v_hasTrace_508_ == 0)
{
v___y_494_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_inheritedTraceOptions_509_; lean_object* v_cls_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_inheritedTraceOptions_509_ = lean_ctor_get(v_a_489_, 13);
v_cls_510_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_511_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_509_, v_options_507_, v___x_511_);
if (v___x_512_ == 0)
{
v___y_494_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_513_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_486_);
v___x_514_ = l_Lean_mkLevelMVar(v_mvarId_486_);
v___x_515_ = l_Lean_MessageData_ofLevel(v___x_514_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
lean_inc(v_u_484_);
v___x_519_ = l_Lean_MessageData_ofLevel(v_u_484_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_510_, v___x_520_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_dec_ref_known(v___x_521_, 1);
v___y_494_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_mvarId_486_);
lean_dec(v_u_484_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v___x_495_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_486_, v_u_484_, v___y_494_);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v___x_495_, 0);
lean_dec(v_unused_504_);
v___x_497_ = v___x_495_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_dec(v___x_495_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_box(v___x_492_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_530_, lean_object* v_v_x27_531_, lean_object* v_mvarId_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_530_, v_v_x27_531_, v_mvarId_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_v_x27_531_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_539_, lean_object* v_v_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
if (lean_obj_tag(v_v_540_) == 2)
{
lean_object* v_a_550_; 
v_a_550_ = lean_ctor_get(v_v_540_, 1);
lean_inc(v_a_550_);
if (lean_obj_tag(v_a_550_) == 5)
{
lean_object* v_a_551_; lean_object* v_a_552_; lean_object* v___x_553_; 
v_a_551_ = lean_ctor_get(v_v_540_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_v_540_, 2);
v_a_552_ = lean_ctor_get(v_a_550_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v_a_550_, 1);
v___x_553_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_539_, v_a_551_, v_a_552_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_551_);
return v___x_553_;
}
else
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v_v_540_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v_v_540_, 2);
if (lean_obj_tag(v_a_554_) == 5)
{
lean_object* v_a_555_; lean_object* v___x_556_; 
v_a_555_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v_a_554_, 1);
v___x_556_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_539_, v_a_550_, v_a_555_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_550_);
return v___x_556_;
}
else
{
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_u_539_);
goto v___jp_546_;
}
}
}
else
{
lean_dec(v_v_540_);
lean_dec(v_u_539_);
goto v___jp_546_;
}
v___jp_546_:
{
uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = 0;
v___x_548_ = lean_box(v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_557_, lean_object* v_v_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_557_, v_v_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_564_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_568_, lean_object* v_u_u2082_569_, lean_object* v_v_x27_570_, lean_object* v_mvarId_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v___x_577_; uint8_t v___x_578_; lean_object* v___y_580_; lean_object* v___y_592_; 
v___x_577_ = lean_level_eq(v_u_u2081_568_, v_v_x27_570_);
v___x_578_ = 1;
if (v___x_577_ == 0)
{
uint8_t v___x_603_; 
v___x_603_ = lean_level_eq(v_u_u2082_569_, v_v_x27_570_);
lean_dec(v_u_u2082_569_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v_mvarId_571_);
lean_dec(v_u_u2081_568_);
v___x_604_ = lean_box(v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
else
{
lean_object* v_options_606_; uint8_t v_hasTrace_607_; 
v_options_606_ = lean_ctor_get(v_a_574_, 2);
v_hasTrace_607_ = lean_ctor_get_uint8(v_options_606_, sizeof(void*)*1);
if (v_hasTrace_607_ == 0)
{
v___y_592_ = v_a_573_;
goto v___jp_591_;
}
else
{
lean_object* v_inheritedTraceOptions_608_; lean_object* v_cls_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_inheritedTraceOptions_608_ = lean_ctor_get(v_a_574_, 13);
v_cls_609_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_610_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_611_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_608_, v_options_606_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_592_ = v_a_573_;
goto v___jp_591_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_571_);
v___x_613_ = l_Lean_mkLevelMVar(v_mvarId_571_);
v___x_614_ = l_Lean_MessageData_ofLevel(v___x_613_);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_612_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_inc(v_u_u2081_568_);
v___x_618_ = l_Lean_MessageData_ofLevel(v_u_u2081_568_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_609_, v___x_619_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec_ref_known(v___x_620_, 1);
v___y_592_ = v_a_573_;
goto v___jp_591_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_mvarId_571_);
lean_dec(v_u_u2081_568_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_629_; uint8_t v_hasTrace_630_; 
lean_dec(v_u_u2081_568_);
v_options_629_ = lean_ctor_get(v_a_574_, 2);
v_hasTrace_630_ = lean_ctor_get_uint8(v_options_629_, sizeof(void*)*1);
if (v_hasTrace_630_ == 0)
{
v___y_580_ = v_a_573_;
goto v___jp_579_;
}
else
{
lean_object* v_inheritedTraceOptions_631_; lean_object* v_cls_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_inheritedTraceOptions_631_ = lean_ctor_get(v_a_574_, 13);
v_cls_632_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_633_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_631_, v_options_629_, v___x_633_);
if (v___x_634_ == 0)
{
v___y_580_ = v_a_573_;
goto v___jp_579_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_635_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_571_);
v___x_636_ = l_Lean_mkLevelMVar(v_mvarId_571_);
v___x_637_ = l_Lean_MessageData_ofLevel(v___x_636_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_inc(v_u_u2082_569_);
v___x_641_ = l_Lean_MessageData_ofLevel(v_u_u2082_569_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_632_, v___x_642_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref_known(v___x_643_, 1);
v___y_580_ = v_a_573_;
goto v___jp_579_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_mvarId_571_);
lean_dec(v_u_u2082_569_);
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v___x_581_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_571_, v_u_u2082_569_, v___y_580_);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_590_);
v___x_583_ = v___x_581_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_dec(v___x_581_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_box(v___x_578_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
v___jp_591_:
{
lean_object* v___x_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v___x_593_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_571_, v_u_u2081_568_, v___y_592_);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_602_);
v___x_595_ = v___x_593_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_dec(v___x_593_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_box(v___x_578_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_652_, lean_object* v_u_u2082_653_, lean_object* v_v_x27_654_, lean_object* v_mvarId_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_652_, v_u_u2082_653_, v_v_x27_654_, v_mvarId_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_v_x27_654_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_662_, lean_object* v_v_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
if (lean_obj_tag(v_u_662_) == 2)
{
if (lean_obj_tag(v_v_663_) == 2)
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v_v_663_, 1);
lean_inc(v_a_673_);
if (lean_obj_tag(v_a_673_) == 5)
{
lean_object* v_a_674_; lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_674_ = lean_ctor_get(v_u_662_, 0);
lean_inc(v_a_674_);
v_a_675_ = lean_ctor_get(v_u_662_, 1);
lean_inc(v_a_675_);
lean_dec_ref_known(v_u_662_, 2);
v_a_676_ = lean_ctor_get(v_v_663_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v_v_663_, 2);
v_a_677_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v_a_673_, 1);
v___x_678_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_676_);
return v___x_678_;
}
else
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v_v_663_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v_v_663_, 2);
if (lean_obj_tag(v_a_679_) == 5)
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_680_ = lean_ctor_get(v_u_662_, 0);
lean_inc(v_a_680_);
v_a_681_ = lean_ctor_get(v_u_662_, 1);
lean_inc(v_a_681_);
lean_dec_ref_known(v_u_662_, 2);
v_a_682_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v_a_679_, 1);
v___x_683_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_680_, v_a_681_, v_a_673_, v_a_682_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_673_);
return v___x_683_;
}
else
{
lean_dec(v_a_679_);
lean_dec(v_a_673_);
lean_dec_ref_known(v_u_662_, 2);
goto v___jp_669_;
}
}
}
else
{
lean_dec_ref_known(v_u_662_, 2);
lean_dec(v_v_663_);
goto v___jp_669_;
}
}
else
{
lean_dec(v_v_663_);
lean_dec(v_u_662_);
goto v___jp_669_;
}
v___jp_669_:
{
uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = 0;
v___x_671_ = lean_box(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_684_, lean_object* v_v_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_684_, v_v_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_699_ = l_Lean_Name_append(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_703_, lean_object* v_rhs_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_options_710_; lean_object* v_ref_711_; lean_object* v_inheritedTraceOptions_712_; lean_object* v___y_714_; uint8_t v_hasTrace_734_; 
v_options_710_ = lean_ctor_get(v_a_707_, 2);
v_ref_711_ = lean_ctor_get(v_a_707_, 5);
v_inheritedTraceOptions_712_ = lean_ctor_get(v_a_707_, 13);
v_hasTrace_734_ = lean_ctor_get_uint8(v_options_710_, sizeof(void*)*1);
if (v_hasTrace_734_ == 0)
{
v___y_714_ = v_a_706_;
goto v___jp_713_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_736_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_712_, v_options_710_, v___x_736_);
if (v___x_737_ == 0)
{
v___y_714_ = v_a_706_;
goto v___jp_713_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_inc(v_lhs_703_);
v___x_738_ = l_Lean_MessageData_ofLevel(v_lhs_703_);
v___x_739_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_inc(v_rhs_704_);
v___x_741_ = l_Lean_MessageData_ofLevel(v_rhs_704_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_735_, v___x_742_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref_known(v___x_743_, 1);
v___y_714_ = v_a_706_;
goto v___jp_713_;
}
else
{
lean_dec(v_rhs_704_);
lean_dec(v_lhs_703_);
return v___x_743_;
}
}
}
v___jp_713_:
{
lean_object* v___x_715_; lean_object* v_mctx_716_; lean_object* v_cache_717_; lean_object* v_zetaDeltaFVarIds_718_; lean_object* v_postponed_719_; lean_object* v_diag_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_733_; 
v___x_715_ = lean_st_ref_take(v___y_714_);
v_mctx_716_ = lean_ctor_get(v___x_715_, 0);
v_cache_717_ = lean_ctor_get(v___x_715_, 1);
v_zetaDeltaFVarIds_718_ = lean_ctor_get(v___x_715_, 2);
v_postponed_719_ = lean_ctor_get(v___x_715_, 3);
v_diag_720_ = lean_ctor_get(v___x_715_, 4);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_722_ = v___x_715_;
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_diag_720_);
lean_inc(v_postponed_719_);
lean_inc(v_zetaDeltaFVarIds_718_);
lean_inc(v_cache_717_);
lean_inc(v_mctx_716_);
lean_dec(v___x_715_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_defEqCtx_x3f_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_defEqCtx_x3f_724_ = lean_ctor_get(v_a_705_, 4);
lean_inc(v_defEqCtx_x3f_724_);
lean_inc(v_ref_711_);
v___x_725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_725_, 0, v_ref_711_);
lean_ctor_set(v___x_725_, 1, v_lhs_703_);
lean_ctor_set(v___x_725_, 2, v_rhs_704_);
lean_ctor_set(v___x_725_, 3, v_defEqCtx_x3f_724_);
v___x_726_ = l_Lean_PersistentArray_push___redArg(v_postponed_719_, v___x_725_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 3, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_mctx_716_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_cache_717_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_zetaDeltaFVarIds_718_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_diag_720_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_st_ref_set(v___y_714_, v___x_728_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_744_, lean_object* v_rhs_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_744_, v_rhs_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_752_, lean_object* v_mvarId_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
if (lean_obj_tag(v_v_752_) == 5)
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v_v_752_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v_v_752_, 1);
v___x_760_ = l_Lean_LMVarId_getLevel(v_a_759_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = l_Lean_LMVarId_getLevel(v_mvarId_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_772_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_772_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = lean_nat_dec_lt(v_a_763_, v_a_761_);
lean_dec(v_a_761_);
lean_dec(v_a_763_);
v___x_768_ = lean_box(v___x_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_761_);
v_a_773_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_762_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_762_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_mvarId_753_);
v_a_781_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_760_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_760_);
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
uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v_mvarId_753_);
lean_dec(v_v_752_);
v___x_789_ = 0;
v___x_790_ = lean_box(v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_792_, lean_object* v_mvarId_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_792_, v_mvarId_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_800_, lean_object* v_v_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___y_808_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_883_; lean_object* v___y_897_; 
switch(lean_obj_tag(v_u_800_))
{
case 5:
{
lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_910_ = lean_ctor_get(v_u_800_, 0);
lean_inc(v_a_910_);
v___x_911_ = l_Lean_LMVarId_isReadOnly(v_a_910_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_1009_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_1009_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_1009_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
uint8_t v___x_916_; 
v___x_916_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_del_object(v___x_914_);
lean_inc(v_a_910_);
lean_inc(v_v_801_);
v___x_917_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_801_, v_a_910_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_995_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_995_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_995_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_995_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v___y_923_; uint8_t v___x_949_; 
v___x_949_ = lean_unbox(v_a_918_);
lean_dec(v_a_918_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = l_Lean_Level_occurs(v_u_800_, v_v_801_);
v___x_951_ = lean_bool_not(v___x_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; 
v___x_952_ = l_Lean_Level_isMax(v_v_801_);
if (v___x_952_ == 0)
{
v___y_923_ = v___x_952_;
goto v___jp_922_;
}
else
{
uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_953_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_800_, v_v_801_);
v___x_954_ = lean_bool_not(v___x_953_);
v___y_923_ = v___x_954_;
goto v___jp_922_;
}
}
else
{
lean_object* v_options_955_; uint8_t v_hasTrace_956_; 
lean_del_object(v___x_920_);
v_options_955_ = lean_ctor_get(v_a_804_, 2);
v_hasTrace_956_ = lean_ctor_get_uint8(v_options_955_, sizeof(void*)*1);
if (v_hasTrace_956_ == 0)
{
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_a_802_);
v___y_883_ = v_a_803_;
goto v___jp_882_;
}
else
{
lean_object* v_inheritedTraceOptions_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_inheritedTraceOptions_957_ = lean_ctor_get(v_a_804_, 13);
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_957_, v_options_955_, v___x_959_);
if (v___x_960_ == 0)
{
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_a_802_);
v___y_883_ = v_a_803_;
goto v___jp_882_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_inc_ref(v_u_800_);
v___x_961_ = l_Lean_MessageData_ofLevel(v_u_800_);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
lean_inc(v_v_801_);
v___x_964_ = l_Lean_MessageData_ofLevel(v_v_801_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_958_, v___x_965_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_a_802_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_dec_ref_known(v___x_966_, 1);
v___y_883_ = v_a_803_;
goto v___jp_882_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref_known(v_u_800_, 1);
lean_dec(v_a_803_);
lean_dec(v_v_801_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_975_; uint8_t v_hasTrace_976_; 
lean_del_object(v___x_920_);
v_options_975_ = lean_ctor_get(v_a_804_, 2);
v_hasTrace_976_ = lean_ctor_get_uint8(v_options_975_, sizeof(void*)*1);
if (v_hasTrace_976_ == 0)
{
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_a_802_);
v___y_897_ = v_a_803_;
goto v___jp_896_;
}
else
{
lean_object* v_inheritedTraceOptions_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_inheritedTraceOptions_977_ = lean_ctor_get(v_a_804_, 13);
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_979_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_977_, v_options_975_, v___x_979_);
if (v___x_980_ == 0)
{
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_a_802_);
v___y_897_ = v_a_803_;
goto v___jp_896_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
lean_inc(v_v_801_);
v___x_981_ = l_Lean_MessageData_ofLevel(v_v_801_);
v___x_982_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
lean_inc_ref(v_u_800_);
v___x_984_ = l_Lean_MessageData_ofLevel(v_u_800_);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_978_, v___x_985_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_a_802_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_dec_ref_known(v___x_986_, 1);
v___y_897_ = v_a_803_;
goto v___jp_896_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref_known(v_u_800_, 1);
lean_dec(v_a_803_);
lean_dec(v_v_801_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
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
}
}
v___jp_922_:
{
if (v___y_923_ == 0)
{
uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec_ref_known(v_u_800_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_v_801_);
v___x_924_ = 2;
v___x_925_ = lean_box(v___x_924_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_925_);
v___x_927_ = v___x_920_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_del_object(v___x_920_);
v___x_929_ = l_Lean_Level_mvarId_x21(v_u_800_);
lean_dec_ref_known(v_u_800_, 1);
v___x_930_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_929_, v_v_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_939_; 
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_940_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = 1;
v___x_935_ = lean_box(v___x_934_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_930_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_930_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref_known(v_u_800_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_v_801_);
v_a_996_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_917_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_917_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_dec_ref_known(v_u_800_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_v_801_);
v___x_1004_ = 2;
v___x_1005_ = lean_box(v___x_1004_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_1005_);
v___x_1007_ = v___x_914_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref_known(v_u_800_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_v_801_);
v_a_1010_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_911_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_911_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_801_))
{
case 5:
{
lean_dec_ref_known(v_v_801_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
goto v___jp_828_;
}
case 2:
{
lean_object* v_a_1018_; lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1018_ = lean_ctor_get(v_v_801_, 0);
lean_inc(v_a_1018_);
v_a_1019_ = lean_ctor_get(v_v_801_, 1);
lean_inc(v_a_1019_);
lean_dec_ref_known(v_v_801_, 2);
lean_inc(v_a_805_);
lean_inc_ref(v_a_804_);
lean_inc(v_a_803_);
lean_inc_ref(v_a_802_);
v___x_1020_ = lean_is_level_def_eq(v_u_800_, v_a_1018_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; uint8_t v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
v___x_1022_ = lean_unbox(v_a_1021_);
lean_dec(v_a_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v_a_1019_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
v___y_808_ = v___x_1020_;
goto v___jp_807_;
}
else
{
lean_object* v___x_1023_; 
lean_dec_ref_known(v___x_1020_, 1);
v___x_1023_ = lean_is_level_def_eq(v_u_800_, v_a_1019_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
v___y_808_ = v___x_1023_;
goto v___jp_807_;
}
}
else
{
lean_dec(v_a_1019_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
v___y_808_ = v___x_1020_;
goto v___jp_807_;
}
}
case 3:
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v_v_801_, 1);
lean_inc(v_a_1024_);
lean_dec_ref_known(v_v_801_, 2);
v___x_1025_ = lean_is_level_def_eq(v_u_800_, v_a_1024_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1036_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
uint8_t v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1030_ = lean_unbox(v_a_1026_);
lean_dec(v_a_1026_);
v___x_1031_ = l_Lean_Bool_toLBool(v___x_1030_);
v___x_1032_ = lean_box(v___x_1031_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1032_);
v___x_1034_ = v___x_1028_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1025_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1025_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
case 1:
{
uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref_known(v_v_801_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
v___x_1045_ = 0;
v___x_1046_ = lean_box(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
default: 
{
v___y_837_ = v_a_802_;
v___y_838_ = v_a_803_;
v___y_839_ = v_a_804_;
v___y_840_ = v_a_805_;
goto v___jp_836_;
}
}
}
case 1:
{
lean_object* v_a_1048_; uint8_t v___y_1050_; 
v_a_1048_ = lean_ctor_get(v_u_800_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v_u_800_, 1);
if (lean_obj_tag(v_v_801_) == 5)
{
lean_dec_ref_known(v_v_801_, 1);
lean_dec(v_a_1048_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
goto v___jp_828_;
}
else
{
uint8_t v___x_1094_; 
v___x_1094_ = l_Lean_Level_isParam(v_v_801_);
if (v___x_1094_ == 0)
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Lean_Level_isMVar(v_a_1048_);
if (v___x_1095_ == 0)
{
v___y_1050_ = v___x_1095_;
goto v___jp_1049_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_Level_occurs(v_a_1048_, v_v_801_);
v___y_1050_ = v___x_1096_;
goto v___jp_1049_;
}
}
else
{
uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v_a_1048_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_v_801_);
v___x_1097_ = 0;
v___x_1098_ = lean_box(v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
v___jp_1049_:
{
if (v___y_1050_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_Meta_decLevel_x3f(v_v_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1082_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1082_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1082_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
if (lean_obj_tag(v_a_1052_) == 0)
{
uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_a_1048_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
v___x_1056_ = 2;
v___x_1057_ = lean_box(v___x_1056_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
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
else
{
lean_object* v_val_1061_; lean_object* v___x_1062_; 
lean_del_object(v___x_1054_);
v_val_1061_ = lean_ctor_get(v_a_1052_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v_a_1052_, 1);
v___x_1062_ = lean_is_level_def_eq(v_a_1048_, v_val_1061_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1073_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1067_ = lean_unbox(v_a_1063_);
lean_dec(v_a_1063_);
v___x_1068_ = l_Lean_Bool_toLBool(v___x_1067_);
v___x_1069_ = lean_box(v___x_1068_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1062_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1062_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_1048_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
v_a_1083_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1051_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1051_);
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
else
{
uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v_a_1048_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_v_801_);
v___x_1091_ = 2;
v___x_1092_ = lean_box(v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_801_) == 5)
{
lean_dec_ref_known(v_v_801_, 1);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_u_800_);
goto v___jp_828_;
}
else
{
v___y_837_ = v_a_802_;
v___y_838_ = v_a_803_;
v___y_839_ = v_a_804_;
v___y_840_ = v_a_805_;
goto v___jp_836_;
}
}
}
v___jp_807_:
{
if (lean_obj_tag(v___y_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_a_809_ = lean_ctor_get(v___y_808_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___y_808_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v___y_808_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___y_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_813_ = lean_unbox(v_a_809_);
lean_dec(v_a_809_);
v___x_814_ = l_Lean_Bool_toLBool(v___x_813_);
v___x_815_ = lean_box(v___x_814_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_a_820_ = lean_ctor_get(v___y_808_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___y_808_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___y_808_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___y_808_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
v___jp_828_:
{
uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = 2;
v___x_830_ = lean_box(v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
v___jp_832_:
{
uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = 2;
v___x_834_ = lean_box(v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
v___jp_836_:
{
uint8_t v_univApprox_841_; 
v_univApprox_841_ = lean_ctor_get_uint8(v___y_837_, sizeof(void*)*7 + 1);
if (v_univApprox_841_ == 0)
{
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v_v_801_);
lean_dec(v_u_800_);
goto v___jp_832_;
}
else
{
lean_object* v___x_842_; 
lean_inc(v_v_801_);
lean_inc(v_u_800_);
v___x_842_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_800_, v_v_801_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_873_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_873_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_873_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_873_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___x_847_; 
v___x_847_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_del_object(v___x_845_);
v___x_848_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_800_, v_v_801_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_859_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
uint8_t v___x_853_; 
v___x_853_ = lean_unbox(v_a_849_);
lean_dec(v_a_849_);
if (v___x_853_ == 0)
{
lean_del_object(v___x_851_);
goto v___jp_832_;
}
else
{
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = 1;
v___x_855_ = lean_box(v___x_854_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_855_);
v___x_857_ = v___x_851_;
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
v_a_860_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_848_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_848_);
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
else
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v_v_801_);
lean_dec(v_u_800_);
v___x_868_ = 1;
v___x_869_ = lean_box(v___x_868_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_869_);
v___x_871_ = v___x_845_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
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
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v_v_801_);
lean_dec(v_u_800_);
v_a_874_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_842_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_842_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
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
}
v___jp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
v___x_884_ = l_Lean_Level_mvarId_x21(v_u_800_);
lean_dec(v_u_800_);
v___x_885_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_884_, v_v_801_, v___y_883_);
lean_dec(v___y_883_);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_885_, 0);
lean_dec(v_unused_895_);
v___x_887_ = v___x_885_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_dec(v___x_885_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = 1;
v___x_890_ = lean_box(v___x_889_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
v___jp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_908_; 
v___x_898_ = l_Lean_Level_mvarId_x21(v_v_801_);
lean_dec(v_v_801_);
v___x_899_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_898_, v_u_800_, v___y_897_);
lean_dec(v___y_897_);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_909_);
v___x_901_ = v___x_899_;
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
else
{
lean_dec(v___x_899_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_903_ = 1;
v___x_904_ = lean_box(v___x_903_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_904_);
v___x_906_ = v___x_901_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1100_, lean_object* v_v_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1100_, v_v_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_mctx_1112_; lean_object* v___x_1113_; lean_object* v_fst_1114_; lean_object* v_snd_1115_; lean_object* v___x_1116_; lean_object* v_cache_1117_; lean_object* v_zetaDeltaFVarIds_1118_; lean_object* v_postponed_1119_; lean_object* v_diag_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_mctx_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_mctx_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = lean_instantiate_level_mvars(v_mctx_1112_, v_l_1108_);
v_fst_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_fst_1114_);
v_snd_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_snd_1115_);
lean_dec_ref(v___x_1113_);
v___x_1116_ = lean_st_ref_take(v___y_1109_);
v_cache_1117_ = lean_ctor_get(v___x_1116_, 1);
v_zetaDeltaFVarIds_1118_ = lean_ctor_get(v___x_1116_, 2);
v_postponed_1119_ = lean_ctor_get(v___x_1116_, 3);
v_diag_1120_ = lean_ctor_get(v___x_1116_, 4);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1116_, 0);
lean_dec(v_unused_1130_);
v___x_1122_ = v___x_1116_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_diag_1120_);
lean_inc(v_postponed_1119_);
lean_inc(v_zetaDeltaFVarIds_1118_);
lean_inc(v_cache_1117_);
lean_dec(v___x_1116_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_fst_1114_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_fst_1114_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_cache_1117_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_zetaDeltaFVarIds_1118_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_postponed_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_diag_1120_);
v___x_1125_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_st_ref_set(v___y_1109_, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_snd_1115_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1131_, v___y_1132_);
lean_dec(v___y_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1135_, v___y_1137_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_unsigned_to_nat(32u);
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = ((size_t)5ULL);
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = lean_unsigned_to_nat(32u);
v___x_1155_ = lean_mk_empty_array_with_capacity(v___x_1154_);
v___x_1156_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1157_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
lean_ctor_set(v___x_1157_, 2, v___x_1153_);
lean_ctor_set(v___x_1157_, 3, v___x_1153_);
lean_ctor_set_usize(v___x_1157_, 4, v___x_1152_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v_traceState_1161_; lean_object* v_traces_1162_; lean_object* v___x_1163_; lean_object* v_traceState_1164_; lean_object* v_env_1165_; lean_object* v_nextMacroScope_1166_; lean_object* v_ngen_1167_; lean_object* v_auxDeclNGen_1168_; lean_object* v_cache_1169_; lean_object* v_messages_1170_; lean_object* v_infoState_1171_; lean_object* v_snapshotTasks_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1191_; 
v___x_1160_ = lean_st_ref_get(v___y_1158_);
v_traceState_1161_ = lean_ctor_get(v___x_1160_, 4);
lean_inc_ref(v_traceState_1161_);
lean_dec(v___x_1160_);
v_traces_1162_ = lean_ctor_get(v_traceState_1161_, 0);
lean_inc_ref(v_traces_1162_);
lean_dec_ref(v_traceState_1161_);
v___x_1163_ = lean_st_ref_take(v___y_1158_);
v_traceState_1164_ = lean_ctor_get(v___x_1163_, 4);
v_env_1165_ = lean_ctor_get(v___x_1163_, 0);
v_nextMacroScope_1166_ = lean_ctor_get(v___x_1163_, 1);
v_ngen_1167_ = lean_ctor_get(v___x_1163_, 2);
v_auxDeclNGen_1168_ = lean_ctor_get(v___x_1163_, 3);
v_cache_1169_ = lean_ctor_get(v___x_1163_, 5);
v_messages_1170_ = lean_ctor_get(v___x_1163_, 6);
v_infoState_1171_ = lean_ctor_get(v___x_1163_, 7);
v_snapshotTasks_1172_ = lean_ctor_get(v___x_1163_, 8);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1174_ = v___x_1163_;
v_isShared_1175_ = v_isSharedCheck_1191_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snapshotTasks_1172_);
lean_inc(v_infoState_1171_);
lean_inc(v_messages_1170_);
lean_inc(v_cache_1169_);
lean_inc(v_traceState_1164_);
lean_inc(v_auxDeclNGen_1168_);
lean_inc(v_ngen_1167_);
lean_inc(v_nextMacroScope_1166_);
lean_inc(v_env_1165_);
lean_dec(v___x_1163_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1191_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
uint64_t v_tid_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1189_; 
v_tid_1176_ = lean_ctor_get_uint64(v_traceState_1164_, sizeof(void*)*1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_traceState_1164_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_traceState_1164_, 0);
lean_dec(v_unused_1190_);
v___x_1178_ = v_traceState_1164_;
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_traceState_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1180_);
lean_ctor_set_uint64(v_reuseFailAlloc_1188_, sizeof(void*)*1, v_tid_1176_);
v___x_1182_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v___x_1182_);
v___x_1184_ = v___x_1174_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_env_1165_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_nextMacroScope_1166_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_ngen_1167_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_auxDeclNGen_1168_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v_cache_1169_);
lean_ctor_set(v_reuseFailAlloc_1187_, 6, v_messages_1170_);
lean_ctor_set(v_reuseFailAlloc_1187_, 7, v_infoState_1171_);
lean_ctor_set(v_reuseFailAlloc_1187_, 8, v_snapshotTasks_1172_);
v___x_1184_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_st_ref_set(v___y_1158_, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_traces_1162_);
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1192_);
lean_dec(v___y_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1207_, lean_object* v_k_1208_, uint8_t v_v_1209_){
_start:
{
lean_object* v_map_1210_; uint8_t v_hasTrace_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1225_; 
v_map_1210_ = lean_ctor_get(v_o_1207_, 0);
v_hasTrace_1211_ = lean_ctor_get_uint8(v_o_1207_, sizeof(void*)*1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_o_1207_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1213_ = v_o_1207_;
v_isShared_1214_ = v_isSharedCheck_1225_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_map_1210_);
lean_dec(v_o_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1225_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1215_, 0, v_v_1209_);
lean_inc(v_k_1208_);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1208_, v___x_1215_, v_map_1210_);
if (v_hasTrace_1211_ == 0)
{
lean_object* v___x_1217_; uint8_t v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1218_ = l_Lean_Name_isPrefixOf(v___x_1217_, v_k_1208_);
lean_dec(v_k_1208_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1220_ = v___x_1213_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1216_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*1, v___x_1218_);
return v___x_1220_;
}
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_k_1208_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1223_ = v___x_1213_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*1, v_hasTrace_1211_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1226_, lean_object* v_k_1227_, lean_object* v_v_1228_){
_start:
{
uint8_t v_v_boxed_1229_; lean_object* v_res_1230_; 
v_v_boxed_1229_ = lean_unbox(v_v_1228_);
v_res_1230_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1226_, v_k_1227_, v_v_boxed_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1231_, lean_object* v_opt_1232_){
_start:
{
lean_object* v_name_1233_; lean_object* v_defValue_1234_; lean_object* v_map_1235_; lean_object* v___x_1236_; 
v_name_1233_ = lean_ctor_get(v_opt_1232_, 0);
v_defValue_1234_ = lean_ctor_get(v_opt_1232_, 1);
v_map_1235_ = lean_ctor_get(v_opts_1231_, 0);
v___x_1236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1235_, v_name_1233_);
if (lean_obj_tag(v___x_1236_) == 0)
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_unbox(v_defValue_1234_);
return v___x_1237_;
}
else
{
lean_object* v_val_1238_; 
v_val_1238_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1236_, 1);
if (lean_obj_tag(v_val_1238_) == 1)
{
uint8_t v_v_1239_; 
v_v_1239_ = lean_ctor_get_uint8(v_val_1238_, 0);
lean_dec_ref_known(v_val_1238_, 0);
return v_v_1239_;
}
else
{
uint8_t v___x_1240_; 
lean_dec(v_val_1238_);
v___x_1240_ = lean_unbox(v_defValue_1234_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1241_, lean_object* v_opt_1242_){
_start:
{
uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_res_1243_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1241_, v_opt_1242_);
lean_dec_ref(v_opt_1242_);
lean_dec_ref(v_opts_1241_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1245_, lean_object* v_opt_1246_){
_start:
{
lean_object* v_name_1247_; lean_object* v_defValue_1248_; lean_object* v_map_1249_; lean_object* v___x_1250_; 
v_name_1247_ = lean_ctor_get(v_opt_1246_, 0);
v_defValue_1248_ = lean_ctor_get(v_opt_1246_, 1);
v_map_1249_ = lean_ctor_get(v_opts_1245_, 0);
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1249_, v_name_1247_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_inc(v_defValue_1248_);
return v_defValue_1248_;
}
else
{
lean_object* v_val_1251_; 
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1250_, 1);
if (lean_obj_tag(v_val_1251_) == 3)
{
lean_object* v_v_1252_; 
v_v_1252_ = lean_ctor_get(v_val_1251_, 0);
lean_inc(v_v_1252_);
lean_dec_ref_known(v_val_1251_, 1);
return v_v_1252_;
}
else
{
lean_dec(v_val_1251_);
lean_inc(v_defValue_1248_);
return v_defValue_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1253_, lean_object* v_opt_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1253_, v_opt_1254_);
lean_dec_ref(v_opt_1254_);
lean_dec_ref(v_opts_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1256_, lean_object* v_lhs_1257_, lean_object* v_rhs_1258_, lean_object* v___x_1259_, lean_object* v___x_1260_, uint8_t v___x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___y_1294_; 
if (v___x_1256_ == 0)
{
lean_object* v___x_1332_; lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v_a_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; uint8_t v___x_1339_; 
lean_inc(v_lhs_1257_);
v___x_1332_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1257_, v___y_1263_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref(v___x_1332_);
lean_inc(v_rhs_1258_);
v___x_1334_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1258_, v___y_1263_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = l_Lean_Level_normalize(v_a_1333_);
lean_dec(v_a_1333_);
v___x_1337_ = l_Lean_Level_normalize(v_a_1335_);
lean_dec(v_a_1335_);
v___x_1338_ = lean_level_eq(v_lhs_1257_, v___x_1336_);
v___x_1339_ = lean_bool_not(v___x_1338_);
if (v___x_1339_ == 0)
{
uint8_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_level_eq(v_rhs_1258_, v___x_1337_);
v___x_1341_ = lean_bool_not(v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec(v___x_1337_);
lean_dec(v___x_1336_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v_rhs_1258_);
lean_inc(v_lhs_1257_);
v___x_1342_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1257_, v_rhs_1258_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1386_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1386_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1386_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
uint8_t v___x_1347_; uint8_t v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1347_ = 2;
v___x_1348_ = lean_unbox(v_a_1343_);
v___x_1349_ = l_Lean_instBEqLBool_beq(v___x_1348_, v___x_1347_);
v___x_1350_ = lean_bool_not(v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_del_object(v___x_1345_);
lean_dec(v_a_1343_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v_lhs_1257_);
lean_inc(v_rhs_1258_);
v___x_1351_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1258_, v_lhs_1257_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1370_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1370_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1370_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_unbox(v_a_1352_);
v___x_1357_ = l_Lean_instBEqLBool_beq(v___x_1356_, v___x_1347_);
v___x_1358_ = lean_bool_not(v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_del_object(v___x_1354_);
lean_dec(v_a_1352_);
lean_inc(v_lhs_1257_);
v___x_1359_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1257_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; uint8_t v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
v___x_1361_ = lean_unbox(v_a_1360_);
lean_dec(v_a_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec_ref_known(v___x_1359_, 1);
lean_inc(v_rhs_1258_);
v___x_1362_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1258_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
v___y_1294_ = v___x_1362_;
goto v___jp_1293_;
}
else
{
v___y_1294_ = v___x_1359_;
goto v___jp_1293_;
}
}
else
{
v___y_1294_ = v___x_1359_;
goto v___jp_1293_;
}
}
else
{
uint8_t v___x_1363_; uint8_t v___x_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v___x_1363_ = 1;
v___x_1364_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
v___x_1365_ = l_Lean_instBEqLBool_beq(v___x_1364_, v___x_1363_);
v___x_1366_ = lean_box(v___x_1365_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1366_);
v___x_1368_ = v___x_1354_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v_a_1371_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1351_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1351_);
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
else
{
uint8_t v___x_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v___x_1379_ = 1;
v___x_1380_ = lean_unbox(v_a_1343_);
lean_dec(v_a_1343_);
v___x_1381_ = l_Lean_instBEqLBool_beq(v___x_1380_, v___x_1379_);
v___x_1382_ = lean_box(v___x_1381_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1382_);
v___x_1384_ = v___x_1345_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
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
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v_a_1387_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1342_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1342_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v___x_1395_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
v___x_1395_ = lean_is_level_def_eq(v___x_1336_, v___x_1337_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1395_;
}
}
else
{
lean_object* v___x_1396_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
v___x_1396_ = lean_is_level_def_eq(v___x_1336_, v___x_1337_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1396_;
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
v___x_1397_ = l_Lean_Level_getOffset(v_lhs_1257_);
lean_dec(v_lhs_1257_);
v___x_1398_ = l_Lean_Level_getOffset(v_rhs_1258_);
lean_dec(v_rhs_1258_);
v___x_1399_ = lean_nat_dec_eq(v___x_1397_, v___x_1398_);
lean_dec(v___x_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
v___jp_1267_:
{
lean_object* v_options_1268_; uint8_t v_hasTrace_1269_; 
v_options_1268_ = lean_ctor_get(v___y_1264_, 2);
v_hasTrace_1269_ = lean_ctor_get_uint8(v_options_1268_, sizeof(void*)*1);
if (v_hasTrace_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v___x_1270_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1270_;
}
else
{
lean_object* v_inheritedTraceOptions_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_inheritedTraceOptions_1271_ = lean_ctor_get(v___y_1264_, 13);
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1273_ = l_Lean_Name_mkStr3(v___x_1259_, v___x_1260_, v___x_1272_);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1273_);
v___x_1275_ = l_Lean_Name_append(v___x_1274_, v___x_1273_);
v___x_1276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1271_, v_options_1268_, v___x_1275_);
lean_dec(v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
lean_dec(v___x_1273_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v___x_1277_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = l_Lean_MessageData_ofLevel(v_lhs_1257_);
v___x_1279_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_MessageData_ofLevel(v_rhs_1258_);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1273_, v___x_1282_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref_known(v___x_1283_, 1);
v___x_1284_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1284_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1283_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
v___jp_1293_:
{
if (lean_obj_tag(v___y_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1331_; 
v_a_1295_ = lean_ctor_get(v___y_1294_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___y_1294_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1297_ = v___y_1294_;
v_isShared_1298_ = v_isSharedCheck_1331_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___y_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1331_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
uint8_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
v___x_1300_ = lean_bool_not(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_del_object(v___x_1297_);
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
v___x_1301_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1257_, v_rhs_1258_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1310_);
v___x_1303_ = v___x_1301_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v___x_1301_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(v___x_1261_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1301_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1301_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v___x_1319_; uint8_t v_isDefEqStuckEx_1320_; 
v___x_1319_ = l_Lean_Meta_Context_config(v___y_1262_);
v_isDefEqStuckEx_1320_ = lean_ctor_get_uint8(v___x_1319_, 4);
lean_dec_ref(v___x_1319_);
if (v_isDefEqStuckEx_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v___x_1321_ = lean_box(v_isDefEqStuckEx_1320_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1321_);
v___x_1323_ = v___x_1297_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Lean_Level_isMVar(v_lhs_1257_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Level_isMVar(v_rhs_1258_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
v___x_1327_ = lean_box(v___x_1326_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1327_);
v___x_1329_ = v___x_1297_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_del_object(v___x_1297_);
goto v___jp_1267_;
}
}
else
{
lean_del_object(v___x_1297_);
goto v___jp_1267_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1259_);
lean_dec(v_rhs_1258_);
lean_dec(v_lhs_1257_);
return v___y_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1402_, lean_object* v_lhs_1403_, lean_object* v_rhs_1404_, lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
uint8_t v___x_14149__boxed_1413_; uint8_t v___x_14152__boxed_1414_; lean_object* v_res_1415_; 
v___x_14149__boxed_1413_ = lean_unbox(v___x_1402_);
v___x_14152__boxed_1414_ = lean_unbox(v___x_1407_);
v_res_1415_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_14149__boxed_1413_, v_lhs_1403_, v_rhs_1404_, v___x_1405_, v___x_1406_, v___x_14152__boxed_1414_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1415_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1416_){
_start:
{
if (lean_obj_tag(v_e_1416_) == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 2;
return v___x_1417_;
}
else
{
lean_object* v_a_1418_; uint8_t v___x_1419_; 
v_a_1418_ = lean_ctor_get(v_e_1416_, 0);
v___x_1419_ = lean_unbox(v_a_1418_);
if (v___x_1419_ == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = 1;
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1422_);
lean_dec_ref(v_e_1422_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v_x_1425_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1425_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v_x_1425_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v_x_1425_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_a_1435_ = lean_ctor_get(v_x_1425_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_x_1425_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v_x_1425_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v_x_1425_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 0);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_bs_1448_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1449_ == 0)
{
return v_bs_1448_;
}
else
{
lean_object* v_v_1450_; lean_object* v_msg_1451_; lean_object* v___x_1452_; lean_object* v_bs_x27_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v_v_1450_ = lean_array_uget_borrowed(v_bs_1448_, v_i_1447_);
v_msg_1451_ = lean_ctor_get(v_v_1450_, 1);
lean_inc_ref(v_msg_1451_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v_bs_x27_1453_ = lean_array_uset(v_bs_1448_, v_i_1447_, v___x_1452_);
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1447_, v___x_1454_);
v___x_1456_ = lean_array_uset(v_bs_x27_1453_, v_i_1447_, v_msg_1451_);
v_i_1447_ = v___x_1455_;
v_bs_1448_ = v___x_1456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1458_, lean_object* v_i_1459_, lean_object* v_bs_1460_){
_start:
{
size_t v_sz_boxed_1461_; size_t v_i_boxed_1462_; lean_object* v_res_1463_; 
v_sz_boxed_1461_ = lean_unbox_usize(v_sz_1458_);
lean_dec(v_sz_1458_);
v_i_boxed_1462_ = lean_unbox_usize(v_i_1459_);
lean_dec(v_i_1459_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1461_, v_i_boxed_1462_, v_bs_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1464_, lean_object* v_data_1465_, lean_object* v_ref_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_fileName_1473_; lean_object* v_fileMap_1474_; lean_object* v_options_1475_; lean_object* v_currRecDepth_1476_; lean_object* v_maxRecDepth_1477_; lean_object* v_ref_1478_; lean_object* v_currNamespace_1479_; lean_object* v_openDecls_1480_; lean_object* v_initHeartbeats_1481_; lean_object* v_maxHeartbeats_1482_; lean_object* v_quotContext_1483_; lean_object* v_currMacroScope_1484_; uint8_t v_diag_1485_; lean_object* v_cancelTk_x3f_1486_; uint8_t v_suppressElabErrors_1487_; lean_object* v_inheritedTraceOptions_1488_; lean_object* v___x_1489_; lean_object* v_traceState_1490_; lean_object* v_traces_1491_; lean_object* v_ref_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; lean_object* v_msg_1498_; lean_object* v___x_1499_; lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1537_; 
v_fileName_1473_ = lean_ctor_get(v___y_1470_, 0);
v_fileMap_1474_ = lean_ctor_get(v___y_1470_, 1);
v_options_1475_ = lean_ctor_get(v___y_1470_, 2);
v_currRecDepth_1476_ = lean_ctor_get(v___y_1470_, 3);
v_maxRecDepth_1477_ = lean_ctor_get(v___y_1470_, 4);
v_ref_1478_ = lean_ctor_get(v___y_1470_, 5);
v_currNamespace_1479_ = lean_ctor_get(v___y_1470_, 6);
v_openDecls_1480_ = lean_ctor_get(v___y_1470_, 7);
v_initHeartbeats_1481_ = lean_ctor_get(v___y_1470_, 8);
v_maxHeartbeats_1482_ = lean_ctor_get(v___y_1470_, 9);
v_quotContext_1483_ = lean_ctor_get(v___y_1470_, 10);
v_currMacroScope_1484_ = lean_ctor_get(v___y_1470_, 11);
v_diag_1485_ = lean_ctor_get_uint8(v___y_1470_, sizeof(void*)*14);
v_cancelTk_x3f_1486_ = lean_ctor_get(v___y_1470_, 12);
v_suppressElabErrors_1487_ = lean_ctor_get_uint8(v___y_1470_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1488_ = lean_ctor_get(v___y_1470_, 13);
v___x_1489_ = lean_st_ref_get(v___y_1471_);
v_traceState_1490_ = lean_ctor_get(v___x_1489_, 4);
lean_inc_ref(v_traceState_1490_);
lean_dec(v___x_1489_);
v_traces_1491_ = lean_ctor_get(v_traceState_1490_, 0);
lean_inc_ref(v_traces_1491_);
lean_dec_ref(v_traceState_1490_);
v_ref_1492_ = l_Lean_replaceRef(v_ref_1466_, v_ref_1478_);
lean_inc_ref(v_inheritedTraceOptions_1488_);
lean_inc(v_cancelTk_x3f_1486_);
lean_inc(v_currMacroScope_1484_);
lean_inc(v_quotContext_1483_);
lean_inc(v_maxHeartbeats_1482_);
lean_inc(v_initHeartbeats_1481_);
lean_inc(v_openDecls_1480_);
lean_inc(v_currNamespace_1479_);
lean_inc(v_maxRecDepth_1477_);
lean_inc(v_currRecDepth_1476_);
lean_inc_ref(v_options_1475_);
lean_inc_ref(v_fileMap_1474_);
lean_inc_ref(v_fileName_1473_);
v___x_1493_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1493_, 0, v_fileName_1473_);
lean_ctor_set(v___x_1493_, 1, v_fileMap_1474_);
lean_ctor_set(v___x_1493_, 2, v_options_1475_);
lean_ctor_set(v___x_1493_, 3, v_currRecDepth_1476_);
lean_ctor_set(v___x_1493_, 4, v_maxRecDepth_1477_);
lean_ctor_set(v___x_1493_, 5, v_ref_1492_);
lean_ctor_set(v___x_1493_, 6, v_currNamespace_1479_);
lean_ctor_set(v___x_1493_, 7, v_openDecls_1480_);
lean_ctor_set(v___x_1493_, 8, v_initHeartbeats_1481_);
lean_ctor_set(v___x_1493_, 9, v_maxHeartbeats_1482_);
lean_ctor_set(v___x_1493_, 10, v_quotContext_1483_);
lean_ctor_set(v___x_1493_, 11, v_currMacroScope_1484_);
lean_ctor_set(v___x_1493_, 12, v_cancelTk_x3f_1486_);
lean_ctor_set(v___x_1493_, 13, v_inheritedTraceOptions_1488_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*14, v_diag_1485_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*14 + 1, v_suppressElabErrors_1487_);
v___x_1494_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1491_);
lean_dec_ref(v_traces_1491_);
v_sz_1495_ = lean_array_size(v___x_1494_);
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1495_, v___x_1496_, v___x_1494_);
v_msg_1498_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1498_, 0, v_data_1465_);
lean_ctor_set(v_msg_1498_, 1, v_msg_1467_);
lean_ctor_set(v_msg_1498_, 2, v___x_1497_);
v___x_1499_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1498_, v___y_1468_, v___y_1469_, v___x_1493_, v___y_1471_);
lean_dec_ref_known(v___x_1493_, 14);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1537_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1537_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v_traceState_1505_; lean_object* v_env_1506_; lean_object* v_nextMacroScope_1507_; lean_object* v_ngen_1508_; lean_object* v_auxDeclNGen_1509_; lean_object* v_cache_1510_; lean_object* v_messages_1511_; lean_object* v_infoState_1512_; lean_object* v_snapshotTasks_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1536_; 
v___x_1504_ = lean_st_ref_take(v___y_1471_);
v_traceState_1505_ = lean_ctor_get(v___x_1504_, 4);
v_env_1506_ = lean_ctor_get(v___x_1504_, 0);
v_nextMacroScope_1507_ = lean_ctor_get(v___x_1504_, 1);
v_ngen_1508_ = lean_ctor_get(v___x_1504_, 2);
v_auxDeclNGen_1509_ = lean_ctor_get(v___x_1504_, 3);
v_cache_1510_ = lean_ctor_get(v___x_1504_, 5);
v_messages_1511_ = lean_ctor_get(v___x_1504_, 6);
v_infoState_1512_ = lean_ctor_get(v___x_1504_, 7);
v_snapshotTasks_1513_ = lean_ctor_get(v___x_1504_, 8);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1515_ = v___x_1504_;
v_isShared_1516_ = v_isSharedCheck_1536_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snapshotTasks_1513_);
lean_inc(v_infoState_1512_);
lean_inc(v_messages_1511_);
lean_inc(v_cache_1510_);
lean_inc(v_traceState_1505_);
lean_inc(v_auxDeclNGen_1509_);
lean_inc(v_ngen_1508_);
lean_inc(v_nextMacroScope_1507_);
lean_inc(v_env_1506_);
lean_dec(v___x_1504_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1536_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint64_t v_tid_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1534_; 
v_tid_1517_ = lean_ctor_get_uint64(v_traceState_1505_, sizeof(void*)*1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_traceState_1505_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_traceState_1505_, 0);
lean_dec(v_unused_1535_);
v___x_1519_ = v_traceState_1505_;
v_isShared_1520_ = v_isSharedCheck_1534_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v_traceState_1505_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1534_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_ref_1466_);
lean_ctor_set(v___x_1521_, 1, v_a_1500_);
v___x_1522_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1464_, v___x_1521_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1522_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1522_);
lean_ctor_set_uint64(v_reuseFailAlloc_1533_, sizeof(void*)*1, v_tid_1517_);
v___x_1524_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 4, v___x_1524_);
v___x_1526_ = v___x_1515_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_env_1506_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_nextMacroScope_1507_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_ngen_1508_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_auxDeclNGen_1509_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1532_, 5, v_cache_1510_);
lean_ctor_set(v_reuseFailAlloc_1532_, 6, v_messages_1511_);
lean_ctor_set(v_reuseFailAlloc_1532_, 7, v_infoState_1512_);
lean_ctor_set(v_reuseFailAlloc_1532_, 8, v_snapshotTasks_1513_);
v___x_1526_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = lean_st_ref_set(v___y_1471_, v___x_1526_);
v___x_1528_ = lean_box(0);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1528_);
v___x_1530_ = v___x_1502_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1538_, lean_object* v_data_1539_, lean_object* v_ref_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1538_, v_data_1539_, v_ref_1540_, v_msg_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1548_; double v___x_1549_; 
v___x_1548_ = lean_unsigned_to_nat(1000u);
v___x_1549_ = lean_float_of_nat(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1550_, uint8_t v_collapsed_1551_, lean_object* v_tag_1552_, lean_object* v_opts_1553_, uint8_t v_clsEnabled_1554_, lean_object* v_oldTraces_1555_, lean_object* v_ref_1556_, lean_object* v_msg_1557_, lean_object* v_resStartStop_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v_data_1567_; lean_object* v_fst_1578_; lean_object* v_snd_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; uint8_t v___y_1592_; double v___y_1623_; 
v_fst_1564_ = lean_ctor_get(v_resStartStop_1558_, 0);
lean_inc(v_fst_1564_);
v_snd_1565_ = lean_ctor_get(v_resStartStop_1558_, 1);
lean_inc(v_snd_1565_);
lean_dec_ref(v_resStartStop_1558_);
v_fst_1578_ = lean_ctor_get(v_snd_1565_, 0);
lean_inc(v_fst_1578_);
v_snd_1579_ = lean_ctor_get(v_snd_1565_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_snd_1565_);
v___x_1580_ = l_Lean_trace_profiler;
v___x_1581_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1553_, v___x_1580_);
if (v___x_1581_ == 0)
{
v___y_1592_ = v___x_1581_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1629_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1553_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; double v___x_1632_; double v___x_1633_; double v___x_1634_; 
v___x_1630_ = l_Lean_trace_profiler_threshold;
v___x_1631_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1553_, v___x_1630_);
v___x_1632_ = lean_float_of_nat(v___x_1631_);
v___x_1633_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1634_ = lean_float_div(v___x_1632_, v___x_1633_);
v___y_1623_ = v___x_1634_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; double v___x_1637_; 
v___x_1635_ = l_Lean_trace_profiler_threshold;
v___x_1636_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1553_, v___x_1635_);
v___x_1637_ = lean_float_of_nat(v___x_1636_);
v___y_1623_ = v___x_1637_;
goto v___jp_1622_;
}
}
v___jp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1555_, v_data_1567_, v_ref_1556_, v_msg_1557_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref_known(v___x_1568_, 1);
v___x_1569_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1564_);
return v___x_1569_;
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_fst_1564_);
v_a_1570_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1568_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1568_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
v___jp_1582_:
{
uint8_t v_result_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; double v___x_1586_; lean_object* v_data_1587_; 
v_result_1583_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1564_);
v___x_1584_ = lean_box(v_result_1583_);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
v___x_1586_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1552_);
lean_inc_ref(v___x_1585_);
lean_inc(v_cls_1550_);
v_data_1587_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1587_, 0, v_cls_1550_);
lean_ctor_set(v_data_1587_, 1, v___x_1585_);
lean_ctor_set(v_data_1587_, 2, v_tag_1552_);
lean_ctor_set_float(v_data_1587_, sizeof(void*)*3, v___x_1586_);
lean_ctor_set_float(v_data_1587_, sizeof(void*)*3 + 8, v___x_1586_);
lean_ctor_set_uint8(v_data_1587_, sizeof(void*)*3 + 16, v_collapsed_1551_);
if (v___x_1581_ == 0)
{
lean_dec_ref_known(v___x_1585_, 1);
lean_dec(v_snd_1579_);
lean_dec(v_fst_1578_);
lean_dec_ref(v_tag_1552_);
lean_dec(v_cls_1550_);
v_data_1567_ = v_data_1587_;
goto v___jp_1566_;
}
else
{
lean_object* v_data_1588_; double v___x_1589_; double v___x_1590_; 
lean_dec_ref_known(v_data_1587_, 3);
v_data_1588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1588_, 0, v_cls_1550_);
lean_ctor_set(v_data_1588_, 1, v___x_1585_);
lean_ctor_set(v_data_1588_, 2, v_tag_1552_);
v___x_1589_ = lean_unbox_float(v_fst_1578_);
lean_dec(v_fst_1578_);
lean_ctor_set_float(v_data_1588_, sizeof(void*)*3, v___x_1589_);
v___x_1590_ = lean_unbox_float(v_snd_1579_);
lean_dec(v_snd_1579_);
lean_ctor_set_float(v_data_1588_, sizeof(void*)*3 + 8, v___x_1590_);
lean_ctor_set_uint8(v_data_1588_, sizeof(void*)*3 + 16, v_collapsed_1551_);
v_data_1567_ = v_data_1588_;
goto v___jp_1566_;
}
}
v___jp_1591_:
{
if (v_clsEnabled_1554_ == 0)
{
if (v___y_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v_traceState_1594_; lean_object* v_env_1595_; lean_object* v_nextMacroScope_1596_; lean_object* v_ngen_1597_; lean_object* v_auxDeclNGen_1598_; lean_object* v_cache_1599_; lean_object* v_messages_1600_; lean_object* v_infoState_1601_; lean_object* v_snapshotTasks_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_snd_1579_);
lean_dec(v_fst_1578_);
lean_dec_ref(v_msg_1557_);
lean_dec(v_ref_1556_);
lean_dec_ref(v_tag_1552_);
lean_dec(v_cls_1550_);
v___x_1593_ = lean_st_ref_take(v___y_1562_);
v_traceState_1594_ = lean_ctor_get(v___x_1593_, 4);
v_env_1595_ = lean_ctor_get(v___x_1593_, 0);
v_nextMacroScope_1596_ = lean_ctor_get(v___x_1593_, 1);
v_ngen_1597_ = lean_ctor_get(v___x_1593_, 2);
v_auxDeclNGen_1598_ = lean_ctor_get(v___x_1593_, 3);
v_cache_1599_ = lean_ctor_get(v___x_1593_, 5);
v_messages_1600_ = lean_ctor_get(v___x_1593_, 6);
v_infoState_1601_ = lean_ctor_get(v___x_1593_, 7);
v_snapshotTasks_1602_ = lean_ctor_get(v___x_1593_, 8);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1604_ = v___x_1593_;
v_isShared_1605_ = v_isSharedCheck_1621_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snapshotTasks_1602_);
lean_inc(v_infoState_1601_);
lean_inc(v_messages_1600_);
lean_inc(v_cache_1599_);
lean_inc(v_traceState_1594_);
lean_inc(v_auxDeclNGen_1598_);
lean_inc(v_ngen_1597_);
lean_inc(v_nextMacroScope_1596_);
lean_inc(v_env_1595_);
lean_dec(v___x_1593_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1621_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
uint64_t v_tid_1606_; lean_object* v_traces_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1620_; 
v_tid_1606_ = lean_ctor_get_uint64(v_traceState_1594_, sizeof(void*)*1);
v_traces_1607_ = lean_ctor_get(v_traceState_1594_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_traceState_1594_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1609_ = v_traceState_1594_;
v_isShared_1610_ = v_isSharedCheck_1620_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_traces_1607_);
lean_dec(v_traceState_1594_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1620_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1555_, v_traces_1607_);
lean_dec_ref(v_traces_1607_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1611_);
lean_ctor_set_uint64(v_reuseFailAlloc_1619_, sizeof(void*)*1, v_tid_1606_);
v___x_1613_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 4, v___x_1613_);
v___x_1615_ = v___x_1604_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_env_1595_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_nextMacroScope_1596_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_ngen_1597_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_auxDeclNGen_1598_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1618_, 5, v_cache_1599_);
lean_ctor_set(v_reuseFailAlloc_1618_, 6, v_messages_1600_);
lean_ctor_set(v_reuseFailAlloc_1618_, 7, v_infoState_1601_);
lean_ctor_set(v_reuseFailAlloc_1618_, 8, v_snapshotTasks_1602_);
v___x_1615_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_st_ref_set(v___y_1562_, v___x_1615_);
v___x_1617_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1564_);
return v___x_1617_;
}
}
}
}
}
else
{
goto v___jp_1582_;
}
}
else
{
goto v___jp_1582_;
}
}
v___jp_1622_:
{
double v___x_1624_; double v___x_1625_; double v___x_1626_; uint8_t v___x_1627_; 
v___x_1624_ = lean_unbox_float(v_snd_1579_);
v___x_1625_ = lean_unbox_float(v_fst_1578_);
v___x_1626_ = lean_float_sub(v___x_1624_, v___x_1625_);
v___x_1627_ = lean_float_decLt(v___y_1623_, v___x_1626_);
v___y_1592_ = v___x_1627_;
goto v___jp_1591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1638_, lean_object* v_collapsed_1639_, lean_object* v_tag_1640_, lean_object* v_opts_1641_, lean_object* v_clsEnabled_1642_, lean_object* v_oldTraces_1643_, lean_object* v_ref_1644_, lean_object* v_msg_1645_, lean_object* v_resStartStop_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v_collapsed_boxed_1652_; uint8_t v_clsEnabled_boxed_1653_; lean_object* v_res_1654_; 
v_collapsed_boxed_1652_ = lean_unbox(v_collapsed_1639_);
v_clsEnabled_boxed_1653_ = lean_unbox(v_clsEnabled_1642_);
v_res_1654_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1638_, v_collapsed_boxed_1652_, v_tag_1640_, v_opts_1641_, v_clsEnabled_boxed_1653_, v_oldTraces_1643_, v_ref_1644_, v_msg_1645_, v_resStartStop_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v_opts_1641_);
return v_res_1654_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1655_; double v___x_1656_; 
v___x_1655_ = lean_unsigned_to_nat(1000000000u);
v___x_1656_ = lean_float_of_nat(v___x_1655_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1672_ = l_Lean_Name_append(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; uint8_t v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v_a_1694_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; uint8_t v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v_a_1717_; lean_object* v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; uint8_t v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; uint8_t v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; uint8_t v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; uint8_t v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; uint8_t v___y_1877_; lean_object* v___y_1878_; uint8_t v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; uint8_t v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; uint8_t v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; uint8_t v_a_1927_; lean_object* v_lhs_1932_; lean_object* v_rhs_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; 
if (lean_obj_tag(v_x_1673_) == 1)
{
if (lean_obj_tag(v_x_1674_) == 1)
{
lean_object* v_a_1970_; lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1970_ = lean_ctor_get(v_x_1673_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v_x_1673_, 1);
v_a_1971_ = lean_ctor_get(v_x_1674_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v_x_1674_, 1);
v___x_1972_ = lean_is_level_def_eq(v_a_1970_, v_a_1971_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
return v___x_1972_;
}
else
{
v_lhs_1932_ = v_x_1673_;
v_rhs_1933_ = v_x_1674_;
v___y_1934_ = v_a_1675_;
v___y_1935_ = v_a_1676_;
v___y_1936_ = v_a_1677_;
v___y_1937_ = v_a_1678_;
goto v___jp_1931_;
}
}
else
{
v_lhs_1932_ = v_x_1673_;
v_rhs_1933_ = v_x_1674_;
v___y_1934_ = v_a_1675_;
v___y_1935_ = v_a_1676_;
v___y_1936_ = v_a_1677_;
v___y_1937_ = v_a_1678_;
goto v___jp_1931_;
}
v___jp_1680_:
{
lean_object* v___x_1695_; double v___x_1696_; double v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1695_ = lean_io_get_num_heartbeats();
v___x_1696_ = lean_float_of_nat(v___y_1683_);
v___x_1697_ = lean_float_of_nat(v___x_1695_);
v___x_1698_ = lean_box_float(v___x_1696_);
v___x_1699_ = lean_box_float(v___x_1697_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1694_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1684_);
v___x_1702_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1684_, v___y_1686_, v___y_1682_, v___y_1692_, v___y_1690_, v___y_1687_, v___y_1689_, v___y_1688_, v___x_1701_, v___y_1681_, v___y_1693_, v___y_1685_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1692_);
return v___x_1702_;
}
v___jp_1703_:
{
lean_object* v___x_1718_; double v___x_1719_; double v___x_1720_; double v___x_1721_; double v___x_1722_; double v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1718_ = lean_io_mono_nanos_now();
v___x_1719_ = lean_float_of_nat(v___y_1706_);
v___x_1720_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1721_ = lean_float_div(v___x_1719_, v___x_1720_);
v___x_1722_ = lean_float_of_nat(v___x_1718_);
v___x_1723_ = lean_float_div(v___x_1722_, v___x_1720_);
v___x_1724_ = lean_box_float(v___x_1721_);
v___x_1725_ = lean_box_float(v___x_1723_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1717_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1707_);
v___x_1728_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1707_, v___y_1709_, v___y_1705_, v___y_1715_, v___y_1713_, v___y_1710_, v___y_1712_, v___y_1711_, v___x_1727_, v___y_1704_, v___y_1716_, v___y_1708_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1715_);
return v___x_1728_;
}
v___jp_1729_:
{
lean_object* v_fileName_1748_; lean_object* v_fileMap_1749_; lean_object* v_currRecDepth_1750_; lean_object* v_ref_1751_; lean_object* v_currNamespace_1752_; lean_object* v_openDecls_1753_; lean_object* v_initHeartbeats_1754_; lean_object* v_maxHeartbeats_1755_; lean_object* v_quotContext_1756_; lean_object* v_currMacroScope_1757_; lean_object* v_cancelTk_x3f_1758_; uint8_t v_suppressElabErrors_1759_; lean_object* v_inheritedTraceOptions_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1811_; 
v_fileName_1748_ = lean_ctor_get(v___y_1746_, 0);
v_fileMap_1749_ = lean_ctor_get(v___y_1746_, 1);
v_currRecDepth_1750_ = lean_ctor_get(v___y_1746_, 3);
v_ref_1751_ = lean_ctor_get(v___y_1746_, 5);
v_currNamespace_1752_ = lean_ctor_get(v___y_1746_, 6);
v_openDecls_1753_ = lean_ctor_get(v___y_1746_, 7);
v_initHeartbeats_1754_ = lean_ctor_get(v___y_1746_, 8);
v_maxHeartbeats_1755_ = lean_ctor_get(v___y_1746_, 9);
v_quotContext_1756_ = lean_ctor_get(v___y_1746_, 10);
v_currMacroScope_1757_ = lean_ctor_get(v___y_1746_, 11);
v_cancelTk_x3f_1758_ = lean_ctor_get(v___y_1746_, 12);
v_suppressElabErrors_1759_ = lean_ctor_get_uint8(v___y_1746_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1760_ = lean_ctor_get(v___y_1746_, 13);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___y_1746_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; lean_object* v_unused_1813_; 
v_unused_1812_ = lean_ctor_get(v___y_1746_, 4);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v___y_1746_, 2);
lean_dec(v_unused_1813_);
v___x_1762_ = v___y_1746_;
v_isShared_1763_ = v_isSharedCheck_1811_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_inheritedTraceOptions_1760_);
lean_inc(v_cancelTk_x3f_1758_);
lean_inc(v_currMacroScope_1757_);
lean_inc(v_quotContext_1756_);
lean_inc(v_maxHeartbeats_1755_);
lean_inc(v_initHeartbeats_1754_);
lean_inc(v_openDecls_1753_);
lean_inc(v_currNamespace_1752_);
lean_inc(v_ref_1751_);
lean_inc(v_currRecDepth_1750_);
lean_inc(v_fileMap_1749_);
lean_inc(v_fileName_1748_);
lean_dec(v___y_1746_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1811_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1764_ = l_Lean_maxRecDepth;
v___x_1765_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1741_, v___x_1764_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v___x_1765_);
lean_ctor_set(v___x_1762_, 2, v___y_1741_);
v___x_1767_ = v___x_1762_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_fileName_1748_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_fileMap_1749_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v___y_1741_);
lean_ctor_set(v_reuseFailAlloc_1810_, 3, v_currRecDepth_1750_);
lean_ctor_set(v_reuseFailAlloc_1810_, 4, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1810_, 5, v_ref_1751_);
lean_ctor_set(v_reuseFailAlloc_1810_, 6, v_currNamespace_1752_);
lean_ctor_set(v_reuseFailAlloc_1810_, 7, v_openDecls_1753_);
lean_ctor_set(v_reuseFailAlloc_1810_, 8, v_initHeartbeats_1754_);
lean_ctor_set(v_reuseFailAlloc_1810_, 9, v_maxHeartbeats_1755_);
lean_ctor_set(v_reuseFailAlloc_1810_, 10, v_quotContext_1756_);
lean_ctor_set(v_reuseFailAlloc_1810_, 11, v_currMacroScope_1757_);
lean_ctor_set(v_reuseFailAlloc_1810_, 12, v_cancelTk_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1810_, 13, v_inheritedTraceOptions_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1810_, sizeof(void*)*14 + 1, v_suppressElabErrors_1759_);
v___x_1767_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v_a_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*14, v___y_1732_);
v___x_1768_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1733_, v___y_1730_, v___y_1745_, v___x_1767_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___x_1767_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1769_, v___y_1730_, v___y_1745_, v___y_1734_, v___y_1743_);
lean_dec_ref(v___y_1734_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1773_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1744_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_io_mono_nanos_now();
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1736_);
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1730_);
v___x_1775_ = lean_apply_5(v___y_1738_, v___y_1730_, v___y_1745_, v___y_1736_, v___y_1743_, lean_box(0));
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
v___y_1704_ = v___y_1730_;
v___y_1705_ = v___y_1731_;
v___y_1706_ = v___x_1774_;
v___y_1707_ = v___y_1735_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1737_;
v___y_1710_ = v___y_1739_;
v___y_1711_ = v_a_1771_;
v___y_1712_ = v___y_1740_;
v___y_1713_ = v___y_1742_;
v___y_1714_ = v___y_1743_;
v___y_1715_ = v___y_1744_;
v___y_1716_ = v___y_1745_;
v_a_1717_ = v___x_1781_;
goto v___jp_1703_;
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
v___y_1704_ = v___y_1730_;
v___y_1705_ = v___y_1731_;
v___y_1706_ = v___x_1774_;
v___y_1707_ = v___y_1735_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1737_;
v___y_1710_ = v___y_1739_;
v___y_1711_ = v_a_1771_;
v___y_1712_ = v___y_1740_;
v___y_1713_ = v___y_1742_;
v___y_1714_ = v___y_1743_;
v___y_1715_ = v___y_1744_;
v___y_1716_ = v___y_1745_;
v_a_1717_ = v___x_1789_;
goto v___jp_1703_;
}
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1736_);
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1730_);
v___x_1793_ = lean_apply_5(v___y_1738_, v___y_1730_, v___y_1745_, v___y_1736_, v___y_1743_, lean_box(0));
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
v___y_1681_ = v___y_1730_;
v___y_1682_ = v___y_1731_;
v___y_1683_ = v___x_1792_;
v___y_1684_ = v___y_1735_;
v___y_1685_ = v___y_1736_;
v___y_1686_ = v___y_1737_;
v___y_1687_ = v___y_1739_;
v___y_1688_ = v_a_1771_;
v___y_1689_ = v___y_1740_;
v___y_1690_ = v___y_1742_;
v___y_1691_ = v___y_1743_;
v___y_1692_ = v___y_1744_;
v___y_1693_ = v___y_1745_;
v_a_1694_ = v___x_1799_;
goto v___jp_1680_;
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
v___y_1681_ = v___y_1730_;
v___y_1682_ = v___y_1731_;
v___y_1683_ = v___x_1792_;
v___y_1684_ = v___y_1735_;
v___y_1685_ = v___y_1736_;
v___y_1686_ = v___y_1737_;
v___y_1687_ = v___y_1739_;
v___y_1688_ = v_a_1771_;
v___y_1689_ = v___y_1740_;
v___y_1690_ = v___y_1742_;
v___y_1691_ = v___y_1743_;
v___y_1692_ = v___y_1744_;
v___y_1693_ = v___y_1745_;
v_a_1694_ = v___x_1807_;
goto v___jp_1680_;
}
}
}
}
}
}
}
v___jp_1814_:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_bool_not(v___y_1831_);
if (v___x_1832_ == 0)
{
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1818_);
v___y_1730_ = v___y_1815_;
v___y_1731_ = v___y_1816_;
v___y_1732_ = v___y_1817_;
v___y_1733_ = v___y_1819_;
v___y_1734_ = v___y_1818_;
v___y_1735_ = v___y_1820_;
v___y_1736_ = v___y_1821_;
v___y_1737_ = v___y_1822_;
v___y_1738_ = v___y_1823_;
v___y_1739_ = v___y_1824_;
v___y_1740_ = v___y_1825_;
v___y_1741_ = v___y_1826_;
v___y_1742_ = v___y_1827_;
v___y_1743_ = v___y_1828_;
v___y_1744_ = v___y_1829_;
v___y_1745_ = v___y_1830_;
v___y_1746_ = v___y_1818_;
v___y_1747_ = v___y_1828_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1833_; lean_object* v_env_1834_; lean_object* v_nextMacroScope_1835_; lean_object* v_ngen_1836_; lean_object* v_auxDeclNGen_1837_; lean_object* v_traceState_1838_; lean_object* v_messages_1839_; lean_object* v_infoState_1840_; lean_object* v_snapshotTasks_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1851_; 
v___x_1833_ = lean_st_ref_take(v___y_1828_);
v_env_1834_ = lean_ctor_get(v___x_1833_, 0);
v_nextMacroScope_1835_ = lean_ctor_get(v___x_1833_, 1);
v_ngen_1836_ = lean_ctor_get(v___x_1833_, 2);
v_auxDeclNGen_1837_ = lean_ctor_get(v___x_1833_, 3);
v_traceState_1838_ = lean_ctor_get(v___x_1833_, 4);
v_messages_1839_ = lean_ctor_get(v___x_1833_, 6);
v_infoState_1840_ = lean_ctor_get(v___x_1833_, 7);
v_snapshotTasks_1841_ = lean_ctor_get(v___x_1833_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1833_, 5);
lean_dec(v_unused_1852_);
v___x_1843_ = v___x_1833_;
v_isShared_1844_ = v_isSharedCheck_1851_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snapshotTasks_1841_);
lean_inc(v_infoState_1840_);
lean_inc(v_messages_1839_);
lean_inc(v_traceState_1838_);
lean_inc(v_auxDeclNGen_1837_);
lean_inc(v_ngen_1836_);
lean_inc(v_nextMacroScope_1835_);
lean_inc(v_env_1834_);
lean_dec(v___x_1833_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1851_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = l_Lean_Kernel_enableDiag(v_env_1834_, v___y_1817_);
v___x_1846_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 5, v___x_1846_);
lean_ctor_set(v___x_1843_, 0, v___x_1845_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_nextMacroScope_1835_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_ngen_1836_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_auxDeclNGen_1837_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_traceState_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v_messages_1839_);
lean_ctor_set(v_reuseFailAlloc_1850_, 7, v_infoState_1840_);
lean_ctor_set(v_reuseFailAlloc_1850_, 8, v_snapshotTasks_1841_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_st_ref_set(v___y_1828_, v___x_1848_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1818_);
v___y_1730_ = v___y_1815_;
v___y_1731_ = v___y_1816_;
v___y_1732_ = v___y_1817_;
v___y_1733_ = v___y_1819_;
v___y_1734_ = v___y_1818_;
v___y_1735_ = v___y_1820_;
v___y_1736_ = v___y_1821_;
v___y_1737_ = v___y_1822_;
v___y_1738_ = v___y_1823_;
v___y_1739_ = v___y_1824_;
v___y_1740_ = v___y_1825_;
v___y_1741_ = v___y_1826_;
v___y_1742_ = v___y_1827_;
v___y_1743_ = v___y_1828_;
v___y_1744_ = v___y_1829_;
v___y_1745_ = v___y_1830_;
v___y_1746_ = v___y_1818_;
v___y_1747_ = v___y_1828_;
goto v___jp_1729_;
}
}
}
}
v___jp_1853_:
{
lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v_env_1885_; lean_object* v_ref_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; uint8_t v___x_1897_; 
v___x_1882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1866_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = lean_st_ref_get(v___y_1866_);
v_env_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc_ref(v_env_1885_);
lean_dec(v___x_1884_);
v_ref_1886_ = l_Lean_replaceRef(v___y_1876_, v___y_1876_);
lean_inc_ref_n(v___y_1880_, 2);
v___x_1887_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1887_, 0, v___y_1865_);
lean_ctor_set(v___x_1887_, 1, v___y_1858_);
lean_ctor_set(v___x_1887_, 2, v___y_1880_);
lean_ctor_set(v___x_1887_, 3, v___y_1871_);
lean_ctor_set(v___x_1887_, 4, v___y_1875_);
lean_ctor_set(v___x_1887_, 5, v_ref_1886_);
lean_ctor_set(v___x_1887_, 6, v___y_1874_);
lean_ctor_set(v___x_1887_, 7, v___y_1868_);
lean_ctor_set(v___x_1887_, 8, v___y_1862_);
lean_ctor_set(v___x_1887_, 9, v___y_1857_);
lean_ctor_set(v___x_1887_, 10, v___y_1873_);
lean_ctor_set(v___x_1887_, 11, v___y_1863_);
lean_ctor_set(v___x_1887_, 12, v___y_1867_);
lean_ctor_set(v___x_1887_, 13, v___y_1878_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*14, v___y_1859_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*14 + 1, v___y_1877_);
v___x_1888_ = l_Lean_MessageData_ofLevel(v___y_1860_);
v___x_1889_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_ofLevel(v___y_1854_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1894_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1880_, v___x_1893_, v___y_1855_);
v___x_1895_ = l_Lean_diagnostics;
v___x_1896_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___x_1894_, v___x_1895_);
v___x_1897_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1885_);
lean_dec_ref(v_env_1885_);
if (v___x_1897_ == 0)
{
if (v___x_1896_ == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = 1;
v___y_1815_ = v___y_1869_;
v___y_1816_ = v___y_1856_;
v___y_1817_ = v___x_1896_;
v___y_1818_ = v___x_1887_;
v___y_1819_ = v___x_1892_;
v___y_1820_ = v___y_1870_;
v___y_1821_ = v___y_1861_;
v___y_1822_ = v___y_1872_;
v___y_1823_ = v___y_1864_;
v___y_1824_ = v_a_1883_;
v___y_1825_ = v___y_1876_;
v___y_1826_ = v___x_1894_;
v___y_1827_ = v___y_1879_;
v___y_1828_ = v___y_1866_;
v___y_1829_ = v___y_1880_;
v___y_1830_ = v___y_1881_;
v___y_1831_ = v___x_1898_;
goto v___jp_1814_;
}
else
{
v___y_1815_ = v___y_1869_;
v___y_1816_ = v___y_1856_;
v___y_1817_ = v___x_1896_;
v___y_1818_ = v___x_1887_;
v___y_1819_ = v___x_1892_;
v___y_1820_ = v___y_1870_;
v___y_1821_ = v___y_1861_;
v___y_1822_ = v___y_1872_;
v___y_1823_ = v___y_1864_;
v___y_1824_ = v_a_1883_;
v___y_1825_ = v___y_1876_;
v___y_1826_ = v___x_1894_;
v___y_1827_ = v___y_1879_;
v___y_1828_ = v___y_1866_;
v___y_1829_ = v___y_1880_;
v___y_1830_ = v___y_1881_;
v___y_1831_ = v___x_1897_;
goto v___jp_1814_;
}
}
else
{
v___y_1815_ = v___y_1869_;
v___y_1816_ = v___y_1856_;
v___y_1817_ = v___x_1896_;
v___y_1818_ = v___x_1887_;
v___y_1819_ = v___x_1892_;
v___y_1820_ = v___y_1870_;
v___y_1821_ = v___y_1861_;
v___y_1822_ = v___y_1872_;
v___y_1823_ = v___y_1864_;
v___y_1824_ = v_a_1883_;
v___y_1825_ = v___y_1876_;
v___y_1826_ = v___x_1894_;
v___y_1827_ = v___y_1879_;
v___y_1828_ = v___y_1866_;
v___y_1829_ = v___y_1880_;
v___y_1830_ = v___y_1881_;
v___y_1831_ = v___x_1896_;
goto v___jp_1814_;
}
}
v___jp_1899_:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = l_Lean_trace_profiler;
v___x_1929_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1925_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1917_);
lean_dec(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1909_);
lean_dec(v___y_1907_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec(v___y_1900_);
v___x_1930_ = lean_apply_5(v___y_1910_, v___y_1915_, v___y_1926_, v___y_1908_, v___y_1912_, lean_box(0));
return v___x_1930_;
}
else
{
v___y_1854_ = v___y_1900_;
v___y_1855_ = v___y_1902_;
v___y_1856_ = v___y_1901_;
v___y_1857_ = v___y_1903_;
v___y_1858_ = v___y_1904_;
v___y_1859_ = v___y_1906_;
v___y_1860_ = v___y_1905_;
v___y_1861_ = v___y_1908_;
v___y_1862_ = v___y_1907_;
v___y_1863_ = v___y_1909_;
v___y_1864_ = v___y_1910_;
v___y_1865_ = v___y_1911_;
v___y_1866_ = v___y_1912_;
v___y_1867_ = v___y_1913_;
v___y_1868_ = v___y_1914_;
v___y_1869_ = v___y_1915_;
v___y_1870_ = v___y_1916_;
v___y_1871_ = v___y_1917_;
v___y_1872_ = v___y_1918_;
v___y_1873_ = v___y_1919_;
v___y_1874_ = v___y_1920_;
v___y_1875_ = v___y_1921_;
v___y_1876_ = v___y_1922_;
v___y_1877_ = v___y_1923_;
v___y_1878_ = v___y_1924_;
v___y_1879_ = v_a_1927_;
v___y_1880_ = v___y_1925_;
v___y_1881_ = v___y_1926_;
goto v___jp_1853_;
}
}
v___jp_1931_:
{
lean_object* v_options_1938_; lean_object* v_fileName_1939_; lean_object* v_fileMap_1940_; lean_object* v_currRecDepth_1941_; lean_object* v_maxRecDepth_1942_; lean_object* v_ref_1943_; lean_object* v_currNamespace_1944_; lean_object* v_openDecls_1945_; lean_object* v_initHeartbeats_1946_; lean_object* v_maxHeartbeats_1947_; lean_object* v_quotContext_1948_; lean_object* v_currMacroScope_1949_; uint8_t v_diag_1950_; lean_object* v_cancelTk_x3f_1951_; uint8_t v_suppressElabErrors_1952_; lean_object* v_inheritedTraceOptions_1953_; uint8_t v_hasTrace_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___y_1963_; uint8_t v___x_1964_; 
v_options_1938_ = lean_ctor_get(v___y_1936_, 2);
v_fileName_1939_ = lean_ctor_get(v___y_1936_, 0);
v_fileMap_1940_ = lean_ctor_get(v___y_1936_, 1);
v_currRecDepth_1941_ = lean_ctor_get(v___y_1936_, 3);
v_maxRecDepth_1942_ = lean_ctor_get(v___y_1936_, 4);
v_ref_1943_ = lean_ctor_get(v___y_1936_, 5);
v_currNamespace_1944_ = lean_ctor_get(v___y_1936_, 6);
v_openDecls_1945_ = lean_ctor_get(v___y_1936_, 7);
v_initHeartbeats_1946_ = lean_ctor_get(v___y_1936_, 8);
v_maxHeartbeats_1947_ = lean_ctor_get(v___y_1936_, 9);
v_quotContext_1948_ = lean_ctor_get(v___y_1936_, 10);
v_currMacroScope_1949_ = lean_ctor_get(v___y_1936_, 11);
v_diag_1950_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*14);
v_cancelTk_x3f_1951_ = lean_ctor_get(v___y_1936_, 12);
v_suppressElabErrors_1952_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1953_ = lean_ctor_get(v___y_1936_, 13);
v_hasTrace_1954_ = lean_ctor_get_uint8(v_options_1938_, sizeof(void*)*1);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1957_ = l_Lean_Level_getLevelOffset(v_lhs_1932_);
v___x_1958_ = l_Lean_Level_getLevelOffset(v_rhs_1933_);
v___x_1959_ = lean_level_eq(v___x_1957_, v___x_1958_);
lean_dec(v___x_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = 1;
v___x_1961_ = lean_box(v___x_1959_);
v___x_1962_ = lean_box(v___x_1960_);
lean_inc(v_rhs_1933_);
lean_inc(v_lhs_1932_);
v___y_1963_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1963_, 0, v___x_1961_);
lean_closure_set(v___y_1963_, 1, v_lhs_1932_);
lean_closure_set(v___y_1963_, 2, v_rhs_1933_);
lean_closure_set(v___y_1963_, 3, v___x_1955_);
lean_closure_set(v___y_1963_, 4, v___x_1956_);
lean_closure_set(v___y_1963_, 5, v___x_1962_);
v___x_1964_ = lean_bool_not(v_hasTrace_1954_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_inc_ref(v_inheritedTraceOptions_1953_);
lean_inc(v_cancelTk_x3f_1951_);
lean_inc(v_currMacroScope_1949_);
lean_inc(v_quotContext_1948_);
lean_inc(v_maxHeartbeats_1947_);
lean_inc(v_initHeartbeats_1946_);
lean_inc(v_openDecls_1945_);
lean_inc(v_currNamespace_1944_);
lean_inc(v_ref_1943_);
lean_inc(v_maxRecDepth_1942_);
lean_inc(v_currRecDepth_1941_);
lean_inc_ref(v_fileMap_1940_);
lean_inc_ref(v_fileName_1939_);
lean_inc_ref(v_options_1938_);
v___x_1965_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1966_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
if (v_hasTrace_1954_ == 0)
{
v___y_1900_ = v_rhs_1933_;
v___y_1901_ = v___x_1966_;
v___y_1902_ = v___x_1964_;
v___y_1903_ = v_maxHeartbeats_1947_;
v___y_1904_ = v_fileMap_1940_;
v___y_1905_ = v_lhs_1932_;
v___y_1906_ = v_diag_1950_;
v___y_1907_ = v_initHeartbeats_1946_;
v___y_1908_ = v___y_1936_;
v___y_1909_ = v_currMacroScope_1949_;
v___y_1910_ = v___y_1963_;
v___y_1911_ = v_fileName_1939_;
v___y_1912_ = v___y_1937_;
v___y_1913_ = v_cancelTk_x3f_1951_;
v___y_1914_ = v_openDecls_1945_;
v___y_1915_ = v___y_1934_;
v___y_1916_ = v___x_1965_;
v___y_1917_ = v_currRecDepth_1941_;
v___y_1918_ = v___x_1960_;
v___y_1919_ = v_quotContext_1948_;
v___y_1920_ = v_currNamespace_1944_;
v___y_1921_ = v_maxRecDepth_1942_;
v___y_1922_ = v_ref_1943_;
v___y_1923_ = v_suppressElabErrors_1952_;
v___y_1924_ = v_inheritedTraceOptions_1953_;
v___y_1925_ = v_options_1938_;
v___y_1926_ = v___y_1935_;
v_a_1927_ = v_hasTrace_1954_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1953_, v_options_1938_, v___x_1967_);
if (v___x_1968_ == 0)
{
v___y_1900_ = v_rhs_1933_;
v___y_1901_ = v___x_1966_;
v___y_1902_ = v___x_1964_;
v___y_1903_ = v_maxHeartbeats_1947_;
v___y_1904_ = v_fileMap_1940_;
v___y_1905_ = v_lhs_1932_;
v___y_1906_ = v_diag_1950_;
v___y_1907_ = v_initHeartbeats_1946_;
v___y_1908_ = v___y_1936_;
v___y_1909_ = v_currMacroScope_1949_;
v___y_1910_ = v___y_1963_;
v___y_1911_ = v_fileName_1939_;
v___y_1912_ = v___y_1937_;
v___y_1913_ = v_cancelTk_x3f_1951_;
v___y_1914_ = v_openDecls_1945_;
v___y_1915_ = v___y_1934_;
v___y_1916_ = v___x_1965_;
v___y_1917_ = v_currRecDepth_1941_;
v___y_1918_ = v___x_1960_;
v___y_1919_ = v_quotContext_1948_;
v___y_1920_ = v_currNamespace_1944_;
v___y_1921_ = v_maxRecDepth_1942_;
v___y_1922_ = v_ref_1943_;
v___y_1923_ = v_suppressElabErrors_1952_;
v___y_1924_ = v_inheritedTraceOptions_1953_;
v___y_1925_ = v_options_1938_;
v___y_1926_ = v___y_1935_;
v_a_1927_ = v___x_1968_;
goto v___jp_1899_;
}
else
{
v___y_1854_ = v_rhs_1933_;
v___y_1855_ = v___x_1964_;
v___y_1856_ = v___x_1966_;
v___y_1857_ = v_maxHeartbeats_1947_;
v___y_1858_ = v_fileMap_1940_;
v___y_1859_ = v_diag_1950_;
v___y_1860_ = v_lhs_1932_;
v___y_1861_ = v___y_1936_;
v___y_1862_ = v_initHeartbeats_1946_;
v___y_1863_ = v_currMacroScope_1949_;
v___y_1864_ = v___y_1963_;
v___y_1865_ = v_fileName_1939_;
v___y_1866_ = v___y_1937_;
v___y_1867_ = v_cancelTk_x3f_1951_;
v___y_1868_ = v_openDecls_1945_;
v___y_1869_ = v___y_1934_;
v___y_1870_ = v___x_1965_;
v___y_1871_ = v_currRecDepth_1941_;
v___y_1872_ = v___x_1960_;
v___y_1873_ = v_quotContext_1948_;
v___y_1874_ = v_currNamespace_1944_;
v___y_1875_ = v_maxRecDepth_1942_;
v___y_1876_ = v_ref_1943_;
v___y_1877_ = v_suppressElabErrors_1952_;
v___y_1878_ = v_inheritedTraceOptions_1953_;
v___y_1879_ = v___x_1968_;
v___y_1880_ = v_options_1938_;
v___y_1881_ = v___y_1935_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v___x_1969_; 
lean_dec_ref(v___y_1963_);
v___x_1969_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1959_, v_lhs_1932_, v_rhs_1933_, v___x_1955_, v___x_1956_, v___x_1960_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = lean_is_level_def_eq(v_x_1973_, v_x_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1981_, lean_object* v_x_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1982_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1989_, v_x_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2053_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2054_ = 0;
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2056_ = l_Lean_registerTraceClass(v___x_2053_, v___x_2054_, v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref_known(v___x_2056_, 1);
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2058_ = 1;
v___x_2059_ = l_Lean_registerTraceClass(v___x_2057_, v___x_2058_, v___x_2055_);
return v___x_2059_;
}
else
{
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2061_;
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
