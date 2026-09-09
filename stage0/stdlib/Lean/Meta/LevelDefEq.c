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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_47_; lean_object* v___x_926__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_926__overap_48_ = lean_panic_fn_borrowed(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_926__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
size_t v_x_2638__boxed_196_; size_t v_x_2639__boxed_197_; lean_object* v_res_198_; 
v_x_2638__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_x_2639__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_191_, v_x_2638__boxed_196_, v_x_2639__boxed_197_, v_x_194_, v_x_195_);
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
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_lAssignment_226_, v_mvarId_206_, v_val_207_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 7, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
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
lean_ctor_set(v_reuseFailAlloc_242_, 7, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_eAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 9, v_dAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_242_, 10, v_instanceTypedMVars_229_);
v___x_235_ = v_reuseFailAlloc_242_;
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
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_zetaDeltaFVarIds_213_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_postponed_214_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_diag_215_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_put(v___y_208_, v___x_237_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
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
lean_object* v___x_256_; lean_object* v_env_257_; lean_object* v___x_258_; lean_object* v_mctx_259_; lean_object* v_lctx_260_; lean_object* v_options_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_256_ = lean_st_ref_get(v___y_254_);
v_env_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_env_257_);
lean_dec(v___x_256_);
v___x_258_ = lean_st_ref_get(v___y_252_);
v_mctx_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_mctx_259_);
lean_dec(v___x_258_);
v_lctx_260_ = lean_ctor_get(v___y_251_, 2);
v_options_261_ = lean_ctor_get(v___y_253_, 1);
lean_inc_ref(v_options_261_);
lean_inc_ref(v_lctx_260_);
v___x_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_262_, 0, v_env_257_);
lean_ctor_set(v___x_262_, 1, v_mctx_259_);
lean_ctor_set(v___x_262_, 2, v_lctx_260_);
lean_ctor_set(v___x_262_, 3, v_options_261_);
v___x_263_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_msgData_250_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3___boxed(lean_object* v_msgData_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msgData_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0(void){
_start:
{
lean_object* v___x_272_; double v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_float_of_nat(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(lean_object* v_cls_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_ref_284_; lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_330_; 
v_ref_284_ = lean_ctor_get(v___y_281_, 4);
v___x_285_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_330_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_330_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_330_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v_traceState_291_; lean_object* v_env_292_; lean_object* v_nextMacroScope_293_; lean_object* v_ngen_294_; lean_object* v_auxDeclNGen_295_; lean_object* v_cache_296_; lean_object* v_messages_297_; lean_object* v_infoState_298_; lean_object* v_snapshotTasks_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_329_; 
v___x_290_ = lean_st_ref_take(v___y_282_);
v_traceState_291_ = lean_ctor_get(v___x_290_, 4);
v_env_292_ = lean_ctor_get(v___x_290_, 0);
v_nextMacroScope_293_ = lean_ctor_get(v___x_290_, 1);
v_ngen_294_ = lean_ctor_get(v___x_290_, 2);
v_auxDeclNGen_295_ = lean_ctor_get(v___x_290_, 3);
v_cache_296_ = lean_ctor_get(v___x_290_, 5);
v_messages_297_ = lean_ctor_get(v___x_290_, 6);
v_infoState_298_ = lean_ctor_get(v___x_290_, 7);
v_snapshotTasks_299_ = lean_ctor_get(v___x_290_, 8);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_329_ == 0)
{
v___x_301_ = v___x_290_;
v_isShared_302_ = v_isSharedCheck_329_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snapshotTasks_299_);
lean_inc(v_infoState_298_);
lean_inc(v_messages_297_);
lean_inc(v_cache_296_);
lean_inc(v_traceState_291_);
lean_inc(v_auxDeclNGen_295_);
lean_inc(v_ngen_294_);
lean_inc(v_nextMacroScope_293_);
lean_inc(v_env_292_);
lean_dec(v___x_290_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_329_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint64_t v_tid_303_; lean_object* v_traces_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_328_; 
v_tid_303_ = lean_ctor_get_uint64(v_traceState_291_, sizeof(void*)*1);
v_traces_304_ = lean_ctor_get(v_traceState_291_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_traceState_291_);
if (v_isSharedCheck_328_ == 0)
{
v___x_306_ = v_traceState_291_;
v_isShared_307_ = v_isSharedCheck_328_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_traces_304_);
lean_dec(v_traceState_291_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_328_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; double v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_310_ = 0;
v___x_311_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_312_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_312_, 0, v_cls_277_);
lean_ctor_set(v___x_312_, 1, v___x_308_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
lean_ctor_set_float(v___x_312_, sizeof(void*)*3, v___x_309_);
lean_ctor_set_float(v___x_312_, sizeof(void*)*3 + 8, v___x_309_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*3 + 16, v___x_310_);
v___x_313_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_314_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v_a_286_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_inc(v_ref_284_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_ref_284_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = l_Lean_PersistentArray_push___redArg(v_traces_304_, v___x_315_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_316_);
v___x_318_ = v___x_306_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_316_);
lean_ctor_set_uint64(v_reuseFailAlloc_327_, sizeof(void*)*1, v_tid_303_);
v___x_318_ = v_reuseFailAlloc_327_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 4, v___x_318_);
v___x_320_ = v___x_301_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_env_292_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_nextMacroScope_293_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ngen_294_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_auxDeclNGen_295_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v_cache_296_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_messages_297_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_infoState_298_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_snapshotTasks_299_);
v___x_320_ = v_reuseFailAlloc_326_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_321_ = lean_st_ref_put(v___y_282_, v___x_320_);
v___x_322_ = lean_box(0);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_322_);
v___x_324_ = v___x_288_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_331_, lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_331_, v_msg_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_343_ = lean_unsigned_to_nat(2u);
v___x_344_ = lean_unsigned_to_nat(39u);
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_347_ = l_mkPanicMessageWithDecl(v___x_346_, v___x_345_, v___x_344_, v___x_343_, v___x_342_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_360_ = l_Lean_Name_append(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_367_, lean_object* v_v_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = l_Lean_Level_isMax(v_v_368_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_v_368_);
lean_dec(v_mvarId_367_);
v___x_375_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_376_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_375_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_mkFreshLevelMVar(v_a_369_, v_a_370_, v_a_371_, v_a_372_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_options_378_; lean_object* v_a_379_; lean_object* v_toCold_380_; uint8_t v_hasTrace_381_; lean_object* v___x_382_; 
v_options_378_ = lean_ctor_get(v_a_371_, 1);
v_a_379_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_377_, 1);
v_toCold_380_ = lean_ctor_get(v_a_371_, 0);
v_hasTrace_381_ = lean_ctor_get_uint8(v_options_378_, sizeof(void*)*1);
v___x_382_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_367_, v_v_368_, v_a_379_);
if (v_hasTrace_381_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_367_, v___x_382_, v_a_370_);
return v___x_383_;
}
else
{
lean_object* v_inheritedTraceOptions_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_inheritedTraceOptions_384_ = lean_ctor_get(v_toCold_380_, 4);
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_386_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_384_, v_options_378_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_367_, v___x_382_, v_a_370_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_389_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_367_);
v___x_390_ = l_Lean_mkLevelMVar(v_mvarId_367_);
v___x_391_ = l_Lean_MessageData_ofLevel(v___x_390_);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_389_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_inc(v___x_382_);
v___x_395_ = l_Lean_MessageData_ofLevel(v___x_382_);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_385_, v___x_396_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; 
lean_dec_ref_known(v___x_397_, 1);
v___x_398_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_367_, v___x_382_, v_a_370_);
return v___x_398_;
}
else
{
lean_dec(v___x_382_);
lean_dec(v_mvarId_367_);
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_v_368_);
lean_dec(v_mvarId_367_);
v_a_399_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_377_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_377_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___boxed(lean_object* v_mvarId_407_, lean_object* v_v_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v_mvarId_407_, v_v_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* v_mvarId_415_, lean_object* v_val_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_415_, v_val_416_, v___y_418_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* v_mvarId_423_, lean_object* v_val_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(v_mvarId_423_, v_val_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1___redArg(v_x_432_, v_x_433_, v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_436_, lean_object* v_x_437_, size_t v_x_438_, size_t v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_437_, v_x_438_, v_x_439_, v_x_440_, v_x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
size_t v_x_3146__boxed_449_; size_t v_x_3147__boxed_450_; lean_object* v_res_451_; 
v_x_3146__boxed_449_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_x_3147__boxed_450_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_res_451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_443_, v_x_444_, v_x_3146__boxed_449_, v_x_3147__boxed_450_, v_x_447_, v_x_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_452_, lean_object* v_n_453_, lean_object* v_k_454_, lean_object* v_v_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5___redArg(v_n_453_, v_k_454_, v_v_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_457_, size_t v_depth_458_, lean_object* v_keys_459_, lean_object* v_vals_460_, lean_object* v_heq_461_, lean_object* v_i_462_, lean_object* v_entries_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___redArg(v_depth_458_, v_keys_459_, v_vals_460_, v_i_462_, v_entries_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_465_, lean_object* v_depth_466_, lean_object* v_keys_467_, lean_object* v_vals_468_, lean_object* v_heq_469_, lean_object* v_i_470_, lean_object* v_entries_471_){
_start:
{
size_t v_depth_boxed_472_; lean_object* v_res_473_; 
v_depth_boxed_472_ = lean_unbox_usize(v_depth_466_);
lean_dec(v_depth_466_);
v_res_473_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__6(v_00_u03b2_465_, v_depth_boxed_472_, v_keys_467_, v_vals_468_, v_heq_469_, v_i_470_, v_entries_471_);
lean_dec_ref(v_vals_468_);
lean_dec_ref(v_keys_467_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_x_475_, v_x_476_, v_x_477_, v_x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__0));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* v_u_483_, lean_object* v_v_x27_484_, lean_object* v_mvarId_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
uint8_t v___x_491_; lean_object* v___y_493_; 
v___x_491_ = lean_level_eq(v_u_483_, v_v_x27_484_);
if (v___x_491_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_mvarId_485_);
lean_dec(v_u_483_);
v___x_504_ = lean_box(v___x_491_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v_options_506_; uint8_t v_hasTrace_507_; 
v_options_506_ = lean_ctor_get(v_a_488_, 1);
v_hasTrace_507_ = lean_ctor_get_uint8(v_options_506_, sizeof(void*)*1);
if (v_hasTrace_507_ == 0)
{
v___y_493_ = v_a_487_;
goto v___jp_492_;
}
else
{
lean_object* v_toCold_508_; lean_object* v_inheritedTraceOptions_509_; lean_object* v_cls_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_toCold_508_ = lean_ctor_get(v_a_488_, 0);
v_inheritedTraceOptions_509_ = lean_ctor_get(v_toCold_508_, 4);
v_cls_510_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_511_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_509_, v_options_506_, v___x_511_);
if (v___x_512_ == 0)
{
v___y_493_ = v_a_487_;
goto v___jp_492_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_513_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_485_);
v___x_514_ = l_Lean_mkLevelMVar(v_mvarId_485_);
v___x_515_ = l_Lean_MessageData_ofLevel(v___x_514_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
lean_inc(v_u_483_);
v___x_519_ = l_Lean_MessageData_ofLevel(v_u_483_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_510_, v___x_520_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_dec_ref_known(v___x_521_, 1);
v___y_493_ = v_a_487_;
goto v___jp_492_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_mvarId_485_);
lean_dec(v_u_483_);
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
v___jp_492_:
{
lean_object* v___x_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v___x_494_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_485_, v_u_483_, v___y_493_);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_494_, 0);
lean_dec(v_unused_503_);
v___x_496_ = v___x_494_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_dec(v___x_494_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_box(v___x_491_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
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
v_options_606_ = lean_ctor_get(v_a_574_, 1);
v_hasTrace_607_ = lean_ctor_get_uint8(v_options_606_, sizeof(void*)*1);
if (v_hasTrace_607_ == 0)
{
v___y_592_ = v_a_573_;
goto v___jp_591_;
}
else
{
lean_object* v_toCold_608_; lean_object* v_inheritedTraceOptions_609_; lean_object* v_cls_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_toCold_608_ = lean_ctor_get(v_a_574_, 0);
v_inheritedTraceOptions_609_ = lean_ctor_get(v_toCold_608_, 4);
v_cls_610_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_611_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_609_, v_options_606_, v___x_611_);
if (v___x_612_ == 0)
{
v___y_592_ = v_a_573_;
goto v___jp_591_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_613_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_571_);
v___x_614_ = l_Lean_mkLevelMVar(v_mvarId_571_);
v___x_615_ = l_Lean_MessageData_ofLevel(v___x_614_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
lean_inc(v_u_u2081_568_);
v___x_619_ = l_Lean_MessageData_ofLevel(v_u_u2081_568_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_610_, v___x_620_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_dec_ref_known(v___x_621_, 1);
v___y_592_ = v_a_573_;
goto v___jp_591_;
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_mvarId_571_);
lean_dec(v_u_u2081_568_);
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_630_; uint8_t v_hasTrace_631_; 
lean_dec(v_u_u2081_568_);
v_options_630_ = lean_ctor_get(v_a_574_, 1);
v_hasTrace_631_ = lean_ctor_get_uint8(v_options_630_, sizeof(void*)*1);
if (v_hasTrace_631_ == 0)
{
v___y_580_ = v_a_573_;
goto v___jp_579_;
}
else
{
lean_object* v_toCold_632_; lean_object* v_inheritedTraceOptions_633_; lean_object* v_cls_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_toCold_632_ = lean_ctor_get(v_a_574_, 0);
v_inheritedTraceOptions_633_ = lean_ctor_get(v_toCold_632_, 4);
v_cls_634_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_635_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_633_, v_options_630_, v___x_635_);
if (v___x_636_ == 0)
{
v___y_580_ = v_a_573_;
goto v___jp_579_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_637_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_571_);
v___x_638_ = l_Lean_mkLevelMVar(v_mvarId_571_);
v___x_639_ = l_Lean_MessageData_ofLevel(v___x_638_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_637_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_inc(v_u_u2082_569_);
v___x_643_ = l_Lean_MessageData_ofLevel(v_u_u2082_569_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_634_, v___x_644_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref_known(v___x_645_, 1);
v___y_580_ = v_a_573_;
goto v___jp_579_;
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_mvarId_571_);
lean_dec(v_u_u2082_569_);
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_654_, lean_object* v_u_u2082_655_, lean_object* v_v_x27_656_, lean_object* v_mvarId_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_654_, v_u_u2082_655_, v_v_x27_656_, v_mvarId_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_v_x27_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_664_, lean_object* v_v_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
if (lean_obj_tag(v_u_664_) == 2)
{
if (lean_obj_tag(v_v_665_) == 2)
{
lean_object* v_a_675_; 
v_a_675_ = lean_ctor_get(v_v_665_, 1);
lean_inc(v_a_675_);
if (lean_obj_tag(v_a_675_) == 5)
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_676_ = lean_ctor_get(v_u_664_, 0);
lean_inc(v_a_676_);
v_a_677_ = lean_ctor_get(v_u_664_, 1);
lean_inc(v_a_677_);
lean_dec_ref_known(v_u_664_, 2);
v_a_678_ = lean_ctor_get(v_v_665_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v_v_665_, 2);
v_a_679_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v_a_675_, 1);
v___x_680_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_678_);
return v___x_680_;
}
else
{
lean_object* v_a_681_; 
v_a_681_ = lean_ctor_get(v_v_665_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v_v_665_, 2);
if (lean_obj_tag(v_a_681_) == 5)
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_685_; 
v_a_682_ = lean_ctor_get(v_u_664_, 0);
lean_inc(v_a_682_);
v_a_683_ = lean_ctor_get(v_u_664_, 1);
lean_inc(v_a_683_);
lean_dec_ref_known(v_u_664_, 2);
v_a_684_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v_a_681_, 1);
v___x_685_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_682_, v_a_683_, v_a_675_, v_a_684_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_675_);
return v___x_685_;
}
else
{
lean_dec(v_a_681_);
lean_dec(v_a_675_);
lean_dec_ref_known(v_u_664_, 2);
goto v___jp_671_;
}
}
}
else
{
lean_dec_ref_known(v_u_664_, 2);
lean_dec(v_v_665_);
goto v___jp_671_;
}
}
else
{
lean_dec(v_v_665_);
lean_dec(v_u_664_);
goto v___jp_671_;
}
v___jp_671_:
{
uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = 0;
v___x_673_ = lean_box(v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_686_, lean_object* v_v_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_686_, v_v_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_693_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_701_ = l_Lean_Name_append(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_705_, lean_object* v_rhs_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_toCold_712_; lean_object* v_options_713_; lean_object* v_ref_714_; lean_object* v___y_716_; uint8_t v_hasTrace_736_; 
v_toCold_712_ = lean_ctor_get(v_a_709_, 0);
v_options_713_ = lean_ctor_get(v_a_709_, 1);
v_ref_714_ = lean_ctor_get(v_a_709_, 4);
v_hasTrace_736_ = lean_ctor_get_uint8(v_options_713_, sizeof(void*)*1);
if (v_hasTrace_736_ == 0)
{
v___y_716_ = v_a_708_;
goto v___jp_715_;
}
else
{
lean_object* v_inheritedTraceOptions_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_inheritedTraceOptions_737_ = lean_ctor_get(v_toCold_712_, 4);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_739_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_740_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_737_, v_options_713_, v___x_739_);
if (v___x_740_ == 0)
{
v___y_716_ = v_a_708_;
goto v___jp_715_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_inc(v_lhs_705_);
v___x_741_ = l_Lean_MessageData_ofLevel(v_lhs_705_);
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_inc(v_rhs_706_);
v___x_744_ = l_Lean_MessageData_ofLevel(v_rhs_706_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_738_, v___x_745_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref_known(v___x_746_, 1);
v___y_716_ = v_a_708_;
goto v___jp_715_;
}
else
{
lean_dec(v_rhs_706_);
lean_dec(v_lhs_705_);
return v___x_746_;
}
}
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v_mctx_718_; lean_object* v_cache_719_; lean_object* v_zetaDeltaFVarIds_720_; lean_object* v_postponed_721_; lean_object* v_diag_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_735_; 
v___x_717_ = lean_st_ref_take(v___y_716_);
v_mctx_718_ = lean_ctor_get(v___x_717_, 0);
v_cache_719_ = lean_ctor_get(v___x_717_, 1);
v_zetaDeltaFVarIds_720_ = lean_ctor_get(v___x_717_, 2);
v_postponed_721_ = lean_ctor_get(v___x_717_, 3);
v_diag_722_ = lean_ctor_get(v___x_717_, 4);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_735_ == 0)
{
v___x_724_ = v___x_717_;
v_isShared_725_ = v_isSharedCheck_735_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_diag_722_);
lean_inc(v_postponed_721_);
lean_inc(v_zetaDeltaFVarIds_720_);
lean_inc(v_cache_719_);
lean_inc(v_mctx_718_);
lean_dec(v___x_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_735_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_defEqCtx_x3f_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v_defEqCtx_x3f_726_ = lean_ctor_get(v_a_707_, 4);
lean_inc(v_defEqCtx_x3f_726_);
lean_inc(v_ref_714_);
v___x_727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_727_, 0, v_ref_714_);
lean_ctor_set(v___x_727_, 1, v_lhs_705_);
lean_ctor_set(v___x_727_, 2, v_rhs_706_);
lean_ctor_set(v___x_727_, 3, v_defEqCtx_x3f_726_);
v___x_728_ = l_Lean_PersistentArray_push___redArg(v_postponed_721_, v___x_727_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 3, v___x_728_);
v___x_730_ = v___x_724_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_mctx_718_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_cache_719_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_zetaDeltaFVarIds_720_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_diag_722_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_st_ref_put(v___y_716_, v___x_730_);
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_747_, lean_object* v_rhs_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_747_, v_rhs_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_755_, lean_object* v_mvarId_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
if (lean_obj_tag(v_v_755_) == 5)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v_v_755_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v_v_755_, 1);
v___x_763_ = l_Lean_LMVarId_getLevel(v_a_762_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_LMVarId_getLevel(v_mvarId_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_nat_dec_lt(v_a_766_, v_a_764_);
lean_dec(v_a_764_);
lean_dec(v_a_766_);
v___x_771_ = lean_box(v___x_770_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_764_);
v_a_776_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_765_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_765_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_mvarId_756_);
v_a_784_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_763_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_763_);
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
else
{
uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v_mvarId_756_);
lean_dec(v_v_755_);
v___x_792_ = 0;
v___x_793_ = lean_box(v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_795_, lean_object* v_mvarId_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_795_, v_mvarId_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_803_, lean_object* v_v_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___y_811_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_886_; lean_object* v___y_900_; 
switch(lean_obj_tag(v_u_803_))
{
case 5:
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v_u_803_, 0);
lean_inc(v_a_913_);
v___x_914_ = l_Lean_LMVarId_isReadOnly(v_a_913_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_1011_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_1011_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_1011_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___x_919_; 
v___x_919_ = lean_unbox(v_a_915_);
lean_dec(v_a_915_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_del_object(v___x_917_);
lean_inc(v_a_913_);
lean_inc(v_v_804_);
v___x_920_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_804_, v_a_913_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_997_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_997_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_997_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_997_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_a_921_);
lean_dec(v_a_921_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; 
v___x_932_ = l_Lean_Level_occurs(v_u_803_, v_v_804_);
if (v___x_932_ == 0)
{
lean_object* v_options_933_; uint8_t v_hasTrace_934_; 
lean_del_object(v___x_923_);
v_options_933_ = lean_ctor_get(v_a_807_, 1);
v_hasTrace_934_ = lean_ctor_get_uint8(v_options_933_, sizeof(void*)*1);
if (v_hasTrace_934_ == 0)
{
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_a_805_);
v___y_886_ = v_a_806_;
goto v___jp_885_;
}
else
{
lean_object* v_toCold_935_; lean_object* v_inheritedTraceOptions_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_toCold_935_ = lean_ctor_get(v_a_807_, 0);
v_inheritedTraceOptions_936_ = lean_ctor_get(v_toCold_935_, 4);
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_936_, v_options_933_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_a_805_);
v___y_886_ = v_a_806_;
goto v___jp_885_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_inc_ref(v_u_803_);
v___x_940_ = l_Lean_MessageData_ofLevel(v_u_803_);
v___x_941_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
lean_inc(v_v_804_);
v___x_943_ = l_Lean_MessageData_ofLevel(v_v_804_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_937_, v___x_944_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_a_805_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_dec_ref_known(v___x_945_, 1);
v___y_886_ = v_a_806_;
goto v___jp_885_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_806_);
lean_dec(v_v_804_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
else
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Level_isMax(v_v_804_);
if (v___x_954_ == 0)
{
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
goto v___jp_925_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_803_, v_v_804_);
if (v___x_955_ == 0)
{
if (v___x_954_ == 0)
{
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
goto v___jp_925_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_del_object(v___x_923_);
v___x_956_ = l_Lean_Level_mvarId_x21(v_u_803_);
lean_dec_ref_known(v_u_803_, 1);
v___x_957_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_956_, v_v_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_966_; 
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_957_, 0);
lean_dec(v_unused_967_);
v___x_959_ = v___x_957_;
v_isShared_960_ = v_isSharedCheck_966_;
goto v_resetjp_958_;
}
else
{
lean_dec(v___x_957_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_966_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_961_ = 1;
v___x_962_ = lean_box(v___x_961_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_957_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_957_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
goto v___jp_925_;
}
}
}
}
else
{
lean_object* v_options_976_; uint8_t v_hasTrace_977_; 
lean_del_object(v___x_923_);
v_options_976_ = lean_ctor_get(v_a_807_, 1);
v_hasTrace_977_ = lean_ctor_get_uint8(v_options_976_, sizeof(void*)*1);
if (v_hasTrace_977_ == 0)
{
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_a_805_);
v___y_900_ = v_a_806_;
goto v___jp_899_;
}
else
{
lean_object* v_toCold_978_; lean_object* v_inheritedTraceOptions_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_toCold_978_ = lean_ctor_get(v_a_807_, 0);
v_inheritedTraceOptions_979_ = lean_ctor_get(v_toCold_978_, 4);
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_981_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_982_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_979_, v_options_976_, v___x_981_);
if (v___x_982_ == 0)
{
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_a_805_);
v___y_900_ = v_a_806_;
goto v___jp_899_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_inc(v_v_804_);
v___x_983_ = l_Lean_MessageData_ofLevel(v_v_804_);
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
lean_inc_ref(v_u_803_);
v___x_986_ = l_Lean_MessageData_ofLevel(v_u_803_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_980_, v___x_987_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_a_805_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_dec_ref_known(v___x_988_, 1);
v___y_900_ = v_a_806_;
goto v___jp_899_;
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_806_);
lean_dec(v_v_804_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
v___jp_925_:
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = 2;
v___x_927_ = lean_box(v___x_926_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
v_a_998_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_920_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_920_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
v___x_1006_ = 2;
v___x_1007_ = lean_box(v___x_1006_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_1007_);
v___x_1009_ = v___x_917_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref_known(v_u_803_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
v_a_1012_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_914_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_914_);
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
case 0:
{
switch(lean_obj_tag(v_v_804_))
{
case 5:
{
lean_dec_ref_known(v_v_804_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
goto v___jp_881_;
}
case 2:
{
lean_object* v_a_1020_; lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1020_ = lean_ctor_get(v_v_804_, 0);
lean_inc(v_a_1020_);
v_a_1021_ = lean_ctor_get(v_v_804_, 1);
lean_inc(v_a_1021_);
lean_dec_ref_known(v_v_804_, 2);
lean_inc(v_a_808_);
lean_inc_ref(v_a_807_);
lean_inc(v_a_806_);
lean_inc_ref(v_a_805_);
v___x_1022_ = lean_is_level_def_eq(v_u_803_, v_a_1020_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; uint8_t v___x_1024_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
v___x_1024_ = lean_unbox(v_a_1023_);
lean_dec(v_a_1023_);
if (v___x_1024_ == 0)
{
lean_dec(v_a_1021_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
v___y_811_ = v___x_1022_;
goto v___jp_810_;
}
else
{
lean_object* v___x_1025_; 
lean_dec_ref_known(v___x_1022_, 1);
v___x_1025_ = lean_is_level_def_eq(v_u_803_, v_a_1021_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
v___y_811_ = v___x_1025_;
goto v___jp_810_;
}
}
else
{
lean_dec(v_a_1021_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
v___y_811_ = v___x_1022_;
goto v___jp_810_;
}
}
case 3:
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v_v_804_, 1);
lean_inc(v_a_1026_);
lean_dec_ref_known(v_v_804_, 2);
v___x_1027_ = lean_is_level_def_eq(v_u_803_, v_a_1026_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
uint8_t v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1032_ = lean_unbox(v_a_1028_);
lean_dec(v_a_1028_);
v___x_1033_ = l_Lean_Bool_toLBool(v___x_1032_);
v___x_1034_ = lean_box(v___x_1033_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_a_1039_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1027_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1027_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
case 1:
{
uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref_known(v_v_804_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
v___x_1047_ = 0;
v___x_1048_ = lean_box(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
default: 
{
v___y_836_ = v_a_805_;
v___y_837_ = v_a_806_;
v___y_838_ = v_a_807_;
v___y_839_ = v_a_808_;
goto v___jp_835_;
}
}
}
case 1:
{
lean_object* v_a_1050_; uint8_t v___y_1052_; 
v_a_1050_ = lean_ctor_get(v_u_803_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_u_803_, 1);
if (lean_obj_tag(v_v_804_) == 5)
{
lean_dec_ref_known(v_v_804_, 1);
lean_dec(v_a_1050_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
goto v___jp_881_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_Level_isParam(v_v_804_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Level_isMVar(v_a_1050_);
if (v___x_1097_ == 0)
{
v___y_1052_ = v___x_1096_;
goto v___jp_1051_;
}
else
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Level_occurs(v_a_1050_, v_v_804_);
v___y_1052_ = v___x_1098_;
goto v___jp_1051_;
}
}
else
{
uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_a_1050_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
v___x_1099_ = 0;
v___x_1100_ = lean_box(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
v___jp_1051_:
{
if (v___y_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_decLevel_x3f(v_v_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1084_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1084_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1084_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
if (lean_obj_tag(v_a_1054_) == 0)
{
uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec(v_a_1050_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
v___x_1058_ = 2;
v___x_1059_ = lean_box(v___x_1058_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v_val_1063_; lean_object* v___x_1064_; 
lean_del_object(v___x_1056_);
v_val_1063_ = lean_ctor_get(v_a_1054_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v_a_1054_, 1);
v___x_1064_ = lean_is_level_def_eq(v_a_1050_, v_val_1063_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
uint8_t v___x_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1069_ = lean_unbox(v_a_1065_);
lean_dec(v_a_1065_);
v___x_1070_ = l_Lean_Bool_toLBool(v___x_1069_);
v___x_1071_ = lean_box(v___x_1070_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1071_);
v___x_1073_ = v___x_1067_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1064_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1064_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_a_1050_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
v_a_1085_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1053_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1053_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v_a_1050_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_v_804_);
v___x_1093_ = 2;
v___x_1094_ = lean_box(v___x_1093_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_804_) == 5)
{
lean_dec_ref_known(v_v_804_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_u_803_);
goto v___jp_881_;
}
else
{
v___y_836_ = v_a_805_;
v___y_837_ = v_a_806_;
v___y_838_ = v_a_807_;
v___y_839_ = v_a_808_;
goto v___jp_835_;
}
}
}
v___jp_810_:
{
if (lean_obj_tag(v___y_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_822_; 
v_a_812_ = lean_ctor_get(v___y_811_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_822_ == 0)
{
v___x_814_ = v___y_811_;
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___y_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_816_ = lean_unbox(v_a_812_);
lean_dec(v_a_812_);
v___x_817_ = l_Lean_Bool_toLBool(v___x_816_);
v___x_818_ = lean_box(v___x_817_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_818_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___y_811_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___y_811_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___y_811_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
v___jp_831_:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = 2;
v___x_833_ = lean_box(v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
v___jp_835_:
{
uint8_t v_univApprox_840_; 
v_univApprox_840_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*7 + 1);
if (v_univApprox_840_ == 0)
{
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_v_804_);
lean_dec(v_u_803_);
goto v___jp_831_;
}
else
{
lean_object* v___x_841_; 
lean_inc(v_v_804_);
lean_inc(v_u_803_);
v___x_841_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_803_, v_v_804_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_872_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_872_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_872_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_872_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint8_t v___x_846_; 
v___x_846_ = lean_unbox(v_a_842_);
lean_dec(v_a_842_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_del_object(v___x_844_);
v___x_847_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_803_, v_v_804_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_858_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
if (v___x_852_ == 0)
{
lean_del_object(v___x_850_);
goto v___jp_831_;
}
else
{
uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = 1;
v___x_854_ = lean_box(v___x_853_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_847_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_847_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_v_804_);
lean_dec(v_u_803_);
v___x_867_ = 1;
v___x_868_ = lean_box(v___x_867_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_868_);
v___x_870_ = v___x_844_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
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
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v_v_804_);
lean_dec(v_u_803_);
v_a_873_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_841_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_841_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
v___jp_881_:
{
uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = 2;
v___x_883_ = lean_box(v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_897_; 
v___x_887_ = l_Lean_Level_mvarId_x21(v_u_803_);
lean_dec(v_u_803_);
v___x_888_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_887_, v_v_804_, v___y_886_);
lean_dec(v___y_886_);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_898_);
v___x_890_ = v___x_888_;
v_isShared_891_ = v_isSharedCheck_897_;
goto v_resetjp_889_;
}
else
{
lean_dec(v___x_888_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_897_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_892_ = 1;
v___x_893_ = lean_box(v___x_892_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_911_; 
v___x_901_ = l_Lean_Level_mvarId_x21(v_v_804_);
lean_dec(v_v_804_);
v___x_902_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_901_, v_u_803_, v___y_900_);
lean_dec(v___y_900_);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_902_, 0);
lean_dec(v_unused_912_);
v___x_904_ = v___x_902_;
v_isShared_905_ = v_isSharedCheck_911_;
goto v_resetjp_903_;
}
else
{
lean_dec(v___x_902_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_911_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = 1;
v___x_907_ = lean_box(v___x_906_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1102_, lean_object* v_v_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1102_, v_v_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_mctx_1114_; lean_object* v___x_1115_; lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v___x_1118_; lean_object* v_cache_1119_; lean_object* v_zetaDeltaFVarIds_1120_; lean_object* v_postponed_1121_; lean_object* v_diag_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1131_; 
v___x_1113_ = lean_st_ref_get(v___y_1111_);
v_mctx_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_mctx_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = lean_instantiate_level_mvars(v_mctx_1114_, v_l_1110_);
v_fst_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_fst_1116_);
v_snd_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_snd_1117_);
lean_dec_ref(v___x_1115_);
v___x_1118_ = lean_st_ref_take(v___y_1111_);
v_cache_1119_ = lean_ctor_get(v___x_1118_, 1);
v_zetaDeltaFVarIds_1120_ = lean_ctor_get(v___x_1118_, 2);
v_postponed_1121_ = lean_ctor_get(v___x_1118_, 3);
v_diag_1122_ = lean_ctor_get(v___x_1118_, 4);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1132_);
v___x_1124_ = v___x_1118_;
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_diag_1122_);
lean_inc(v_postponed_1121_);
lean_inc(v_zetaDeltaFVarIds_1120_);
lean_inc(v_cache_1119_);
lean_dec(v___x_1118_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_fst_1116_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_fst_1116_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_cache_1119_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_zetaDeltaFVarIds_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_postponed_1121_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_diag_1122_);
v___x_1127_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_st_ref_put(v___y_1111_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_snd_1117_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1133_, v___y_1134_);
lean_dec(v___y_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1137_, v___y_1139_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(32u);
v___x_1152_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((size_t)5ULL);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_unsigned_to_nat(32u);
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
v___x_1158_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1159_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1157_);
lean_ctor_set(v___x_1159_, 2, v___x_1155_);
lean_ctor_set(v___x_1159_, 3, v___x_1155_);
lean_ctor_set_usize(v___x_1159_, 4, v___x_1154_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v_traceState_1163_; lean_object* v_traces_1164_; lean_object* v___x_1165_; lean_object* v_traceState_1166_; lean_object* v_env_1167_; lean_object* v_nextMacroScope_1168_; lean_object* v_ngen_1169_; lean_object* v_auxDeclNGen_1170_; lean_object* v_cache_1171_; lean_object* v_messages_1172_; lean_object* v_infoState_1173_; lean_object* v_snapshotTasks_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1193_; 
v___x_1162_ = lean_st_ref_get(v___y_1160_);
v_traceState_1163_ = lean_ctor_get(v___x_1162_, 4);
lean_inc_ref(v_traceState_1163_);
lean_dec(v___x_1162_);
v_traces_1164_ = lean_ctor_get(v_traceState_1163_, 0);
lean_inc_ref(v_traces_1164_);
lean_dec_ref(v_traceState_1163_);
v___x_1165_ = lean_st_ref_take(v___y_1160_);
v_traceState_1166_ = lean_ctor_get(v___x_1165_, 4);
v_env_1167_ = lean_ctor_get(v___x_1165_, 0);
v_nextMacroScope_1168_ = lean_ctor_get(v___x_1165_, 1);
v_ngen_1169_ = lean_ctor_get(v___x_1165_, 2);
v_auxDeclNGen_1170_ = lean_ctor_get(v___x_1165_, 3);
v_cache_1171_ = lean_ctor_get(v___x_1165_, 5);
v_messages_1172_ = lean_ctor_get(v___x_1165_, 6);
v_infoState_1173_ = lean_ctor_get(v___x_1165_, 7);
v_snapshotTasks_1174_ = lean_ctor_get(v___x_1165_, 8);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1176_ = v___x_1165_;
v_isShared_1177_ = v_isSharedCheck_1193_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snapshotTasks_1174_);
lean_inc(v_infoState_1173_);
lean_inc(v_messages_1172_);
lean_inc(v_cache_1171_);
lean_inc(v_traceState_1166_);
lean_inc(v_auxDeclNGen_1170_);
lean_inc(v_ngen_1169_);
lean_inc(v_nextMacroScope_1168_);
lean_inc(v_env_1167_);
lean_dec(v___x_1165_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1193_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
uint64_t v_tid_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1191_; 
v_tid_1178_ = lean_ctor_get_uint64(v_traceState_1166_, sizeof(void*)*1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_traceState_1166_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_traceState_1166_, 0);
lean_dec(v_unused_1192_);
v___x_1180_ = v_traceState_1166_;
v_isShared_1181_ = v_isSharedCheck_1191_;
goto v_resetjp_1179_;
}
else
{
lean_dec(v_traceState_1166_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1191_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1182_);
lean_ctor_set_uint64(v_reuseFailAlloc_1190_, sizeof(void*)*1, v_tid_1178_);
v___x_1184_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 4, v___x_1184_);
v___x_1186_ = v___x_1176_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_env_1167_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_nextMacroScope_1168_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_ngen_1169_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_auxDeclNGen_1170_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1189_, 5, v_cache_1171_);
lean_ctor_set(v_reuseFailAlloc_1189_, 6, v_messages_1172_);
lean_ctor_set(v_reuseFailAlloc_1189_, 7, v_infoState_1173_);
lean_ctor_set(v_reuseFailAlloc_1189_, 8, v_snapshotTasks_1174_);
v___x_1186_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_st_ref_put(v___y_1160_, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_traces_1164_);
return v___x_1188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1194_);
lean_dec(v___y_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1209_, lean_object* v_k_1210_, uint8_t v_v_1211_){
_start:
{
lean_object* v_map_1212_; uint8_t v_hasTrace_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1227_; 
v_map_1212_ = lean_ctor_get(v_o_1209_, 0);
v_hasTrace_1213_ = lean_ctor_get_uint8(v_o_1209_, sizeof(void*)*1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_o_1209_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1215_ = v_o_1209_;
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_map_1212_);
lean_dec(v_o_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1217_, 0, v_v_1211_);
lean_inc(v_k_1210_);
v___x_1218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1210_, v___x_1217_, v_map_1212_);
if (v_hasTrace_1213_ == 0)
{
lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1222_; 
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1220_ = l_Lean_Name_isPrefixOf(v___x_1219_, v_k_1210_);
lean_dec(v_k_1210_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1218_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1218_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_ctor_set_uint8(v___x_1222_, sizeof(void*)*1, v___x_1220_);
return v___x_1222_;
}
}
else
{
lean_object* v___x_1225_; 
lean_dec(v_k_1210_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1218_);
v___x_1225_ = v___x_1215_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*1, v_hasTrace_1213_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1228_, lean_object* v_k_1229_, lean_object* v_v_1230_){
_start:
{
uint8_t v_v_boxed_1231_; lean_object* v_res_1232_; 
v_v_boxed_1231_ = lean_unbox(v_v_1230_);
v_res_1232_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1228_, v_k_1229_, v_v_boxed_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1233_, lean_object* v_opt_1234_){
_start:
{
lean_object* v_name_1235_; lean_object* v_defValue_1236_; lean_object* v_map_1237_; lean_object* v___x_1238_; 
v_name_1235_ = lean_ctor_get(v_opt_1234_, 0);
v_defValue_1236_ = lean_ctor_get(v_opt_1234_, 1);
v_map_1237_ = lean_ctor_get(v_opts_1233_, 0);
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1237_, v_name_1235_);
if (lean_obj_tag(v___x_1238_) == 0)
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_unbox(v_defValue_1236_);
return v___x_1239_;
}
else
{
lean_object* v_val_1240_; 
v_val_1240_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v___x_1238_, 1);
if (lean_obj_tag(v_val_1240_) == 1)
{
uint8_t v_v_1241_; 
v_v_1241_ = lean_ctor_get_uint8(v_val_1240_, 0);
lean_dec_ref_known(v_val_1240_, 0);
return v_v_1241_;
}
else
{
uint8_t v___x_1242_; 
lean_dec(v_val_1240_);
v___x_1242_ = lean_unbox(v_defValue_1236_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1243_, lean_object* v_opt_1244_){
_start:
{
uint8_t v_res_1245_; lean_object* v_r_1246_; 
v_res_1245_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1243_, v_opt_1244_);
lean_dec_ref(v_opt_1244_);
lean_dec_ref(v_opts_1243_);
v_r_1246_ = lean_box(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1247_, lean_object* v_opt_1248_){
_start:
{
lean_object* v_name_1249_; lean_object* v_defValue_1250_; lean_object* v_map_1251_; lean_object* v___x_1252_; 
v_name_1249_ = lean_ctor_get(v_opt_1248_, 0);
v_defValue_1250_ = lean_ctor_get(v_opt_1248_, 1);
v_map_1251_ = lean_ctor_get(v_opts_1247_, 0);
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1251_, v_name_1249_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_inc(v_defValue_1250_);
return v_defValue_1250_;
}
else
{
lean_object* v_val_1253_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
if (lean_obj_tag(v_val_1253_) == 3)
{
lean_object* v_v_1254_; 
v_v_1254_ = lean_ctor_get(v_val_1253_, 0);
lean_inc(v_v_1254_);
lean_dec_ref_known(v_val_1253_, 1);
return v_v_1254_;
}
else
{
lean_dec(v_val_1253_);
lean_inc(v_defValue_1250_);
return v_defValue_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1255_, lean_object* v_opt_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1255_, v_opt_1256_);
lean_dec_ref(v_opt_1256_);
lean_dec_ref(v_opts_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1258_, lean_object* v_lhs_1259_, lean_object* v_rhs_1260_, lean_object* v___x_1261_, lean_object* v___x_1262_, uint8_t v___x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___y_1297_; 
if (v___x_1258_ == 0)
{
lean_object* v___x_1334_; lean_object* v_a_1335_; lean_object* v___x_1336_; lean_object* v_a_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
lean_inc(v_lhs_1259_);
v___x_1334_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1259_, v___y_1265_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1334_);
lean_inc(v_rhs_1260_);
v___x_1336_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1260_, v___y_1265_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = l_Lean_Level_normalize(v_a_1335_);
lean_dec(v_a_1335_);
v___x_1339_ = l_Lean_Level_normalize(v_a_1337_);
lean_dec(v_a_1337_);
v___x_1340_ = lean_level_eq(v_lhs_1259_, v___x_1338_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
v___x_1341_ = lean_is_level_def_eq(v___x_1338_, v___x_1339_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1341_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_level_eq(v_rhs_1260_, v___x_1339_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
v___x_1343_ = lean_is_level_def_eq(v___x_1338_, v___x_1339_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; 
lean_dec(v___x_1339_);
lean_dec(v___x_1338_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v_rhs_1260_);
lean_inc(v_lhs_1259_);
v___x_1344_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1259_, v_rhs_1260_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1386_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1386_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1386_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v___x_1349_; uint8_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = 2;
v___x_1350_ = lean_unbox(v_a_1345_);
v___x_1351_ = l_Lean_instBEqLBool_beq(v___x_1350_, v___x_1349_);
if (v___x_1351_ == 0)
{
uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v___x_1352_ = 1;
v___x_1353_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
v___x_1354_ = l_Lean_instBEqLBool_beq(v___x_1353_, v___x_1352_);
v___x_1355_ = lean_box(v___x_1354_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1355_);
v___x_1357_ = v___x_1347_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_object* v___x_1359_; 
lean_del_object(v___x_1347_);
lean_dec(v_a_1345_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v_lhs_1259_);
lean_inc(v_rhs_1260_);
v___x_1359_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1260_, v_lhs_1259_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1377_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1377_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1377_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
uint8_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_unbox(v_a_1360_);
v___x_1365_ = l_Lean_instBEqLBool_beq(v___x_1364_, v___x_1349_);
if (v___x_1365_ == 0)
{
uint8_t v___x_1366_; uint8_t v___x_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v___x_1366_ = 1;
v___x_1367_ = lean_unbox(v_a_1360_);
lean_dec(v_a_1360_);
v___x_1368_ = l_Lean_instBEqLBool_beq(v___x_1367_, v___x_1366_);
v___x_1369_ = lean_box(v___x_1368_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1369_);
v___x_1371_ = v___x_1362_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v___x_1373_; 
lean_del_object(v___x_1362_);
lean_dec(v_a_1360_);
lean_inc(v_lhs_1259_);
v___x_1373_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1259_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; uint8_t v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
v___x_1375_ = lean_unbox(v_a_1374_);
lean_dec(v_a_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref_known(v___x_1373_, 1);
lean_inc(v_rhs_1260_);
v___x_1376_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1260_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
v___y_1297_ = v___x_1376_;
goto v___jp_1296_;
}
else
{
v___y_1297_ = v___x_1373_;
goto v___jp_1296_;
}
}
else
{
v___y_1297_ = v___x_1373_;
goto v___jp_1296_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v_a_1378_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1359_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1359_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v_a_1387_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1344_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1344_);
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
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
v___x_1395_ = l_Lean_Level_getOffset(v_lhs_1259_);
lean_dec(v_lhs_1259_);
v___x_1396_ = l_Lean_Level_getOffset(v_rhs_1260_);
lean_dec(v_rhs_1260_);
v___x_1397_ = lean_nat_dec_eq(v___x_1395_, v___x_1396_);
lean_dec(v___x_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
v___jp_1269_:
{
lean_object* v_options_1270_; uint8_t v_hasTrace_1271_; 
v_options_1270_ = lean_ctor_get(v___y_1266_, 1);
v_hasTrace_1271_ = lean_ctor_get_uint8(v_options_1270_, sizeof(void*)*1);
if (v_hasTrace_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v___x_1272_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1272_;
}
else
{
lean_object* v_toCold_1273_; lean_object* v_inheritedTraceOptions_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_toCold_1273_ = lean_ctor_get(v___y_1266_, 0);
v_inheritedTraceOptions_1274_ = lean_ctor_get(v_toCold_1273_, 4);
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1276_ = l_Lean_Name_mkStr3(v___x_1261_, v___x_1262_, v___x_1275_);
v___x_1277_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1276_);
v___x_1278_ = l_Lean_Name_append(v___x_1277_, v___x_1276_);
v___x_1279_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1274_, v_options_1270_, v___x_1278_);
lean_dec(v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v___x_1276_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v___x_1280_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1281_ = l_Lean_MessageData_ofLevel(v_lhs_1259_);
v___x_1282_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_MessageData_ofLevel(v_rhs_1260_);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1276_, v___x_1285_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; 
lean_dec_ref_known(v___x_1286_, 1);
v___x_1287_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1286_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1286_);
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
v___jp_1296_:
{
if (lean_obj_tag(v___y_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1333_; 
v_a_1298_ = lean_ctor_get(v___y_1297_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___y_1297_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1300_ = v___y_1297_;
v_isShared_1301_ = v_isSharedCheck_1333_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___y_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1333_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_unbox(v_a_1298_);
lean_dec(v_a_1298_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v_isDefEqStuckEx_1304_; 
v___x_1303_ = l_Lean_Meta_Context_config(v___y_1264_);
v_isDefEqStuckEx_1304_ = lean_ctor_get_uint8(v___x_1303_, 4);
lean_dec_ref(v___x_1303_);
if (v_isDefEqStuckEx_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v___x_1305_ = lean_box(v___x_1258_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1305_);
v___x_1307_ = v___x_1300_;
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
else
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_Level_isMVar(v_lhs_1259_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Level_isMVar(v_rhs_1260_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
v___x_1311_ = lean_box(v___x_1310_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1311_);
v___x_1313_ = v___x_1300_;
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
lean_del_object(v___x_1300_);
goto v___jp_1269_;
}
}
else
{
lean_del_object(v___x_1300_);
goto v___jp_1269_;
}
}
}
else
{
lean_object* v___x_1315_; 
lean_del_object(v___x_1300_);
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
v___x_1315_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1259_, v_rhs_1260_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1315_, 0);
lean_dec(v_unused_1324_);
v___x_1317_ = v___x_1315_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v___x_1315_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_box(v___x_1263_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1315_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1315_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1262_);
lean_dec_ref(v___x_1261_);
lean_dec(v_rhs_1260_);
lean_dec(v_lhs_1259_);
return v___y_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1400_, lean_object* v_lhs_1401_, lean_object* v_rhs_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v___x_13182__boxed_1411_; uint8_t v___x_13185__boxed_1412_; lean_object* v_res_1413_; 
v___x_13182__boxed_1411_ = lean_unbox(v___x_1400_);
v___x_13185__boxed_1412_ = lean_unbox(v___x_1405_);
v_res_1413_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13182__boxed_1411_, v_lhs_1401_, v_rhs_1402_, v___x_1403_, v___x_1404_, v___x_13185__boxed_1412_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1414_){
_start:
{
if (lean_obj_tag(v_e_1414_) == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = 2;
return v___x_1415_;
}
else
{
lean_object* v_a_1416_; uint8_t v___x_1417_; 
v_a_1416_ = lean_ctor_get(v_e_1414_, 0);
v___x_1417_ = lean_unbox(v_a_1416_);
if (v___x_1417_ == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = 1;
return v___x_1418_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1420_);
lean_dec_ref(v_e_1420_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1423_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v_x_1423_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_x_1423_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v_x_1423_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v_x_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 1);
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v_x_1423_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1423_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v_x_1423_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v_x_1423_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 0);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1444_, size_t v_i_1445_, lean_object* v_bs_1446_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_lt(v_i_1445_, v_sz_1444_);
if (v___x_1447_ == 0)
{
return v_bs_1446_;
}
else
{
lean_object* v_v_1448_; lean_object* v_msg_1449_; lean_object* v___x_1450_; lean_object* v_bs_x27_1451_; size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v_v_1448_ = lean_array_uget_borrowed(v_bs_1446_, v_i_1445_);
v_msg_1449_ = lean_ctor_get(v_v_1448_, 1);
lean_inc_ref(v_msg_1449_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v_bs_x27_1451_ = lean_array_uset(v_bs_1446_, v_i_1445_, v___x_1450_);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1445_, v___x_1452_);
v___x_1454_ = lean_array_uset(v_bs_x27_1451_, v_i_1445_, v_msg_1449_);
v_i_1445_ = v___x_1453_;
v_bs_1446_ = v___x_1454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_bs_1458_){
_start:
{
size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1459_, v_i_boxed_1460_, v_bs_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1462_, lean_object* v_data_1463_, lean_object* v_ref_1464_, lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_toCold_1471_; lean_object* v_options_1472_; lean_object* v_currRecDepth_1473_; lean_object* v_maxRecDepth_1474_; lean_object* v_ref_1475_; lean_object* v_currNamespace_1476_; lean_object* v_openDecls_1477_; lean_object* v_initHeartbeats_1478_; lean_object* v_maxHeartbeats_1479_; lean_object* v_currMacroScope_1480_; uint8_t v_diag_1481_; uint8_t v_suppressElabErrors_1482_; lean_object* v___x_1483_; lean_object* v_traceState_1484_; lean_object* v_traces_1485_; lean_object* v_ref_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v_msg_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1531_; 
v_toCold_1471_ = lean_ctor_get(v___y_1468_, 0);
v_options_1472_ = lean_ctor_get(v___y_1468_, 1);
v_currRecDepth_1473_ = lean_ctor_get(v___y_1468_, 2);
v_maxRecDepth_1474_ = lean_ctor_get(v___y_1468_, 3);
v_ref_1475_ = lean_ctor_get(v___y_1468_, 4);
v_currNamespace_1476_ = lean_ctor_get(v___y_1468_, 5);
v_openDecls_1477_ = lean_ctor_get(v___y_1468_, 6);
v_initHeartbeats_1478_ = lean_ctor_get(v___y_1468_, 7);
v_maxHeartbeats_1479_ = lean_ctor_get(v___y_1468_, 8);
v_currMacroScope_1480_ = lean_ctor_get(v___y_1468_, 9);
v_diag_1481_ = lean_ctor_get_uint8(v___y_1468_, sizeof(void*)*10);
v_suppressElabErrors_1482_ = lean_ctor_get_uint8(v___y_1468_, sizeof(void*)*10 + 1);
v___x_1483_ = lean_st_ref_get(v___y_1469_);
v_traceState_1484_ = lean_ctor_get(v___x_1483_, 4);
lean_inc_ref(v_traceState_1484_);
lean_dec(v___x_1483_);
v_traces_1485_ = lean_ctor_get(v_traceState_1484_, 0);
lean_inc_ref(v_traces_1485_);
lean_dec_ref(v_traceState_1484_);
v_ref_1486_ = l_Lean_replaceRef(v_ref_1464_, v_ref_1475_);
lean_inc(v_currMacroScope_1480_);
lean_inc(v_maxHeartbeats_1479_);
lean_inc(v_initHeartbeats_1478_);
lean_inc(v_openDecls_1477_);
lean_inc(v_currNamespace_1476_);
lean_inc(v_maxRecDepth_1474_);
lean_inc(v_currRecDepth_1473_);
lean_inc_ref(v_options_1472_);
lean_inc_ref(v_toCold_1471_);
v___x_1487_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1487_, 0, v_toCold_1471_);
lean_ctor_set(v___x_1487_, 1, v_options_1472_);
lean_ctor_set(v___x_1487_, 2, v_currRecDepth_1473_);
lean_ctor_set(v___x_1487_, 3, v_maxRecDepth_1474_);
lean_ctor_set(v___x_1487_, 4, v_ref_1486_);
lean_ctor_set(v___x_1487_, 5, v_currNamespace_1476_);
lean_ctor_set(v___x_1487_, 6, v_openDecls_1477_);
lean_ctor_set(v___x_1487_, 7, v_initHeartbeats_1478_);
lean_ctor_set(v___x_1487_, 8, v_maxHeartbeats_1479_);
lean_ctor_set(v___x_1487_, 9, v_currMacroScope_1480_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*10, v_diag_1481_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*10 + 1, v_suppressElabErrors_1482_);
v___x_1488_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1485_);
lean_dec_ref(v_traces_1485_);
v_sz_1489_ = lean_array_size(v___x_1488_);
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1489_, v___x_1490_, v___x_1488_);
v_msg_1492_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1492_, 0, v_data_1463_);
lean_ctor_set(v_msg_1492_, 1, v_msg_1465_);
lean_ctor_set(v_msg_1492_, 2, v___x_1491_);
v___x_1493_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1492_, v___y_1466_, v___y_1467_, v___x_1487_, v___y_1469_);
lean_dec_ref_known(v___x_1487_, 10);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1531_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1531_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v_traceState_1499_; lean_object* v_env_1500_; lean_object* v_nextMacroScope_1501_; lean_object* v_ngen_1502_; lean_object* v_auxDeclNGen_1503_; lean_object* v_cache_1504_; lean_object* v_messages_1505_; lean_object* v_infoState_1506_; lean_object* v_snapshotTasks_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1530_; 
v___x_1498_ = lean_st_ref_take(v___y_1469_);
v_traceState_1499_ = lean_ctor_get(v___x_1498_, 4);
v_env_1500_ = lean_ctor_get(v___x_1498_, 0);
v_nextMacroScope_1501_ = lean_ctor_get(v___x_1498_, 1);
v_ngen_1502_ = lean_ctor_get(v___x_1498_, 2);
v_auxDeclNGen_1503_ = lean_ctor_get(v___x_1498_, 3);
v_cache_1504_ = lean_ctor_get(v___x_1498_, 5);
v_messages_1505_ = lean_ctor_get(v___x_1498_, 6);
v_infoState_1506_ = lean_ctor_get(v___x_1498_, 7);
v_snapshotTasks_1507_ = lean_ctor_get(v___x_1498_, 8);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1509_ = v___x_1498_;
v_isShared_1510_ = v_isSharedCheck_1530_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snapshotTasks_1507_);
lean_inc(v_infoState_1506_);
lean_inc(v_messages_1505_);
lean_inc(v_cache_1504_);
lean_inc(v_traceState_1499_);
lean_inc(v_auxDeclNGen_1503_);
lean_inc(v_ngen_1502_);
lean_inc(v_nextMacroScope_1501_);
lean_inc(v_env_1500_);
lean_dec(v___x_1498_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1530_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
uint64_t v_tid_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1528_; 
v_tid_1511_ = lean_ctor_get_uint64(v_traceState_1499_, sizeof(void*)*1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_traceState_1499_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_traceState_1499_, 0);
lean_dec(v_unused_1529_);
v___x_1513_ = v_traceState_1499_;
v_isShared_1514_ = v_isSharedCheck_1528_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v_traceState_1499_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1528_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_ref_1464_);
lean_ctor_set(v___x_1515_, 1, v_a_1494_);
v___x_1516_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1462_, v___x_1515_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1516_);
lean_ctor_set_uint64(v_reuseFailAlloc_1527_, sizeof(void*)*1, v_tid_1511_);
v___x_1518_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v___x_1518_);
v___x_1520_ = v___x_1509_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_env_1500_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_nextMacroScope_1501_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_ngen_1502_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_auxDeclNGen_1503_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1526_, 5, v_cache_1504_);
lean_ctor_set(v_reuseFailAlloc_1526_, 6, v_messages_1505_);
lean_ctor_set(v_reuseFailAlloc_1526_, 7, v_infoState_1506_);
lean_ctor_set(v_reuseFailAlloc_1526_, 8, v_snapshotTasks_1507_);
v___x_1520_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1521_ = lean_st_ref_put(v___y_1469_, v___x_1520_);
v___x_1522_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1522_);
v___x_1524_ = v___x_1496_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1532_, lean_object* v_data_1533_, lean_object* v_ref_1534_, lean_object* v_msg_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1532_, v_data_1533_, v_ref_1534_, v_msg_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1541_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1542_; double v___x_1543_; 
v___x_1542_ = lean_unsigned_to_nat(1000u);
v___x_1543_ = lean_float_of_nat(v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1544_, uint8_t v_collapsed_1545_, lean_object* v_tag_1546_, lean_object* v_opts_1547_, uint8_t v_clsEnabled_1548_, lean_object* v_oldTraces_1549_, lean_object* v_ref_1550_, lean_object* v_msg_1551_, lean_object* v_resStartStop_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_fst_1558_; lean_object* v_snd_1559_; lean_object* v_data_1561_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; uint8_t v___y_1586_; double v___y_1617_; 
v_fst_1558_ = lean_ctor_get(v_resStartStop_1552_, 0);
lean_inc(v_fst_1558_);
v_snd_1559_ = lean_ctor_get(v_resStartStop_1552_, 1);
lean_inc(v_snd_1559_);
lean_dec_ref(v_resStartStop_1552_);
v_fst_1572_ = lean_ctor_get(v_snd_1559_, 0);
lean_inc(v_fst_1572_);
v_snd_1573_ = lean_ctor_get(v_snd_1559_, 1);
lean_inc(v_snd_1573_);
lean_dec(v_snd_1559_);
v___x_1574_ = l_Lean_trace_profiler;
v___x_1575_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1547_, v___x_1574_);
if (v___x_1575_ == 0)
{
v___y_1586_ = v___x_1575_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1623_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1547_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; double v___x_1626_; double v___x_1627_; double v___x_1628_; 
v___x_1624_ = l_Lean_trace_profiler_threshold;
v___x_1625_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1547_, v___x_1624_);
v___x_1626_ = lean_float_of_nat(v___x_1625_);
v___x_1627_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1628_ = lean_float_div(v___x_1626_, v___x_1627_);
v___y_1617_ = v___x_1628_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; double v___x_1631_; 
v___x_1629_ = l_Lean_trace_profiler_threshold;
v___x_1630_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1547_, v___x_1629_);
v___x_1631_ = lean_float_of_nat(v___x_1630_);
v___y_1617_ = v___x_1631_;
goto v___jp_1616_;
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1549_, v_data_1561_, v_ref_1550_, v_msg_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1562_, 1);
v___x_1563_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1558_);
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_fst_1558_);
v_a_1564_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1562_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
v___jp_1576_:
{
uint8_t v_result_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; double v___x_1580_; lean_object* v_data_1581_; 
v_result_1577_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1558_);
v___x_1578_ = lean_box(v_result_1577_);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
v___x_1580_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1546_);
lean_inc_ref(v___x_1579_);
lean_inc(v_cls_1544_);
v_data_1581_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1581_, 0, v_cls_1544_);
lean_ctor_set(v_data_1581_, 1, v___x_1579_);
lean_ctor_set(v_data_1581_, 2, v_tag_1546_);
lean_ctor_set_float(v_data_1581_, sizeof(void*)*3, v___x_1580_);
lean_ctor_set_float(v_data_1581_, sizeof(void*)*3 + 8, v___x_1580_);
lean_ctor_set_uint8(v_data_1581_, sizeof(void*)*3 + 16, v_collapsed_1545_);
if (v___x_1575_ == 0)
{
lean_dec_ref_known(v___x_1579_, 1);
lean_dec(v_snd_1573_);
lean_dec(v_fst_1572_);
lean_dec_ref(v_tag_1546_);
lean_dec(v_cls_1544_);
v_data_1561_ = v_data_1581_;
goto v___jp_1560_;
}
else
{
lean_object* v_data_1582_; double v___x_1583_; double v___x_1584_; 
lean_dec_ref_known(v_data_1581_, 3);
v_data_1582_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1582_, 0, v_cls_1544_);
lean_ctor_set(v_data_1582_, 1, v___x_1579_);
lean_ctor_set(v_data_1582_, 2, v_tag_1546_);
v___x_1583_ = lean_unbox_float(v_fst_1572_);
lean_dec(v_fst_1572_);
lean_ctor_set_float(v_data_1582_, sizeof(void*)*3, v___x_1583_);
v___x_1584_ = lean_unbox_float(v_snd_1573_);
lean_dec(v_snd_1573_);
lean_ctor_set_float(v_data_1582_, sizeof(void*)*3 + 8, v___x_1584_);
lean_ctor_set_uint8(v_data_1582_, sizeof(void*)*3 + 16, v_collapsed_1545_);
v_data_1561_ = v_data_1582_;
goto v___jp_1560_;
}
}
v___jp_1585_:
{
if (v_clsEnabled_1548_ == 0)
{
if (v___y_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v_traceState_1588_; lean_object* v_env_1589_; lean_object* v_nextMacroScope_1590_; lean_object* v_ngen_1591_; lean_object* v_auxDeclNGen_1592_; lean_object* v_cache_1593_; lean_object* v_messages_1594_; lean_object* v_infoState_1595_; lean_object* v_snapshotTasks_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_snd_1573_);
lean_dec(v_fst_1572_);
lean_dec_ref(v_msg_1551_);
lean_dec(v_ref_1550_);
lean_dec_ref(v_tag_1546_);
lean_dec(v_cls_1544_);
v___x_1587_ = lean_st_ref_take(v___y_1556_);
v_traceState_1588_ = lean_ctor_get(v___x_1587_, 4);
v_env_1589_ = lean_ctor_get(v___x_1587_, 0);
v_nextMacroScope_1590_ = lean_ctor_get(v___x_1587_, 1);
v_ngen_1591_ = lean_ctor_get(v___x_1587_, 2);
v_auxDeclNGen_1592_ = lean_ctor_get(v___x_1587_, 3);
v_cache_1593_ = lean_ctor_get(v___x_1587_, 5);
v_messages_1594_ = lean_ctor_get(v___x_1587_, 6);
v_infoState_1595_ = lean_ctor_get(v___x_1587_, 7);
v_snapshotTasks_1596_ = lean_ctor_get(v___x_1587_, 8);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1598_ = v___x_1587_;
v_isShared_1599_ = v_isSharedCheck_1615_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_snapshotTasks_1596_);
lean_inc(v_infoState_1595_);
lean_inc(v_messages_1594_);
lean_inc(v_cache_1593_);
lean_inc(v_traceState_1588_);
lean_inc(v_auxDeclNGen_1592_);
lean_inc(v_ngen_1591_);
lean_inc(v_nextMacroScope_1590_);
lean_inc(v_env_1589_);
lean_dec(v___x_1587_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1615_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
uint64_t v_tid_1600_; lean_object* v_traces_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1614_; 
v_tid_1600_ = lean_ctor_get_uint64(v_traceState_1588_, sizeof(void*)*1);
v_traces_1601_ = lean_ctor_get(v_traceState_1588_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_traceState_1588_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1603_ = v_traceState_1588_;
v_isShared_1604_ = v_isSharedCheck_1614_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_traces_1601_);
lean_dec(v_traceState_1588_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1614_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1549_, v_traces_1601_);
lean_dec_ref(v_traces_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1605_);
lean_ctor_set_uint64(v_reuseFailAlloc_1613_, sizeof(void*)*1, v_tid_1600_);
v___x_1607_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 4, v___x_1607_);
v___x_1609_ = v___x_1598_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_env_1589_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_nextMacroScope_1590_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_ngen_1591_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_auxDeclNGen_1592_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1612_, 5, v_cache_1593_);
lean_ctor_set(v_reuseFailAlloc_1612_, 6, v_messages_1594_);
lean_ctor_set(v_reuseFailAlloc_1612_, 7, v_infoState_1595_);
lean_ctor_set(v_reuseFailAlloc_1612_, 8, v_snapshotTasks_1596_);
v___x_1609_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_st_ref_put(v___y_1556_, v___x_1609_);
v___x_1611_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1558_);
return v___x_1611_;
}
}
}
}
}
else
{
goto v___jp_1576_;
}
}
else
{
goto v___jp_1576_;
}
}
v___jp_1616_:
{
double v___x_1618_; double v___x_1619_; double v___x_1620_; uint8_t v___x_1621_; 
v___x_1618_ = lean_unbox_float(v_snd_1573_);
v___x_1619_ = lean_unbox_float(v_fst_1572_);
v___x_1620_ = lean_float_sub(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_float_decLt(v___y_1617_, v___x_1620_);
v___y_1586_ = v___x_1621_;
goto v___jp_1585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1632_, lean_object* v_collapsed_1633_, lean_object* v_tag_1634_, lean_object* v_opts_1635_, lean_object* v_clsEnabled_1636_, lean_object* v_oldTraces_1637_, lean_object* v_ref_1638_, lean_object* v_msg_1639_, lean_object* v_resStartStop_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_collapsed_boxed_1646_; uint8_t v_clsEnabled_boxed_1647_; lean_object* v_res_1648_; 
v_collapsed_boxed_1646_ = lean_unbox(v_collapsed_1633_);
v_clsEnabled_boxed_1647_ = lean_unbox(v_clsEnabled_1636_);
v_res_1648_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1632_, v_collapsed_boxed_1646_, v_tag_1634_, v_opts_1635_, v_clsEnabled_boxed_1647_, v_oldTraces_1637_, v_ref_1638_, v_msg_1639_, v_resStartStop_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_opts_1635_);
return v_res_1648_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1649_; double v___x_1650_; 
v___x_1649_ = lean_unsigned_to_nat(1000000000u);
v___x_1650_ = lean_float_of_nat(v___x_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1665_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1666_ = l_Lean_Name_append(v___x_1665_, v___x_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___y_1675_; lean_object* v___y_1676_; uint8_t v___y_1677_; uint8_t v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_a_1688_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; uint8_t v___y_1701_; uint8_t v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v_a_1711_; lean_object* v___y_1724_; lean_object* v___y_1725_; uint8_t v___y_1726_; uint8_t v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v_toCold_1740_; lean_object* v_currRecDepth_1741_; lean_object* v_ref_1742_; lean_object* v_currNamespace_1743_; lean_object* v_openDecls_1744_; lean_object* v_initHeartbeats_1745_; lean_object* v_maxHeartbeats_1746_; lean_object* v_currMacroScope_1747_; uint8_t v_suppressElabErrors_1748_; lean_object* v___y_1749_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; uint8_t v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; uint8_t v___y_1827_; uint8_t v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; uint8_t v___y_1840_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; uint8_t v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; uint8_t v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v_lhs_1903_; lean_object* v_rhs_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; 
if (lean_obj_tag(v_x_1667_) == 1)
{
if (lean_obj_tag(v_x_1668_) == 1)
{
lean_object* v_a_1940_; lean_object* v_a_1941_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v_x_1667_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v_x_1667_, 1);
v_a_1941_ = lean_ctor_get(v_x_1668_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v_x_1668_, 1);
v___x_1942_ = lean_is_level_def_eq(v_a_1940_, v_a_1941_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1942_;
}
else
{
v_lhs_1903_ = v_x_1667_;
v_rhs_1904_ = v_x_1668_;
v___y_1905_ = v_a_1669_;
v___y_1906_ = v_a_1670_;
v___y_1907_ = v_a_1671_;
v___y_1908_ = v_a_1672_;
goto v___jp_1902_;
}
}
else
{
v_lhs_1903_ = v_x_1667_;
v_rhs_1904_ = v_x_1668_;
v___y_1905_ = v_a_1669_;
v___y_1906_ = v_a_1670_;
v___y_1907_ = v_a_1671_;
v___y_1908_ = v_a_1672_;
goto v___jp_1902_;
}
v___jp_1674_:
{
lean_object* v___x_1689_; double v___x_1690_; double v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1689_ = lean_io_get_num_heartbeats();
v___x_1690_ = lean_float_of_nat(v___y_1680_);
v___x_1691_ = lean_float_of_nat(v___x_1689_);
v___x_1692_ = lean_box_float(v___x_1690_);
v___x_1693_ = lean_box_float(v___x_1691_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_a_1688_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1687_);
v___x_1696_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1687_, v___y_1678_, v___y_1675_, v___y_1684_, v___y_1677_, v___y_1682_, v___y_1685_, v___y_1679_, v___x_1695_, v___y_1683_, v___y_1676_, v___y_1686_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v___y_1684_);
return v___x_1696_;
}
v___jp_1697_:
{
lean_object* v___x_1712_; double v___x_1713_; double v___x_1714_; double v___x_1715_; double v___x_1716_; double v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1712_ = lean_io_mono_nanos_now();
v___x_1713_ = lean_float_of_nat(v___y_1700_);
v___x_1714_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1715_ = lean_float_div(v___x_1713_, v___x_1714_);
v___x_1716_ = lean_float_of_nat(v___x_1712_);
v___x_1717_ = lean_float_div(v___x_1716_, v___x_1714_);
v___x_1718_ = lean_box_float(v___x_1715_);
v___x_1719_ = lean_box_float(v___x_1717_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1711_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1710_);
v___x_1722_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1710_, v___y_1702_, v___y_1698_, v___y_1707_, v___y_1701_, v___y_1705_, v___y_1708_, v___y_1703_, v___x_1721_, v___y_1706_, v___y_1699_, v___y_1709_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v___y_1707_);
return v___x_1722_;
}
v___jp_1723_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1750_ = l_Lean_maxRecDepth;
v___x_1751_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1736_, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1752_, 0, v_toCold_1740_);
lean_ctor_set(v___x_1752_, 1, v___y_1736_);
lean_ctor_set(v___x_1752_, 2, v_currRecDepth_1741_);
lean_ctor_set(v___x_1752_, 3, v___x_1751_);
lean_ctor_set(v___x_1752_, 4, v_ref_1742_);
lean_ctor_set(v___x_1752_, 5, v_currNamespace_1743_);
lean_ctor_set(v___x_1752_, 6, v_openDecls_1744_);
lean_ctor_set(v___x_1752_, 7, v_initHeartbeats_1745_);
lean_ctor_set(v___x_1752_, 8, v_maxHeartbeats_1746_);
lean_ctor_set(v___x_1752_, 9, v_currMacroScope_1747_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*10, v___y_1728_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*10 + 1, v_suppressElabErrors_1748_);
v___x_1753_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1739_, v___y_1732_, v___y_1725_, v___x_1752_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref_known(v___x_1752_, 10);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1754_, v___y_1732_, v___y_1725_, v___y_1737_, v___y_1729_);
lean_dec_ref(v___y_1737_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1758_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1733_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_io_mono_nanos_now();
lean_inc(v___y_1729_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1732_);
v___x_1760_ = lean_apply_5(v___y_1731_, v___y_1732_, v___y_1725_, v___y_1735_, v___y_1729_, lean_box(0));
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 1);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v___y_1698_ = v___y_1724_;
v___y_1699_ = v___y_1725_;
v___y_1700_ = v___x_1759_;
v___y_1701_ = v___y_1726_;
v___y_1702_ = v___y_1727_;
v___y_1703_ = v_a_1756_;
v___y_1704_ = v___y_1729_;
v___y_1705_ = v___y_1730_;
v___y_1706_ = v___y_1732_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1738_;
v_a_1711_ = v___x_1766_;
goto v___jp_1697_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 0);
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
v___y_1698_ = v___y_1724_;
v___y_1699_ = v___y_1725_;
v___y_1700_ = v___x_1759_;
v___y_1701_ = v___y_1726_;
v___y_1702_ = v___y_1727_;
v___y_1703_ = v_a_1756_;
v___y_1704_ = v___y_1729_;
v___y_1705_ = v___y_1730_;
v___y_1706_ = v___y_1732_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1734_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1738_;
v_a_1711_ = v___x_1774_;
goto v___jp_1697_;
}
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1729_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1725_);
lean_inc_ref(v___y_1732_);
v___x_1778_ = lean_apply_5(v___y_1731_, v___y_1732_, v___y_1725_, v___y_1735_, v___y_1729_, lean_box(0));
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 1);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v___y_1675_ = v___y_1724_;
v___y_1676_ = v___y_1725_;
v___y_1677_ = v___y_1726_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v_a_1756_;
v___y_1680_ = v___x_1777_;
v___y_1681_ = v___y_1729_;
v___y_1682_ = v___y_1730_;
v___y_1683_ = v___y_1732_;
v___y_1684_ = v___y_1733_;
v___y_1685_ = v___y_1734_;
v___y_1686_ = v___y_1735_;
v___y_1687_ = v___y_1738_;
v_a_1688_ = v___x_1784_;
goto v___jp_1674_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1778_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 0);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v___y_1675_ = v___y_1724_;
v___y_1676_ = v___y_1725_;
v___y_1677_ = v___y_1726_;
v___y_1678_ = v___y_1727_;
v___y_1679_ = v_a_1756_;
v___y_1680_ = v___x_1777_;
v___y_1681_ = v___y_1729_;
v___y_1682_ = v___y_1730_;
v___y_1683_ = v___y_1732_;
v___y_1684_ = v___y_1733_;
v___y_1685_ = v___y_1734_;
v___y_1686_ = v___y_1735_;
v___y_1687_ = v___y_1738_;
v_a_1688_ = v___x_1792_;
goto v___jp_1674_;
}
}
}
}
}
v___jp_1795_:
{
lean_object* v_toCold_1814_; lean_object* v_currRecDepth_1815_; lean_object* v_ref_1816_; lean_object* v_currNamespace_1817_; lean_object* v_openDecls_1818_; lean_object* v_initHeartbeats_1819_; lean_object* v_maxHeartbeats_1820_; lean_object* v_currMacroScope_1821_; uint8_t v_suppressElabErrors_1822_; 
v_toCold_1814_ = lean_ctor_get(v___y_1812_, 0);
lean_inc_ref(v_toCold_1814_);
v_currRecDepth_1815_ = lean_ctor_get(v___y_1812_, 2);
lean_inc(v_currRecDepth_1815_);
v_ref_1816_ = lean_ctor_get(v___y_1812_, 4);
lean_inc(v_ref_1816_);
v_currNamespace_1817_ = lean_ctor_get(v___y_1812_, 5);
lean_inc(v_currNamespace_1817_);
v_openDecls_1818_ = lean_ctor_get(v___y_1812_, 6);
lean_inc(v_openDecls_1818_);
v_initHeartbeats_1819_ = lean_ctor_get(v___y_1812_, 7);
lean_inc(v_initHeartbeats_1819_);
v_maxHeartbeats_1820_ = lean_ctor_get(v___y_1812_, 8);
lean_inc(v_maxHeartbeats_1820_);
v_currMacroScope_1821_ = lean_ctor_get(v___y_1812_, 9);
lean_inc(v_currMacroScope_1821_);
v_suppressElabErrors_1822_ = lean_ctor_get_uint8(v___y_1812_, sizeof(void*)*10 + 1);
lean_dec_ref(v___y_1812_);
v___y_1724_ = v___y_1796_;
v___y_1725_ = v___y_1797_;
v___y_1726_ = v___y_1798_;
v___y_1727_ = v___y_1799_;
v___y_1728_ = v___y_1800_;
v___y_1729_ = v___y_1801_;
v___y_1730_ = v___y_1802_;
v___y_1731_ = v___y_1803_;
v___y_1732_ = v___y_1804_;
v___y_1733_ = v___y_1805_;
v___y_1734_ = v___y_1806_;
v___y_1735_ = v___y_1807_;
v___y_1736_ = v___y_1808_;
v___y_1737_ = v___y_1809_;
v___y_1738_ = v___y_1810_;
v___y_1739_ = v___y_1811_;
v_toCold_1740_ = v_toCold_1814_;
v_currRecDepth_1741_ = v_currRecDepth_1815_;
v_ref_1742_ = v_ref_1816_;
v_currNamespace_1743_ = v_currNamespace_1817_;
v_openDecls_1744_ = v_openDecls_1818_;
v_initHeartbeats_1745_ = v_initHeartbeats_1819_;
v_maxHeartbeats_1746_ = v_maxHeartbeats_1820_;
v_currMacroScope_1747_ = v_currMacroScope_1821_;
v_suppressElabErrors_1748_ = v_suppressElabErrors_1822_;
v___y_1749_ = v___y_1813_;
goto v___jp_1723_;
}
v___jp_1823_:
{
if (v___y_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v_env_1842_; lean_object* v_nextMacroScope_1843_; lean_object* v_ngen_1844_; lean_object* v_auxDeclNGen_1845_; lean_object* v_traceState_1846_; lean_object* v_messages_1847_; lean_object* v_infoState_1848_; lean_object* v_snapshotTasks_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1859_; 
v___x_1841_ = lean_st_ref_take(v___y_1829_);
v_env_1842_ = lean_ctor_get(v___x_1841_, 0);
v_nextMacroScope_1843_ = lean_ctor_get(v___x_1841_, 1);
v_ngen_1844_ = lean_ctor_get(v___x_1841_, 2);
v_auxDeclNGen_1845_ = lean_ctor_get(v___x_1841_, 3);
v_traceState_1846_ = lean_ctor_get(v___x_1841_, 4);
v_messages_1847_ = lean_ctor_get(v___x_1841_, 6);
v_infoState_1848_ = lean_ctor_get(v___x_1841_, 7);
v_snapshotTasks_1849_ = lean_ctor_get(v___x_1841_, 8);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1841_, 5);
lean_dec(v_unused_1860_);
v___x_1851_ = v___x_1841_;
v_isShared_1852_ = v_isSharedCheck_1859_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_snapshotTasks_1849_);
lean_inc(v_infoState_1848_);
lean_inc(v_messages_1847_);
lean_inc(v_traceState_1846_);
lean_inc(v_auxDeclNGen_1845_);
lean_inc(v_ngen_1844_);
lean_inc(v_nextMacroScope_1843_);
lean_inc(v_env_1842_);
lean_dec(v___x_1841_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1859_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = l_Lean_Kernel_enableDiag(v_env_1842_, v___y_1828_);
v___x_1854_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 5, v___x_1854_);
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_nextMacroScope_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_ngen_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_auxDeclNGen_1845_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_traceState_1846_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_messages_1847_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_infoState_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v_snapshotTasks_1849_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_st_ref_put(v___y_1829_, v___x_1856_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1829_);
v___y_1796_ = v___y_1824_;
v___y_1797_ = v___y_1825_;
v___y_1798_ = v___y_1826_;
v___y_1799_ = v___y_1827_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1830_;
v___y_1803_ = v___y_1831_;
v___y_1804_ = v___y_1832_;
v___y_1805_ = v___y_1833_;
v___y_1806_ = v___y_1834_;
v___y_1807_ = v___y_1835_;
v___y_1808_ = v___y_1836_;
v___y_1809_ = v___y_1837_;
v___y_1810_ = v___y_1838_;
v___y_1811_ = v___y_1839_;
v___y_1812_ = v___y_1837_;
v___y_1813_ = v___y_1829_;
goto v___jp_1795_;
}
}
}
else
{
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1829_);
v___y_1796_ = v___y_1824_;
v___y_1797_ = v___y_1825_;
v___y_1798_ = v___y_1826_;
v___y_1799_ = v___y_1827_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1830_;
v___y_1803_ = v___y_1831_;
v___y_1804_ = v___y_1832_;
v___y_1805_ = v___y_1833_;
v___y_1806_ = v___y_1834_;
v___y_1807_ = v___y_1835_;
v___y_1808_ = v___y_1836_;
v___y_1809_ = v___y_1837_;
v___y_1810_ = v___y_1838_;
v___y_1811_ = v___y_1839_;
v___y_1812_ = v___y_1837_;
v___y_1813_ = v___y_1829_;
goto v___jp_1795_;
}
}
v___jp_1861_:
{
lean_object* v___x_1885_; lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v_env_1888_; lean_object* v_ref_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1885_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1873_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = lean_st_ref_get(v___y_1873_);
v_env_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_env_1888_);
lean_dec(v___x_1887_);
v_ref_1889_ = l_Lean_replaceRef(v___y_1880_, v___y_1880_);
lean_inc(v___y_1874_);
lean_inc(v___y_1883_);
lean_inc(v___y_1870_);
lean_inc(v___y_1879_);
lean_inc(v___y_1869_);
lean_inc(v_ref_1889_);
lean_inc(v___y_1868_);
lean_inc_ref_n(v___y_1881_, 2);
lean_inc_ref(v___y_1875_);
v___x_1890_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1890_, 0, v___y_1875_);
lean_ctor_set(v___x_1890_, 1, v___y_1881_);
lean_ctor_set(v___x_1890_, 2, v___y_1868_);
lean_ctor_set(v___x_1890_, 3, v___y_1871_);
lean_ctor_set(v___x_1890_, 4, v_ref_1889_);
lean_ctor_set(v___x_1890_, 5, v___y_1869_);
lean_ctor_set(v___x_1890_, 6, v___y_1879_);
lean_ctor_set(v___x_1890_, 7, v___y_1870_);
lean_ctor_set(v___x_1890_, 8, v___y_1883_);
lean_ctor_set(v___x_1890_, 9, v___y_1874_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*10, v___y_1867_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*10 + 1, v___y_1876_);
v___x_1891_ = l_Lean_MessageData_ofLevel(v___y_1866_);
v___x_1892_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_MessageData_ofLevel(v___y_1872_);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1897_ = 0;
v___x_1898_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1881_, v___x_1896_, v___x_1897_);
v___x_1899_ = l_Lean_diagnostics;
v___x_1900_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___x_1898_, v___x_1899_);
v___x_1901_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1888_);
lean_dec_ref(v_env_1888_);
if (v___x_1900_ == 0)
{
if (v___x_1901_ == 0)
{
lean_inc(v___y_1873_);
v___y_1724_ = v___y_1862_;
v___y_1725_ = v___y_1863_;
v___y_1726_ = v___y_1864_;
v___y_1727_ = v___y_1865_;
v___y_1728_ = v___x_1900_;
v___y_1729_ = v___y_1873_;
v___y_1730_ = v_a_1886_;
v___y_1731_ = v___y_1877_;
v___y_1732_ = v___y_1878_;
v___y_1733_ = v___y_1881_;
v___y_1734_ = v___y_1880_;
v___y_1735_ = v___y_1882_;
v___y_1736_ = v___x_1898_;
v___y_1737_ = v___x_1890_;
v___y_1738_ = v___y_1884_;
v___y_1739_ = v___x_1895_;
v_toCold_1740_ = v___y_1875_;
v_currRecDepth_1741_ = v___y_1868_;
v_ref_1742_ = v_ref_1889_;
v_currNamespace_1743_ = v___y_1869_;
v_openDecls_1744_ = v___y_1879_;
v_initHeartbeats_1745_ = v___y_1870_;
v_maxHeartbeats_1746_ = v___y_1883_;
v_currMacroScope_1747_ = v___y_1874_;
v_suppressElabErrors_1748_ = v___y_1876_;
v___y_1749_ = v___y_1873_;
goto v___jp_1723_;
}
else
{
lean_dec(v_ref_1889_);
lean_dec(v___y_1883_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
v___y_1824_ = v___y_1862_;
v___y_1825_ = v___y_1863_;
v___y_1826_ = v___y_1864_;
v___y_1827_ = v___y_1865_;
v___y_1828_ = v___x_1900_;
v___y_1829_ = v___y_1873_;
v___y_1830_ = v_a_1886_;
v___y_1831_ = v___y_1877_;
v___y_1832_ = v___y_1878_;
v___y_1833_ = v___y_1881_;
v___y_1834_ = v___y_1880_;
v___y_1835_ = v___y_1882_;
v___y_1836_ = v___x_1898_;
v___y_1837_ = v___x_1890_;
v___y_1838_ = v___y_1884_;
v___y_1839_ = v___x_1895_;
v___y_1840_ = v___x_1900_;
goto v___jp_1823_;
}
}
else
{
lean_dec(v_ref_1889_);
lean_dec(v___y_1883_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
v___y_1824_ = v___y_1862_;
v___y_1825_ = v___y_1863_;
v___y_1826_ = v___y_1864_;
v___y_1827_ = v___y_1865_;
v___y_1828_ = v___x_1900_;
v___y_1829_ = v___y_1873_;
v___y_1830_ = v_a_1886_;
v___y_1831_ = v___y_1877_;
v___y_1832_ = v___y_1878_;
v___y_1833_ = v___y_1881_;
v___y_1834_ = v___y_1880_;
v___y_1835_ = v___y_1882_;
v___y_1836_ = v___x_1898_;
v___y_1837_ = v___x_1890_;
v___y_1838_ = v___y_1884_;
v___y_1839_ = v___x_1895_;
v___y_1840_ = v___x_1901_;
goto v___jp_1823_;
}
}
v___jp_1902_:
{
lean_object* v_options_1909_; lean_object* v_toCold_1910_; lean_object* v_currRecDepth_1911_; lean_object* v_maxRecDepth_1912_; lean_object* v_ref_1913_; lean_object* v_currNamespace_1914_; lean_object* v_openDecls_1915_; lean_object* v_initHeartbeats_1916_; lean_object* v_maxHeartbeats_1917_; lean_object* v_currMacroScope_1918_; uint8_t v_diag_1919_; uint8_t v_suppressElabErrors_1920_; uint8_t v_hasTrace_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___y_1930_; 
v_options_1909_ = lean_ctor_get(v___y_1907_, 1);
v_toCold_1910_ = lean_ctor_get(v___y_1907_, 0);
v_currRecDepth_1911_ = lean_ctor_get(v___y_1907_, 2);
v_maxRecDepth_1912_ = lean_ctor_get(v___y_1907_, 3);
v_ref_1913_ = lean_ctor_get(v___y_1907_, 4);
v_currNamespace_1914_ = lean_ctor_get(v___y_1907_, 5);
v_openDecls_1915_ = lean_ctor_get(v___y_1907_, 6);
v_initHeartbeats_1916_ = lean_ctor_get(v___y_1907_, 7);
v_maxHeartbeats_1917_ = lean_ctor_get(v___y_1907_, 8);
v_currMacroScope_1918_ = lean_ctor_get(v___y_1907_, 9);
v_diag_1919_ = lean_ctor_get_uint8(v___y_1907_, sizeof(void*)*10);
v_suppressElabErrors_1920_ = lean_ctor_get_uint8(v___y_1907_, sizeof(void*)*10 + 1);
v_hasTrace_1921_ = lean_ctor_get_uint8(v_options_1909_, sizeof(void*)*1);
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1924_ = l_Lean_Level_getLevelOffset(v_lhs_1903_);
v___x_1925_ = l_Lean_Level_getLevelOffset(v_rhs_1904_);
v___x_1926_ = lean_level_eq(v___x_1924_, v___x_1925_);
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = 1;
v___x_1928_ = lean_box(v___x_1926_);
v___x_1929_ = lean_box(v___x_1927_);
lean_inc(v_rhs_1904_);
lean_inc(v_lhs_1903_);
v___y_1930_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1930_, 0, v___x_1928_);
lean_closure_set(v___y_1930_, 1, v_lhs_1903_);
lean_closure_set(v___y_1930_, 2, v_rhs_1904_);
lean_closure_set(v___y_1930_, 3, v___x_1922_);
lean_closure_set(v___y_1930_, 4, v___x_1923_);
lean_closure_set(v___y_1930_, 5, v___x_1929_);
if (v_hasTrace_1921_ == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v___y_1930_);
v___x_1931_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1926_, v_lhs_1903_, v_rhs_1904_, v___x_1922_, v___x_1923_, v___x_1927_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v___x_1931_;
}
else
{
lean_object* v_inheritedTraceOptions_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v_inheritedTraceOptions_1932_ = lean_ctor_get(v_toCold_1910_, 4);
v___x_1933_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1934_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1935_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1932_, v_options_1909_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = l_Lean_trace_profiler;
v___x_1938_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_options_1909_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v___y_1930_);
v___x_1939_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1926_, v_lhs_1903_, v_rhs_1904_, v___x_1922_, v___x_1923_, v___x_1927_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v___x_1939_;
}
else
{
lean_inc(v_currMacroScope_1918_);
lean_inc(v_maxHeartbeats_1917_);
lean_inc(v_initHeartbeats_1916_);
lean_inc(v_openDecls_1915_);
lean_inc(v_currNamespace_1914_);
lean_inc(v_ref_1913_);
lean_inc(v_maxRecDepth_1912_);
lean_inc(v_currRecDepth_1911_);
lean_inc_ref(v_toCold_1910_);
lean_inc_ref(v_options_1909_);
v___y_1862_ = v___x_1934_;
v___y_1863_ = v___y_1906_;
v___y_1864_ = v___x_1936_;
v___y_1865_ = v___x_1927_;
v___y_1866_ = v_lhs_1903_;
v___y_1867_ = v_diag_1919_;
v___y_1868_ = v_currRecDepth_1911_;
v___y_1869_ = v_currNamespace_1914_;
v___y_1870_ = v_initHeartbeats_1916_;
v___y_1871_ = v_maxRecDepth_1912_;
v___y_1872_ = v_rhs_1904_;
v___y_1873_ = v___y_1908_;
v___y_1874_ = v_currMacroScope_1918_;
v___y_1875_ = v_toCold_1910_;
v___y_1876_ = v_suppressElabErrors_1920_;
v___y_1877_ = v___y_1930_;
v___y_1878_ = v___y_1905_;
v___y_1879_ = v_openDecls_1915_;
v___y_1880_ = v_ref_1913_;
v___y_1881_ = v_options_1909_;
v___y_1882_ = v___y_1907_;
v___y_1883_ = v_maxHeartbeats_1917_;
v___y_1884_ = v___x_1933_;
goto v___jp_1861_;
}
}
else
{
lean_inc(v_currMacroScope_1918_);
lean_inc(v_maxHeartbeats_1917_);
lean_inc(v_initHeartbeats_1916_);
lean_inc(v_openDecls_1915_);
lean_inc(v_currNamespace_1914_);
lean_inc(v_ref_1913_);
lean_inc(v_maxRecDepth_1912_);
lean_inc(v_currRecDepth_1911_);
lean_inc_ref(v_toCold_1910_);
lean_inc_ref(v_options_1909_);
v___y_1862_ = v___x_1934_;
v___y_1863_ = v___y_1906_;
v___y_1864_ = v___x_1936_;
v___y_1865_ = v___x_1927_;
v___y_1866_ = v_lhs_1903_;
v___y_1867_ = v_diag_1919_;
v___y_1868_ = v_currRecDepth_1911_;
v___y_1869_ = v_currNamespace_1914_;
v___y_1870_ = v_initHeartbeats_1916_;
v___y_1871_ = v_maxRecDepth_1912_;
v___y_1872_ = v_rhs_1904_;
v___y_1873_ = v___y_1908_;
v___y_1874_ = v_currMacroScope_1918_;
v___y_1875_ = v_toCold_1910_;
v___y_1876_ = v_suppressElabErrors_1920_;
v___y_1877_ = v___y_1930_;
v___y_1878_ = v___y_1905_;
v___y_1879_ = v_openDecls_1915_;
v___y_1880_ = v_ref_1913_;
v___y_1881_ = v_options_1909_;
v___y_1882_ = v___y_1907_;
v___y_1883_ = v_maxHeartbeats_1917_;
v___y_1884_ = v___x_1933_;
goto v___jp_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = lean_is_level_def_eq(v_x_1943_, v_x_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1951_, lean_object* v_x_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1952_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1959_, v_x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2024_ = 0;
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2026_ = l_Lean_registerTraceClass(v___x_2023_, v___x_2024_, v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref_known(v___x_2026_, 1);
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2028_ = 1;
v___x_2029_ = l_Lean_registerTraceClass(v___x_2027_, v___x_2028_, v___x_2025_);
return v___x_2029_;
}
else
{
return v___x_2026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2031_;
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
