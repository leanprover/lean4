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
lean_object* v___f_47_; lean_object* v___x_935__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0___closed__0));
v___x_935__overap_48_ = lean_panic_fn_borrowed(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_935__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
size_t v_x_2648__boxed_196_; size_t v_x_2649__boxed_197_; lean_object* v_res_198_; 
v_x_2648__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_x_2649__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2___redArg(v_x_191_, v_x_2648__boxed_196_, v_x_2649__boxed_197_, v_x_194_, v_x_195_);
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
lean_object* v_ref_285_; lean_object* v___x_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_331_; 
v_ref_285_ = lean_ctor_get(v___y_282_, 2);
v___x_286_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_331_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_331_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_331_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v_traceState_292_; lean_object* v_env_293_; lean_object* v_nextMacroScope_294_; lean_object* v_ngen_295_; lean_object* v_auxDeclNGen_296_; lean_object* v_cache_297_; lean_object* v_messages_298_; lean_object* v_infoState_299_; lean_object* v_snapshotTasks_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_330_; 
v___x_291_ = lean_st_ref_take(v___y_283_);
v_traceState_292_ = lean_ctor_get(v___x_291_, 4);
v_env_293_ = lean_ctor_get(v___x_291_, 0);
v_nextMacroScope_294_ = lean_ctor_get(v___x_291_, 1);
v_ngen_295_ = lean_ctor_get(v___x_291_, 2);
v_auxDeclNGen_296_ = lean_ctor_get(v___x_291_, 3);
v_cache_297_ = lean_ctor_get(v___x_291_, 5);
v_messages_298_ = lean_ctor_get(v___x_291_, 6);
v_infoState_299_ = lean_ctor_get(v___x_291_, 7);
v_snapshotTasks_300_ = lean_ctor_get(v___x_291_, 8);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_330_ == 0)
{
v___x_302_ = v___x_291_;
v_isShared_303_ = v_isSharedCheck_330_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snapshotTasks_300_);
lean_inc(v_infoState_299_);
lean_inc(v_messages_298_);
lean_inc(v_cache_297_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_296_);
lean_inc(v_ngen_295_);
lean_inc(v_nextMacroScope_294_);
lean_inc(v_env_293_);
lean_dec(v___x_291_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_330_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint64_t v_tid_304_; lean_object* v_traces_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_329_; 
v_tid_304_ = lean_ctor_get_uint64(v_traceState_292_, sizeof(void*)*1);
v_traces_305_ = lean_ctor_get(v_traceState_292_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_traceState_292_);
if (v_isSharedCheck_329_ == 0)
{
v___x_307_ = v_traceState_292_;
v_isShared_308_ = v_isSharedCheck_329_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_traces_305_);
lean_dec(v_traceState_292_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_329_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; double v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
v___x_311_ = 0;
v___x_312_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_313_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_313_, 0, v_cls_278_);
lean_ctor_set(v___x_313_, 1, v___x_309_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
lean_ctor_set_float(v___x_313_, sizeof(void*)*3, v___x_310_);
lean_ctor_set_float(v___x_313_, sizeof(void*)*3 + 8, v___x_310_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*3 + 16, v___x_311_);
v___x_314_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__2));
v___x_315_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v_a_287_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
lean_inc(v_ref_285_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_ref_285_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_PersistentArray_push___redArg(v_traces_305_, v___x_316_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_317_);
v___x_319_ = v___x_307_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_317_);
lean_ctor_set_uint64(v_reuseFailAlloc_328_, sizeof(void*)*1, v_tid_304_);
v___x_319_ = v_reuseFailAlloc_328_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v___x_319_);
v___x_321_ = v___x_302_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_env_293_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_nextMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_ngen_295_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_auxDeclNGen_296_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_cache_297_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_messages_298_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_infoState_299_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_snapshotTasks_300_);
v___x_321_ = v_reuseFailAlloc_327_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_st_ref_put(v___y_283_, v___x_321_);
v___x_323_ = lean_box(0);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_323_);
v___x_325_ = v___x_289_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___boxed(lean_object* v_cls_332_, lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_332_, v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2));
v___x_344_ = lean_unsigned_to_nat(2u);
v___x_345_ = lean_unsigned_to_nat(39u);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1));
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__0));
v___x_348_ = l_mkPanicMessageWithDecl(v___x_347_, v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_361_ = l_Lean_Name_append(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__11));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__13));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* v_mvarId_368_, lean_object* v_v_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_Level_isMax(v_v_369_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_v_369_);
lean_dec(v_mvarId_368_);
v___x_376_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
v___x_377_ = l_panic___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(v___x_376_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_mkFreshLevelMVar(v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_toCold_379_; lean_object* v_options_380_; lean_object* v_a_381_; lean_object* v_inheritedTraceOptions_382_; uint8_t v_hasTrace_383_; lean_object* v___x_384_; 
v_toCold_379_ = lean_ctor_get(v_a_372_, 0);
v_options_380_ = lean_ctor_get(v_toCold_379_, 2);
v_a_381_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_378_, 1);
v_inheritedTraceOptions_382_ = lean_ctor_get(v_toCold_379_, 11);
v_hasTrace_383_ = lean_ctor_get_uint8(v_options_380_, sizeof(void*)*1);
v___x_384_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(v_mvarId_368_, v_v_369_, v_a_381_);
if (v_hasTrace_383_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_368_, v___x_384_, v_a_371_);
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
v___x_389_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_368_, v___x_384_, v_a_371_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__12);
lean_inc(v_mvarId_368_);
v___x_391_ = l_Lean_mkLevelMVar(v_mvarId_368_);
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
v___x_398_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_386_, v___x_397_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_368_, v___x_384_, v_a_371_);
return v___x_399_;
}
else
{
lean_dec(v___x_384_);
lean_dec(v_mvarId_368_);
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_v_369_);
lean_dec(v_mvarId_368_);
v_a_400_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_378_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_378_);
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
size_t v_x_3156__boxed_450_; size_t v_x_3157__boxed_451_; lean_object* v_res_452_; 
v_x_3156__boxed_450_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_x_3157__boxed_451_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_res_452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1_spec__1_spec__2(v_00_u03b2_444_, v_x_445_, v_x_3156__boxed_450_, v_x_3157__boxed_451_, v_x_448_, v_x_449_);
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
lean_object* v_toCold_507_; lean_object* v_options_508_; uint8_t v_hasTrace_509_; 
v_toCold_507_ = lean_ctor_get(v_a_489_, 0);
v_options_508_ = lean_ctor_get(v_toCold_507_, 2);
v_hasTrace_509_ = lean_ctor_get_uint8(v_options_508_, sizeof(void*)*1);
if (v_hasTrace_509_ == 0)
{
v___y_494_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_inheritedTraceOptions_510_; lean_object* v_cls_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_inheritedTraceOptions_510_ = lean_ctor_get(v_toCold_507_, 11);
v_cls_511_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_513_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_510_, v_options_508_, v___x_512_);
if (v___x_513_ == 0)
{
v___y_494_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_514_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___closed__1);
lean_inc(v_mvarId_486_);
v___x_515_ = l_Lean_mkLevelMVar(v_mvarId_486_);
v___x_516_ = l_Lean_MessageData_ofLevel(v___x_515_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_514_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
lean_inc(v_u_484_);
v___x_520_ = l_Lean_MessageData_ofLevel(v_u_484_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_511_, v___x_521_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_dec_ref_known(v___x_522_, 1);
v___y_494_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_mvarId_486_);
lean_dec(v_u_484_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* v_u_531_, lean_object* v_v_x27_532_, lean_object* v_mvarId_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_531_, v_v_x27_532_, v_mvarId_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_v_x27_532_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* v_u_540_, lean_object* v_v_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
if (lean_obj_tag(v_v_541_) == 2)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v_v_541_, 1);
lean_inc(v_a_551_);
if (lean_obj_tag(v_a_551_) == 5)
{
lean_object* v_a_552_; lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_552_ = lean_ctor_get(v_v_541_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v_v_541_, 2);
v_a_553_ = lean_ctor_get(v_a_551_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v_a_551_, 1);
v___x_554_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_540_, v_a_552_, v_a_553_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_552_);
return v___x_554_;
}
else
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v_v_541_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v_v_541_, 2);
if (lean_obj_tag(v_a_555_) == 5)
{
lean_object* v_a_556_; lean_object* v___x_557_; 
v_a_556_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v_a_555_, 1);
v___x_557_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(v_u_540_, v_a_551_, v_a_556_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_551_);
return v___x_557_;
}
else
{
lean_dec(v_a_555_);
lean_dec(v_a_551_);
lean_dec(v_u_540_);
goto v___jp_547_;
}
}
}
else
{
lean_dec(v_v_541_);
lean_dec(v_u_540_);
goto v___jp_547_;
}
v___jp_547_:
{
uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = 0;
v___x_549_ = lean_box(v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* v_u_558_, lean_object* v_v_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_558_, v_v_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_565_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* v_u_u2081_569_, lean_object* v_u_u2082_570_, lean_object* v_v_x27_571_, lean_object* v_mvarId_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
uint8_t v___x_578_; uint8_t v___x_579_; lean_object* v___y_581_; lean_object* v___y_593_; 
v___x_578_ = lean_level_eq(v_u_u2081_569_, v_v_x27_571_);
v___x_579_ = 1;
if (v___x_578_ == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_level_eq(v_u_u2082_570_, v_v_x27_571_);
lean_dec(v_u_u2082_570_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_mvarId_572_);
lean_dec(v_u_u2081_569_);
v___x_605_ = lean_box(v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v_toCold_607_; lean_object* v_options_608_; uint8_t v_hasTrace_609_; 
v_toCold_607_ = lean_ctor_get(v_a_575_, 0);
v_options_608_ = lean_ctor_get(v_toCold_607_, 2);
v_hasTrace_609_ = lean_ctor_get_uint8(v_options_608_, sizeof(void*)*1);
if (v_hasTrace_609_ == 0)
{
v___y_593_ = v_a_574_;
goto v___jp_592_;
}
else
{
lean_object* v_inheritedTraceOptions_610_; lean_object* v_cls_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_inheritedTraceOptions_610_ = lean_ctor_get(v_toCold_607_, 11);
v_cls_611_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_613_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_610_, v_options_608_, v___x_612_);
if (v___x_613_ == 0)
{
v___y_593_ = v_a_574_;
goto v___jp_592_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_614_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_572_);
v___x_615_ = l_Lean_mkLevelMVar(v_mvarId_572_);
v___x_616_ = l_Lean_MessageData_ofLevel(v___x_615_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_614_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
lean_inc(v_u_u2081_569_);
v___x_620_ = l_Lean_MessageData_ofLevel(v_u_u2081_569_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_611_, v___x_621_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_dec_ref_known(v___x_622_, 1);
v___y_593_ = v_a_574_;
goto v___jp_592_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_mvarId_572_);
lean_dec(v_u_u2081_569_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_631_; lean_object* v_options_632_; uint8_t v_hasTrace_633_; 
lean_dec(v_u_u2081_569_);
v_toCold_631_ = lean_ctor_get(v_a_575_, 0);
v_options_632_ = lean_ctor_get(v_toCold_631_, 2);
v_hasTrace_633_ = lean_ctor_get_uint8(v_options_632_, sizeof(void*)*1);
if (v_hasTrace_633_ == 0)
{
v___y_581_ = v_a_574_;
goto v___jp_580_;
}
else
{
lean_object* v_inheritedTraceOptions_634_; lean_object* v_cls_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_inheritedTraceOptions_634_ = lean_ctor_get(v_toCold_631_, 11);
v_cls_635_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_636_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_637_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_634_, v_options_632_, v___x_636_);
if (v___x_637_ == 0)
{
v___y_581_ = v_a_574_;
goto v___jp_580_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_638_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___closed__1);
lean_inc(v_mvarId_572_);
v___x_639_ = l_Lean_mkLevelMVar(v_mvarId_572_);
v___x_640_ = l_Lean_MessageData_ofLevel(v___x_639_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_inc(v_u_u2082_570_);
v___x_644_ = l_Lean_MessageData_ofLevel(v_u_u2082_570_);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v_cls_635_, v___x_645_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref_known(v___x_646_, 1);
v___y_581_ = v_a_574_;
goto v___jp_580_;
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_mvarId_572_);
lean_dec(v_u_u2082_570_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v___x_582_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_572_, v_u_u2082_570_, v___y_581_);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_591_);
v___x_584_ = v___x_582_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_dec(v___x_582_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_box(v___x_579_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
v___jp_592_:
{
lean_object* v___x_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v___x_594_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v_mvarId_572_, v_u_u2081_569_, v___y_593_);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_594_, 0);
lean_dec(v_unused_603_);
v___x_596_ = v___x_594_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_dec(v___x_594_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_box(v___x_579_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* v_u_u2081_655_, lean_object* v_u_u2082_656_, lean_object* v_v_x27_657_, lean_object* v_mvarId_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_u_u2081_655_, v_u_u2082_656_, v_v_x27_657_, v_mvarId_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_v_x27_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* v_u_665_, lean_object* v_v_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
if (lean_obj_tag(v_u_665_) == 2)
{
if (lean_obj_tag(v_v_666_) == 2)
{
lean_object* v_a_676_; 
v_a_676_ = lean_ctor_get(v_v_666_, 1);
lean_inc(v_a_676_);
if (lean_obj_tag(v_a_676_) == 5)
{
lean_object* v_a_677_; lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_677_ = lean_ctor_get(v_u_665_, 0);
lean_inc(v_a_677_);
v_a_678_ = lean_ctor_get(v_u_665_, 1);
lean_inc(v_a_678_);
lean_dec_ref_known(v_u_665_, 2);
v_a_679_ = lean_ctor_get(v_v_666_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v_v_666_, 2);
v_a_680_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v_a_676_, 1);
v___x_681_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_679_);
return v___x_681_;
}
else
{
lean_object* v_a_682_; 
v_a_682_ = lean_ctor_get(v_v_666_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v_v_666_, 2);
if (lean_obj_tag(v_a_682_) == 5)
{
lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_683_ = lean_ctor_get(v_u_665_, 0);
lean_inc(v_a_683_);
v_a_684_ = lean_ctor_get(v_u_665_, 1);
lean_inc(v_a_684_);
lean_dec_ref_known(v_u_665_, 2);
v_a_685_ = lean_ctor_get(v_a_682_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v_a_682_, 1);
v___x_686_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(v_a_683_, v_a_684_, v_a_676_, v_a_685_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_676_);
return v___x_686_;
}
else
{
lean_dec(v_a_682_);
lean_dec(v_a_676_);
lean_dec_ref_known(v_u_665_, 2);
goto v___jp_672_;
}
}
}
else
{
lean_dec_ref_known(v_u_665_, 2);
lean_dec(v_v_666_);
goto v___jp_672_;
}
}
else
{
lean_dec(v_v_666_);
lean_dec(v_u_665_);
goto v___jp_672_;
}
v___jp_672_:
{
uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = 0;
v___x_674_ = lean_box(v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* v_u_687_, lean_object* v_v_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_687_, v_v_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
return v_res_694_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_702_ = l_Lean_Name_append(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* v_lhs_706_, lean_object* v_rhs_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_toCold_713_; lean_object* v_ref_714_; lean_object* v___y_716_; lean_object* v_options_736_; uint8_t v_hasTrace_737_; 
v_toCold_713_ = lean_ctor_get(v_a_710_, 0);
v_ref_714_ = lean_ctor_get(v_a_710_, 2);
v_options_736_ = lean_ctor_get(v_toCold_713_, 2);
v_hasTrace_737_ = lean_ctor_get_uint8(v_options_736_, sizeof(void*)*1);
if (v_hasTrace_737_ == 0)
{
v___y_716_ = v_a_709_;
goto v___jp_715_;
}
else
{
lean_object* v_inheritedTraceOptions_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_inheritedTraceOptions_738_ = lean_ctor_get(v_toCold_713_, 11);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_740_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
v___x_741_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_738_, v_options_736_, v___x_740_);
if (v___x_741_ == 0)
{
v___y_716_ = v_a_709_;
goto v___jp_715_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_inc(v_lhs_706_);
v___x_742_ = l_Lean_MessageData_ofLevel(v_lhs_706_);
v___x_743_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
lean_inc(v_rhs_707_);
v___x_745_ = l_Lean_MessageData_ofLevel(v_rhs_707_);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_739_, v___x_746_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_dec_ref_known(v___x_747_, 1);
v___y_716_ = v_a_709_;
goto v___jp_715_;
}
else
{
lean_dec(v_rhs_707_);
lean_dec(v_lhs_706_);
return v___x_747_;
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
v_defEqCtx_x3f_726_ = lean_ctor_get(v_a_708_, 4);
lean_inc(v_defEqCtx_x3f_726_);
lean_inc(v_ref_714_);
v___x_727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_727_, 0, v_ref_714_);
lean_ctor_set(v___x_727_, 1, v_lhs_706_);
lean_ctor_set(v___x_727_, 2, v_rhs_707_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* v_lhs_748_, lean_object* v_rhs_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_748_, v_rhs_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* v_v_756_, lean_object* v_mvarId_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
if (lean_obj_tag(v_v_756_) == 5)
{
lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_763_ = lean_ctor_get(v_v_756_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v_v_756_, 1);
v___x_764_ = l_Lean_LMVarId_getLevel(v_a_763_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = l_Lean_LMVarId_getLevel(v_mvarId_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_776_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_776_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_nat_dec_lt(v_a_767_, v_a_765_);
lean_dec(v_a_765_);
lean_dec(v_a_767_);
v___x_772_ = lean_box(v___x_771_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v_a_765_);
v_a_777_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_766_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_766_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v_mvarId_757_);
v_a_785_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_764_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_764_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_mvarId_757_);
lean_dec(v_v_756_);
v___x_793_ = 0;
v___x_794_ = lean_box(v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* v_v_796_, lean_object* v_mvarId_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_796_, v_mvarId_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* v_u_804_, lean_object* v_v_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___y_812_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_887_; lean_object* v___y_901_; 
switch(lean_obj_tag(v_u_804_))
{
case 5:
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v_u_804_, 0);
lean_inc(v_a_914_);
v___x_915_ = l_Lean_LMVarId_isReadOnly(v_a_914_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1012_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_1012_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1012_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; 
v___x_920_ = lean_unbox(v_a_916_);
lean_dec(v_a_916_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_del_object(v___x_918_);
lean_inc(v_a_914_);
lean_inc(v_v_805_);
v___x_921_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(v_v_805_, v_a_914_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_998_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_998_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_998_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_998_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
uint8_t v___x_932_; 
v___x_932_ = lean_unbox(v_a_922_);
lean_dec(v_a_922_);
if (v___x_932_ == 0)
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_Level_occurs(v_u_804_, v_v_805_);
if (v___x_933_ == 0)
{
lean_object* v_toCold_934_; lean_object* v_options_935_; uint8_t v_hasTrace_936_; 
lean_del_object(v___x_924_);
v_toCold_934_ = lean_ctor_get(v_a_808_, 0);
v_options_935_ = lean_ctor_get(v_toCold_934_, 2);
v_hasTrace_936_ = lean_ctor_get_uint8(v_options_935_, sizeof(void*)*1);
if (v_hasTrace_936_ == 0)
{
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_806_);
v___y_887_ = v_a_807_;
goto v___jp_886_;
}
else
{
lean_object* v_inheritedTraceOptions_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_inheritedTraceOptions_937_ = lean_ctor_get(v_toCold_934_, 11);
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_940_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_937_, v_options_935_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_806_);
v___y_887_ = v_a_807_;
goto v___jp_886_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_inc_ref(v_u_804_);
v___x_941_ = l_Lean_MessageData_ofLevel(v_u_804_);
v___x_942_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_inc(v_v_805_);
v___x_944_ = l_Lean_MessageData_ofLevel(v_v_805_);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_938_, v___x_945_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_806_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_dec_ref_known(v___x_946_, 1);
v___y_887_ = v_a_807_;
goto v___jp_886_;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_807_);
lean_dec(v_v_805_);
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
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
else
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Level_isMax(v_v_805_);
if (v___x_955_ == 0)
{
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
goto v___jp_926_;
}
else
{
uint8_t v___x_956_; 
v___x_956_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(v_u_804_, v_v_805_);
if (v___x_956_ == 0)
{
if (v___x_955_ == 0)
{
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
goto v___jp_926_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_del_object(v___x_924_);
v___x_957_ = l_Lean_Level_mvarId_x21(v_u_804_);
lean_dec_ref_known(v_u_804_, 1);
v___x_958_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(v___x_957_, v_v_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_967_; 
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v___x_958_, 0);
lean_dec(v_unused_968_);
v___x_960_ = v___x_958_;
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
else
{
lean_dec(v___x_958_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_962_ = 1;
v___x_963_ = lean_box(v___x_962_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_963_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_958_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_958_);
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
else
{
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
goto v___jp_926_;
}
}
}
}
else
{
lean_object* v_toCold_977_; lean_object* v_options_978_; uint8_t v_hasTrace_979_; 
lean_del_object(v___x_924_);
v_toCold_977_ = lean_ctor_get(v_a_808_, 0);
v_options_978_ = lean_ctor_get(v_toCold_977_, 2);
v_hasTrace_979_ = lean_ctor_get_uint8(v_options_978_, sizeof(void*)*1);
if (v_hasTrace_979_ == 0)
{
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_806_);
v___y_901_ = v_a_807_;
goto v___jp_900_;
}
else
{
lean_object* v_inheritedTraceOptions_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_inheritedTraceOptions_980_ = lean_ctor_get(v_toCold_977_, 11);
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__7));
v___x_982_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__10);
v___x_983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_980_, v_options_978_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_806_);
v___y_901_ = v_a_807_;
goto v___jp_900_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_inc(v_v_805_);
v___x_984_ = l_Lean_MessageData_ofLevel(v_v_805_);
v___x_985_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__14);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_inc_ref(v_u_804_);
v___x_987_ = l_Lean_MessageData_ofLevel(v_u_804_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_981_, v___x_988_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_806_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_dec_ref_known(v___x_989_, 1);
v___y_901_ = v_a_807_;
goto v___jp_900_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_807_);
lean_dec(v_v_805_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
v___jp_926_:
{
uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = 2;
v___x_928_ = lean_box(v___x_927_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_928_);
v___x_930_ = v___x_924_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
v_a_999_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_921_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_921_);
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
else
{
uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
v___x_1007_ = 2;
v___x_1008_ = lean_box(v___x_1007_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_1008_);
v___x_1010_ = v___x_918_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref_known(v_u_804_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
v_a_1013_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_915_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_915_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
case 0:
{
switch(lean_obj_tag(v_v_805_))
{
case 5:
{
lean_dec_ref_known(v_v_805_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
goto v___jp_882_;
}
case 2:
{
lean_object* v_a_1021_; lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v_v_805_, 0);
lean_inc(v_a_1021_);
v_a_1022_ = lean_ctor_get(v_v_805_, 1);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_v_805_, 2);
lean_inc(v_a_809_);
lean_inc_ref(v_a_808_);
lean_inc(v_a_807_);
lean_inc_ref(v_a_806_);
v___x_1023_ = lean_is_level_def_eq(v_u_804_, v_a_1021_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; uint8_t v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
v___x_1025_ = lean_unbox(v_a_1024_);
lean_dec(v_a_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v_a_1022_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
v___y_812_ = v___x_1023_;
goto v___jp_811_;
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref_known(v___x_1023_, 1);
v___x_1026_ = lean_is_level_def_eq(v_u_804_, v_a_1022_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
v___y_812_ = v___x_1026_;
goto v___jp_811_;
}
}
else
{
lean_dec(v_a_1022_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
v___y_812_ = v___x_1023_;
goto v___jp_811_;
}
}
case 3:
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v_v_805_, 1);
lean_inc(v_a_1027_);
lean_dec_ref_known(v_v_805_, 2);
v___x_1028_ = lean_is_level_def_eq(v_u_804_, v_a_1027_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1039_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
uint8_t v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1033_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
v___x_1034_ = l_Lean_Bool_toLBool(v___x_1033_);
v___x_1035_ = lean_box(v___x_1034_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1028_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1028_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
case 1:
{
uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref_known(v_v_805_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
v___x_1048_ = 0;
v___x_1049_ = lean_box(v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
default: 
{
v___y_837_ = v_a_806_;
v___y_838_ = v_a_807_;
v___y_839_ = v_a_808_;
v___y_840_ = v_a_809_;
goto v___jp_836_;
}
}
}
case 1:
{
lean_object* v_a_1051_; uint8_t v___y_1053_; 
v_a_1051_ = lean_ctor_get(v_u_804_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v_u_804_, 1);
if (lean_obj_tag(v_v_805_) == 5)
{
lean_dec_ref_known(v_v_805_, 1);
lean_dec(v_a_1051_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
goto v___jp_882_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Level_isParam(v_v_805_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Level_isMVar(v_a_1051_);
if (v___x_1098_ == 0)
{
v___y_1053_ = v___x_1097_;
goto v___jp_1052_;
}
else
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Lean_Level_occurs(v_a_1051_, v_v_805_);
v___y_1053_ = v___x_1099_;
goto v___jp_1052_;
}
}
else
{
uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_a_1051_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
v___x_1100_ = 0;
v___x_1101_ = lean_box(v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
v___jp_1052_:
{
if (v___y_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_decLevel_x3f(v_v_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1085_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1085_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1085_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
if (lean_obj_tag(v_a_1055_) == 0)
{
uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec(v_a_1051_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
v___x_1059_ = 2;
v___x_1060_ = lean_box(v___x_1059_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v_val_1064_; lean_object* v___x_1065_; 
lean_del_object(v___x_1057_);
v_val_1064_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_val_1064_);
lean_dec_ref_known(v_a_1055_, 1);
v___x_1065_ = lean_is_level_def_eq(v_a_1051_, v_val_1064_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1070_ = lean_unbox(v_a_1066_);
lean_dec(v_a_1066_);
v___x_1071_ = l_Lean_Bool_toLBool(v___x_1070_);
v___x_1072_ = lean_box(v___x_1071_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1065_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1065_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_a_1051_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
v_a_1086_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1054_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1054_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_a_1051_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_v_805_);
v___x_1094_ = 2;
v___x_1095_ = lean_box(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
}
default: 
{
if (lean_obj_tag(v_v_805_) == 5)
{
lean_dec_ref_known(v_v_805_, 1);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_u_804_);
goto v___jp_882_;
}
else
{
v___y_837_ = v_a_806_;
v___y_838_ = v_a_807_;
v___y_839_ = v_a_808_;
v___y_840_ = v_a_809_;
goto v___jp_836_;
}
}
}
v___jp_811_:
{
if (lean_obj_tag(v___y_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v_a_813_ = lean_ctor_get(v___y_812_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___y_812_);
if (v_isSharedCheck_823_ == 0)
{
v___x_815_ = v___y_812_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___y_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_817_ = lean_unbox(v_a_813_);
lean_dec(v_a_813_);
v___x_818_ = l_Lean_Bool_toLBool(v___x_817_);
v___x_819_ = lean_box(v___x_818_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___y_812_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___y_812_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___y_812_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___y_812_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
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
lean_dec(v_v_805_);
lean_dec(v_u_804_);
goto v___jp_832_;
}
else
{
lean_object* v___x_842_; 
lean_inc(v_v_805_);
lean_inc(v_u_804_);
v___x_842_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(v_u_804_, v_v_805_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
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
v___x_848_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(v_u_804_, v_v_805_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
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
lean_dec(v_v_805_);
lean_dec(v_u_804_);
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
lean_dec(v_v_805_);
lean_dec(v_u_804_);
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
uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = 2;
v___x_884_ = lean_box(v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_898_; 
v___x_888_ = l_Lean_Level_mvarId_x21(v_u_804_);
lean_dec(v_u_804_);
v___x_889_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_888_, v_v_805_, v___y_887_);
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
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_912_; 
v___x_902_ = l_Lean_Level_mvarId_x21(v_v_805_);
lean_dec(v_v_805_);
v___x_903_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(v___x_902_, v_u_804_, v___y_901_);
lean_dec(v___y_901_);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_903_, 0);
lean_dec(v_unused_913_);
v___x_905_ = v___x_903_;
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
else
{
lean_dec(v___x_903_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_907_ = 1;
v___x_908_ = lean_box(v___x_907_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___boxed(lean_object* v_u_1103_, lean_object* v_v_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_u_1103_, v_v_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(lean_object* v_l_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_mctx_1115_; lean_object* v___x_1116_; lean_object* v_fst_1117_; lean_object* v_snd_1118_; lean_object* v___x_1119_; lean_object* v_cache_1120_; lean_object* v_zetaDeltaFVarIds_1121_; lean_object* v_postponed_1122_; lean_object* v_diag_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v___x_1114_ = lean_st_ref_get(v___y_1112_);
v_mctx_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_mctx_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = lean_instantiate_level_mvars(v_mctx_1115_, v_l_1111_);
v_fst_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_fst_1117_);
v_snd_1118_ = lean_ctor_get(v___x_1116_, 1);
lean_inc(v_snd_1118_);
lean_dec_ref(v___x_1116_);
v___x_1119_ = lean_st_ref_take(v___y_1112_);
v_cache_1120_ = lean_ctor_get(v___x_1119_, 1);
v_zetaDeltaFVarIds_1121_ = lean_ctor_get(v___x_1119_, 2);
v_postponed_1122_ = lean_ctor_get(v___x_1119_, 3);
v_diag_1123_ = lean_ctor_get(v___x_1119_, 4);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v___x_1119_, 0);
lean_dec(v_unused_1133_);
v___x_1125_ = v___x_1119_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_diag_1123_);
lean_inc(v_postponed_1122_);
lean_inc(v_zetaDeltaFVarIds_1121_);
lean_inc(v_cache_1120_);
lean_dec(v___x_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v_fst_1117_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_fst_1117_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_cache_1120_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_zetaDeltaFVarIds_1121_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_postponed_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_diag_1123_);
v___x_1128_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_st_ref_put(v___y_1112_, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_snd_1118_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg___boxed(lean_object* v_l_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1134_, v___y_1135_);
lean_dec(v___y_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* v_l_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_l_1138_, v___y_1140_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* v_l_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0(v_l_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1151_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(32u);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1155_ = ((size_t)5ULL);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_unsigned_to_nat(32u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
v___x_1159_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__0);
v___x_1160_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
lean_ctor_set(v___x_1160_, 2, v___x_1156_);
lean_ctor_set(v___x_1160_, 3, v___x_1156_);
lean_ctor_set_usize(v___x_1160_, 4, v___x_1155_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v_traceState_1164_; lean_object* v_traces_1165_; lean_object* v___x_1166_; lean_object* v_traceState_1167_; lean_object* v_env_1168_; lean_object* v_nextMacroScope_1169_; lean_object* v_ngen_1170_; lean_object* v_auxDeclNGen_1171_; lean_object* v_cache_1172_; lean_object* v_messages_1173_; lean_object* v_infoState_1174_; lean_object* v_snapshotTasks_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1194_; 
v___x_1163_ = lean_st_ref_get(v___y_1161_);
v_traceState_1164_ = lean_ctor_get(v___x_1163_, 4);
lean_inc_ref(v_traceState_1164_);
lean_dec(v___x_1163_);
v_traces_1165_ = lean_ctor_get(v_traceState_1164_, 0);
lean_inc_ref(v_traces_1165_);
lean_dec_ref(v_traceState_1164_);
v___x_1166_ = lean_st_ref_take(v___y_1161_);
v_traceState_1167_ = lean_ctor_get(v___x_1166_, 4);
v_env_1168_ = lean_ctor_get(v___x_1166_, 0);
v_nextMacroScope_1169_ = lean_ctor_get(v___x_1166_, 1);
v_ngen_1170_ = lean_ctor_get(v___x_1166_, 2);
v_auxDeclNGen_1171_ = lean_ctor_get(v___x_1166_, 3);
v_cache_1172_ = lean_ctor_get(v___x_1166_, 5);
v_messages_1173_ = lean_ctor_get(v___x_1166_, 6);
v_infoState_1174_ = lean_ctor_get(v___x_1166_, 7);
v_snapshotTasks_1175_ = lean_ctor_get(v___x_1166_, 8);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1177_ = v___x_1166_;
v_isShared_1178_ = v_isSharedCheck_1194_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snapshotTasks_1175_);
lean_inc(v_infoState_1174_);
lean_inc(v_messages_1173_);
lean_inc(v_cache_1172_);
lean_inc(v_traceState_1167_);
lean_inc(v_auxDeclNGen_1171_);
lean_inc(v_ngen_1170_);
lean_inc(v_nextMacroScope_1169_);
lean_inc(v_env_1168_);
lean_dec(v___x_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1194_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
uint64_t v_tid_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1192_; 
v_tid_1179_ = lean_ctor_get_uint64(v_traceState_1167_, sizeof(void*)*1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_traceState_1167_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_traceState_1167_, 0);
lean_dec(v_unused_1193_);
v___x_1181_ = v_traceState_1167_;
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_traceState_1167_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___closed__1);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1183_);
lean_ctor_set_uint64(v_reuseFailAlloc_1191_, sizeof(void*)*1, v_tid_1179_);
v___x_1185_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 4, v___x_1185_);
v___x_1187_ = v___x_1177_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_env_1168_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_nextMacroScope_1169_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_ngen_1170_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_auxDeclNGen_1171_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_cache_1172_);
lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1190_, 8, v_snapshotTasks_1175_);
v___x_1187_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_st_ref_put(v___y_1161_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_traces_1165_);
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg___boxed(lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1195_);
lean_dec(v___y_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___boxed(lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1(v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(lean_object* v_o_1210_, lean_object* v_k_1211_, uint8_t v_v_1212_){
_start:
{
lean_object* v_map_1213_; uint8_t v_hasTrace_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1228_; 
v_map_1213_ = lean_ctor_get(v_o_1210_, 0);
v_hasTrace_1214_ = lean_ctor_get_uint8(v_o_1210_, sizeof(void*)*1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_o_1210_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1216_ = v_o_1210_;
v_isShared_1217_ = v_isSharedCheck_1228_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_map_1213_);
lean_dec(v_o_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1228_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1218_, 0, v_v_1212_);
lean_inc(v_k_1211_);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1211_, v___x_1218_, v_map_1213_);
if (v_hasTrace_1214_ == 0)
{
lean_object* v___x_1220_; uint8_t v___x_1221_; lean_object* v___x_1223_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1221_ = l_Lean_Name_isPrefixOf(v___x_1220_, v_k_1211_);
lean_dec(v_k_1211_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1219_);
v___x_1223_ = v___x_1216_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1219_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*1, v___x_1221_);
return v___x_1223_;
}
}
else
{
lean_object* v___x_1226_; 
lean_dec(v_k_1211_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1219_);
v___x_1226_ = v___x_1216_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1227_, sizeof(void*)*1, v_hasTrace_1214_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2___boxed(lean_object* v_o_1229_, lean_object* v_k_1230_, lean_object* v_v_1231_){
_start:
{
uint8_t v_v_boxed_1232_; lean_object* v_res_1233_; 
v_v_boxed_1232_ = lean_unbox(v_v_1231_);
v_res_1233_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v_o_1229_, v_k_1230_, v_v_boxed_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(lean_object* v_opts_1234_, lean_object* v_opt_1235_){
_start:
{
lean_object* v_name_1236_; lean_object* v_defValue_1237_; lean_object* v_map_1238_; lean_object* v___x_1239_; 
v_name_1236_ = lean_ctor_get(v_opt_1235_, 0);
v_defValue_1237_ = lean_ctor_get(v_opt_1235_, 1);
v_map_1238_ = lean_ctor_get(v_opts_1234_, 0);
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1238_, v_name_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_unbox(v_defValue_1237_);
return v___x_1240_;
}
else
{
lean_object* v_val_1241_; 
v_val_1241_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v___x_1239_, 1);
if (lean_obj_tag(v_val_1241_) == 1)
{
uint8_t v_v_1242_; 
v_v_1242_ = lean_ctor_get_uint8(v_val_1241_, 0);
lean_dec_ref_known(v_val_1241_, 0);
return v_v_1242_;
}
else
{
uint8_t v___x_1243_; 
lean_dec(v_val_1241_);
v___x_1243_ = lean_unbox(v_defValue_1237_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3___boxed(lean_object* v_opts_1244_, lean_object* v_opt_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1244_, v_opt_1245_);
lean_dec_ref(v_opt_1245_);
lean_dec_ref(v_opts_1244_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(lean_object* v_opts_1248_, lean_object* v_opt_1249_){
_start:
{
lean_object* v_name_1250_; lean_object* v_defValue_1251_; lean_object* v_map_1252_; lean_object* v___x_1253_; 
v_name_1250_ = lean_ctor_get(v_opt_1249_, 0);
v_defValue_1251_ = lean_ctor_get(v_opt_1249_, 1);
v_map_1252_ = lean_ctor_get(v_opts_1248_, 0);
v___x_1253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1252_, v_name_1250_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_inc(v_defValue_1251_);
return v_defValue_1251_;
}
else
{
lean_object* v_val_1254_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v___x_1253_, 1);
if (lean_obj_tag(v_val_1254_) == 3)
{
lean_object* v_v_1255_; 
v_v_1255_ = lean_ctor_get(v_val_1254_, 0);
lean_inc(v_v_1255_);
lean_dec_ref_known(v_val_1254_, 1);
return v_v_1255_;
}
else
{
lean_dec(v_val_1254_);
lean_inc(v_defValue_1251_);
return v_defValue_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4___boxed(lean_object* v_opts_1256_, lean_object* v_opt_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1256_, v_opt_1257_);
lean_dec_ref(v_opt_1257_);
lean_dec_ref(v_opts_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(uint8_t v___x_1259_, lean_object* v_lhs_1260_, lean_object* v_rhs_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, uint8_t v___x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___y_1298_; 
if (v___x_1259_ == 0)
{
lean_object* v___x_1335_; lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
lean_inc(v_lhs_1260_);
v___x_1335_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_lhs_1260_, v___y_1266_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref(v___x_1335_);
lean_inc(v_rhs_1261_);
v___x_1337_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__0___redArg(v_rhs_1261_, v___y_1266_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Lean_Level_normalize(v_a_1336_);
lean_dec(v_a_1336_);
v___x_1340_ = l_Lean_Level_normalize(v_a_1338_);
lean_dec(v_a_1338_);
v___x_1341_ = lean_level_eq(v_lhs_1260_, v___x_1339_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
v___x_1342_ = lean_is_level_def_eq(v___x_1339_, v___x_1340_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1342_;
}
else
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_level_eq(v_rhs_1261_, v___x_1340_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
v___x_1344_ = lean_is_level_def_eq(v___x_1339_, v___x_1340_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; 
lean_dec(v___x_1340_);
lean_dec(v___x_1339_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v_rhs_1261_);
lean_inc(v_lhs_1260_);
v___x_1345_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_lhs_1260_, v_rhs_1261_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
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
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v_lhs_1260_);
lean_inc(v_rhs_1261_);
v___x_1360_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(v_rhs_1261_, v_lhs_1260_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
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
lean_inc(v_lhs_1260_);
v___x_1374_ = l_Lean_Meta_hasAssignableLevelMVar(v_lhs_1260_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
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
lean_dec_ref_known(v___x_1374_, 1);
lean_inc(v_rhs_1261_);
v___x_1377_ = l_Lean_Meta_hasAssignableLevelMVar(v_rhs_1261_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
v___x_1396_ = l_Lean_Level_getOffset(v_lhs_1260_);
lean_dec(v_lhs_1260_);
v___x_1397_ = l_Lean_Level_getOffset(v_rhs_1261_);
lean_dec(v_rhs_1261_);
v___x_1398_ = lean_nat_dec_eq(v___x_1396_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
v___jp_1270_:
{
lean_object* v_toCold_1271_; lean_object* v_options_1272_; uint8_t v_hasTrace_1273_; 
v_toCold_1271_ = lean_ctor_get(v___y_1267_, 0);
v_options_1272_ = lean_ctor_get(v_toCold_1271_, 2);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_options_1272_, sizeof(void*)*1);
if (v_hasTrace_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
v___x_1274_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1274_;
}
else
{
lean_object* v_inheritedTraceOptions_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_inheritedTraceOptions_1275_ = lean_ctor_get(v_toCold_1271_, 11);
v___x_1276_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__0));
v___x_1277_ = l_Lean_Name_mkStr3(v___x_1262_, v___x_1263_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
lean_inc(v___x_1277_);
v___x_1279_ = l_Lean_Name_append(v___x_1278_, v___x_1277_);
v___x_1280_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1275_, v_options_1272_, v___x_1279_);
lean_dec(v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec(v___x_1277_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
v___x_1281_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1282_ = l_Lean_MessageData_ofLevel(v_lhs_1260_);
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_MessageData_ofLevel(v_rhs_1261_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2(v___x_1277_, v___x_1286_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1288_; 
lean_dec_ref_known(v___x_1287_, 1);
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
v___x_1304_ = l_Lean_Meta_Context_config(v___y_1265_);
v_isDefEqStuckEx_1305_ = lean_ctor_get_uint8(v___x_1304_, 4);
lean_dec_ref(v___x_1304_);
if (v_isDefEqStuckEx_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
v___x_1306_ = lean_box(v___x_1259_);
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
v___x_1310_ = l_Lean_Level_isMVar(v_lhs_1260_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_Level_isMVar(v_rhs_1261_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
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
goto v___jp_1270_;
}
}
else
{
lean_del_object(v___x_1301_);
goto v___jp_1270_;
}
}
}
else
{
lean_object* v___x_1316_; 
lean_del_object(v___x_1301_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
v___x_1316_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(v_lhs_1260_, v_rhs_1261_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
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
v___x_1320_ = lean_box(v___x_1264_);
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
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec(v_rhs_1261_);
lean_dec(v_lhs_1260_);
return v___y_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* v___x_1401_, lean_object* v_lhs_1402_, lean_object* v_rhs_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___x_13030__boxed_1412_; uint8_t v___x_13033__boxed_1413_; lean_object* v_res_1414_; 
v___x_13030__boxed_1412_ = lean_unbox(v___x_1401_);
v___x_13033__boxed_1413_ = lean_unbox(v___x_1406_);
v_res_1414_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_13030__boxed_1412_, v_lhs_1402_, v_rhs_1403_, v___x_1404_, v___x_1405_, v___x_13033__boxed_1413_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(lean_object* v_e_1415_){
_start:
{
if (lean_obj_tag(v_e_1415_) == 0)
{
uint8_t v___x_1416_; 
v___x_1416_ = 2;
return v___x_1416_;
}
else
{
lean_object* v_a_1417_; uint8_t v___x_1418_; 
v_a_1417_ = lean_ctor_get(v_e_1415_, 0);
v___x_1418_ = lean_unbox(v_a_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = 1;
return v___x_1419_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = 0;
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7___boxed(lean_object* v_e_1421_){
_start:
{
uint8_t v_res_1422_; lean_object* v_r_1423_; 
v_res_1422_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_e_1421_);
lean_dec_ref(v_e_1421_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v_x_1424_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1424_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v_x_1424_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v_x_1424_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 1);
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_a_1434_ = lean_ctor_get(v_x_1424_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_x_1424_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v_x_1424_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v_x_1424_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 0);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg___boxed(lean_object* v_x_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(size_t v_sz_1445_, size_t v_i_1446_, lean_object* v_bs_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_lt(v_i_1446_, v_sz_1445_);
if (v___x_1448_ == 0)
{
return v_bs_1447_;
}
else
{
lean_object* v_v_1449_; lean_object* v_msg_1450_; lean_object* v___x_1451_; lean_object* v_bs_x27_1452_; size_t v___x_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v_v_1449_ = lean_array_uget_borrowed(v_bs_1447_, v_i_1446_);
v_msg_1450_ = lean_ctor_get(v_v_1449_, 1);
lean_inc_ref(v_msg_1450_);
v___x_1451_ = lean_unsigned_to_nat(0u);
v_bs_x27_1452_ = lean_array_uset(v_bs_1447_, v_i_1446_, v___x_1451_);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1446_, v___x_1453_);
v___x_1455_ = lean_array_uset(v_bs_x27_1452_, v_i_1446_, v_msg_1450_);
v_i_1446_ = v___x_1454_;
v_bs_1447_ = v___x_1455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_1457_, lean_object* v_i_1458_, lean_object* v_bs_1459_){
_start:
{
size_t v_sz_boxed_1460_; size_t v_i_boxed_1461_; lean_object* v_res_1462_; 
v_sz_boxed_1460_ = lean_unbox_usize(v_sz_1457_);
lean_dec(v_sz_1457_);
v_i_boxed_1461_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_boxed_1460_, v_i_boxed_1461_, v_bs_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(lean_object* v_oldTraces_1463_, lean_object* v_data_1464_, lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_toCold_1472_; lean_object* v_currRecDepth_1473_; lean_object* v_ref_1474_; uint8_t v_diag_1475_; uint8_t v_suppressElabErrors_1476_; lean_object* v___x_1477_; lean_object* v_traceState_1478_; lean_object* v_traces_1479_; lean_object* v_ref_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v_msg_1486_; lean_object* v___x_1487_; lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1525_; 
v_toCold_1472_ = lean_ctor_get(v___y_1469_, 0);
v_currRecDepth_1473_ = lean_ctor_get(v___y_1469_, 1);
v_ref_1474_ = lean_ctor_get(v___y_1469_, 2);
v_diag_1475_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3);
v_suppressElabErrors_1476_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3 + 1);
v___x_1477_ = lean_st_ref_get(v___y_1470_);
v_traceState_1478_ = lean_ctor_get(v___x_1477_, 4);
lean_inc_ref(v_traceState_1478_);
lean_dec(v___x_1477_);
v_traces_1479_ = lean_ctor_get(v_traceState_1478_, 0);
lean_inc_ref(v_traces_1479_);
lean_dec_ref(v_traceState_1478_);
v_ref_1480_ = l_Lean_replaceRef(v_ref_1465_, v_ref_1474_);
lean_inc(v_currRecDepth_1473_);
lean_inc_ref(v_toCold_1472_);
v___x_1481_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1481_, 0, v_toCold_1472_);
lean_ctor_set(v___x_1481_, 1, v_currRecDepth_1473_);
lean_ctor_set(v___x_1481_, 2, v_ref_1480_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3, v_diag_1475_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3 + 1, v_suppressElabErrors_1476_);
v___x_1482_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1479_);
lean_dec_ref(v_traces_1479_);
v_sz_1483_ = lean_array_size(v___x_1482_);
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5_spec__6(v_sz_1483_, v___x_1484_, v___x_1482_);
v_msg_1486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1486_, 0, v_data_1464_);
lean_ctor_set(v_msg_1486_, 1, v_msg_1466_);
lean_ctor_set(v_msg_1486_, 2, v___x_1485_);
v___x_1487_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_msg_1486_, v___y_1467_, v___y_1468_, v___x_1481_, v___y_1470_);
lean_dec_ref_known(v___x_1481_, 3);
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1525_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1525_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v_traceState_1493_; lean_object* v_env_1494_; lean_object* v_nextMacroScope_1495_; lean_object* v_ngen_1496_; lean_object* v_auxDeclNGen_1497_; lean_object* v_cache_1498_; lean_object* v_messages_1499_; lean_object* v_infoState_1500_; lean_object* v_snapshotTasks_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1524_; 
v___x_1492_ = lean_st_ref_take(v___y_1470_);
v_traceState_1493_ = lean_ctor_get(v___x_1492_, 4);
v_env_1494_ = lean_ctor_get(v___x_1492_, 0);
v_nextMacroScope_1495_ = lean_ctor_get(v___x_1492_, 1);
v_ngen_1496_ = lean_ctor_get(v___x_1492_, 2);
v_auxDeclNGen_1497_ = lean_ctor_get(v___x_1492_, 3);
v_cache_1498_ = lean_ctor_get(v___x_1492_, 5);
v_messages_1499_ = lean_ctor_get(v___x_1492_, 6);
v_infoState_1500_ = lean_ctor_get(v___x_1492_, 7);
v_snapshotTasks_1501_ = lean_ctor_get(v___x_1492_, 8);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1503_ = v___x_1492_;
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snapshotTasks_1501_);
lean_inc(v_infoState_1500_);
lean_inc(v_messages_1499_);
lean_inc(v_cache_1498_);
lean_inc(v_traceState_1493_);
lean_inc(v_auxDeclNGen_1497_);
lean_inc(v_ngen_1496_);
lean_inc(v_nextMacroScope_1495_);
lean_inc(v_env_1494_);
lean_dec(v___x_1492_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
uint64_t v_tid_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1522_; 
v_tid_1505_ = lean_ctor_get_uint64(v_traceState_1493_, sizeof(void*)*1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_traceState_1493_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_traceState_1493_, 0);
lean_dec(v_unused_1523_);
v___x_1507_ = v_traceState_1493_;
v_isShared_1508_ = v_isSharedCheck_1522_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_traceState_1493_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1522_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_ref_1465_);
lean_ctor_set(v___x_1509_, 1, v_a_1488_);
v___x_1510_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1463_, v___x_1509_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1510_);
lean_ctor_set_uint64(v_reuseFailAlloc_1521_, sizeof(void*)*1, v_tid_1505_);
v___x_1512_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v___x_1512_);
v___x_1514_ = v___x_1503_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_env_1494_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_nextMacroScope_1495_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_ngen_1496_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_auxDeclNGen_1497_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1520_, 5, v_cache_1498_);
lean_ctor_set(v_reuseFailAlloc_1520_, 6, v_messages_1499_);
lean_ctor_set(v_reuseFailAlloc_1520_, 7, v_infoState_1500_);
lean_ctor_set(v_reuseFailAlloc_1520_, 8, v_snapshotTasks_1501_);
v___x_1514_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1515_ = lean_st_ref_put(v___y_1470_, v___x_1514_);
v___x_1516_ = lean_box(0);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1516_);
v___x_1518_ = v___x_1490_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5___boxed(lean_object* v_oldTraces_1526_, lean_object* v_data_1527_, lean_object* v_ref_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1526_, v_data_1527_, v_ref_1528_, v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1535_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1536_; double v___x_1537_; 
v___x_1536_ = lean_unsigned_to_nat(1000u);
v___x_1537_ = lean_float_of_nat(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(lean_object* v_cls_1538_, uint8_t v_collapsed_1539_, lean_object* v_tag_1540_, lean_object* v_opts_1541_, uint8_t v_clsEnabled_1542_, lean_object* v_oldTraces_1543_, lean_object* v_ref_1544_, lean_object* v_msg_1545_, lean_object* v_resStartStop_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_fst_1552_; lean_object* v_snd_1553_; lean_object* v_data_1555_; lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; uint8_t v___y_1580_; double v___y_1611_; 
v_fst_1552_ = lean_ctor_get(v_resStartStop_1546_, 0);
lean_inc(v_fst_1552_);
v_snd_1553_ = lean_ctor_get(v_resStartStop_1546_, 1);
lean_inc(v_snd_1553_);
lean_dec_ref(v_resStartStop_1546_);
v_fst_1566_ = lean_ctor_get(v_snd_1553_, 0);
lean_inc(v_fst_1566_);
v_snd_1567_ = lean_ctor_get(v_snd_1553_, 1);
lean_inc(v_snd_1567_);
lean_dec(v_snd_1553_);
v___x_1568_ = l_Lean_trace_profiler;
v___x_1569_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1541_, v___x_1568_);
if (v___x_1569_ == 0)
{
v___y_1580_ = v___x_1569_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1617_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_opts_1541_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; double v___x_1620_; double v___x_1621_; double v___x_1622_; 
v___x_1618_ = l_Lean_trace_profiler_threshold;
v___x_1619_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1541_, v___x_1618_);
v___x_1620_ = lean_float_of_nat(v___x_1619_);
v___x_1621_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___closed__0);
v___x_1622_ = lean_float_div(v___x_1620_, v___x_1621_);
v___y_1611_ = v___x_1622_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; double v___x_1625_; 
v___x_1623_ = l_Lean_trace_profiler_threshold;
v___x_1624_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v_opts_1541_, v___x_1623_);
v___x_1625_ = lean_float_of_nat(v___x_1624_);
v___y_1611_ = v___x_1625_;
goto v___jp_1610_;
}
}
v___jp_1554_:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__5(v_oldTraces_1543_, v_data_1555_, v_ref_1544_, v_msg_1545_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
lean_dec_ref_known(v___x_1556_, 1);
v___x_1557_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1552_);
return v___x_1557_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_fst_1552_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
v___jp_1570_:
{
uint8_t v_result_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; double v___x_1574_; lean_object* v_data_1575_; 
v_result_1571_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__7(v_fst_1552_);
v___x_1572_ = lean_box(v_result_1571_);
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
v___x_1574_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__0);
lean_inc_ref(v_tag_1540_);
lean_inc_ref(v___x_1573_);
lean_inc(v_cls_1538_);
v_data_1575_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1575_, 0, v_cls_1538_);
lean_ctor_set(v_data_1575_, 1, v___x_1573_);
lean_ctor_set(v_data_1575_, 2, v_tag_1540_);
lean_ctor_set_float(v_data_1575_, sizeof(void*)*3, v___x_1574_);
lean_ctor_set_float(v_data_1575_, sizeof(void*)*3 + 8, v___x_1574_);
lean_ctor_set_uint8(v_data_1575_, sizeof(void*)*3 + 16, v_collapsed_1539_);
if (v___x_1569_ == 0)
{
lean_dec_ref_known(v___x_1573_, 1);
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref(v_tag_1540_);
lean_dec(v_cls_1538_);
v_data_1555_ = v_data_1575_;
goto v___jp_1554_;
}
else
{
lean_object* v_data_1576_; double v___x_1577_; double v___x_1578_; 
lean_dec_ref_known(v_data_1575_, 3);
v_data_1576_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1576_, 0, v_cls_1538_);
lean_ctor_set(v_data_1576_, 1, v___x_1573_);
lean_ctor_set(v_data_1576_, 2, v_tag_1540_);
v___x_1577_ = lean_unbox_float(v_fst_1566_);
lean_dec(v_fst_1566_);
lean_ctor_set_float(v_data_1576_, sizeof(void*)*3, v___x_1577_);
v___x_1578_ = lean_unbox_float(v_snd_1567_);
lean_dec(v_snd_1567_);
lean_ctor_set_float(v_data_1576_, sizeof(void*)*3 + 8, v___x_1578_);
lean_ctor_set_uint8(v_data_1576_, sizeof(void*)*3 + 16, v_collapsed_1539_);
v_data_1555_ = v_data_1576_;
goto v___jp_1554_;
}
}
v___jp_1579_:
{
if (v_clsEnabled_1542_ == 0)
{
if (v___y_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v_traceState_1582_; lean_object* v_env_1583_; lean_object* v_nextMacroScope_1584_; lean_object* v_ngen_1585_; lean_object* v_auxDeclNGen_1586_; lean_object* v_cache_1587_; lean_object* v_messages_1588_; lean_object* v_infoState_1589_; lean_object* v_snapshotTasks_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref(v_msg_1545_);
lean_dec(v_ref_1544_);
lean_dec_ref(v_tag_1540_);
lean_dec(v_cls_1538_);
v___x_1581_ = lean_st_ref_take(v___y_1550_);
v_traceState_1582_ = lean_ctor_get(v___x_1581_, 4);
v_env_1583_ = lean_ctor_get(v___x_1581_, 0);
v_nextMacroScope_1584_ = lean_ctor_get(v___x_1581_, 1);
v_ngen_1585_ = lean_ctor_get(v___x_1581_, 2);
v_auxDeclNGen_1586_ = lean_ctor_get(v___x_1581_, 3);
v_cache_1587_ = lean_ctor_get(v___x_1581_, 5);
v_messages_1588_ = lean_ctor_get(v___x_1581_, 6);
v_infoState_1589_ = lean_ctor_get(v___x_1581_, 7);
v_snapshotTasks_1590_ = lean_ctor_get(v___x_1581_, 8);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1592_ = v___x_1581_;
v_isShared_1593_ = v_isSharedCheck_1609_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snapshotTasks_1590_);
lean_inc(v_infoState_1589_);
lean_inc(v_messages_1588_);
lean_inc(v_cache_1587_);
lean_inc(v_traceState_1582_);
lean_inc(v_auxDeclNGen_1586_);
lean_inc(v_ngen_1585_);
lean_inc(v_nextMacroScope_1584_);
lean_inc(v_env_1583_);
lean_dec(v___x_1581_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1609_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint64_t v_tid_1594_; lean_object* v_traces_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1608_; 
v_tid_1594_ = lean_ctor_get_uint64(v_traceState_1582_, sizeof(void*)*1);
v_traces_1595_ = lean_ctor_get(v_traceState_1582_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_traceState_1582_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1597_ = v_traceState_1582_;
v_isShared_1598_ = v_isSharedCheck_1608_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_traces_1595_);
lean_dec(v_traceState_1582_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1608_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1543_, v_traces_1595_);
lean_dec_ref(v_traces_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1599_);
lean_ctor_set_uint64(v_reuseFailAlloc_1607_, sizeof(void*)*1, v_tid_1594_);
v___x_1601_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1603_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 4, v___x_1601_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_env_1583_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_nextMacroScope_1584_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_ngen_1585_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_auxDeclNGen_1586_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v_cache_1587_);
lean_ctor_set(v_reuseFailAlloc_1606_, 6, v_messages_1588_);
lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_infoState_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_snapshotTasks_1590_);
v___x_1603_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_st_ref_put(v___y_1550_, v___x_1603_);
v___x_1605_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_fst_1552_);
return v___x_1605_;
}
}
}
}
}
else
{
goto v___jp_1570_;
}
}
else
{
goto v___jp_1570_;
}
}
v___jp_1610_:
{
double v___x_1612_; double v___x_1613_; double v___x_1614_; uint8_t v___x_1615_; 
v___x_1612_ = lean_unbox_float(v_snd_1567_);
v___x_1613_ = lean_unbox_float(v_fst_1566_);
v___x_1614_ = lean_float_sub(v___x_1612_, v___x_1613_);
v___x_1615_ = lean_float_decLt(v___y_1611_, v___x_1614_);
v___y_1580_ = v___x_1615_;
goto v___jp_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5___boxed(lean_object* v_cls_1626_, lean_object* v_collapsed_1627_, lean_object* v_tag_1628_, lean_object* v_opts_1629_, lean_object* v_clsEnabled_1630_, lean_object* v_oldTraces_1631_, lean_object* v_ref_1632_, lean_object* v_msg_1633_, lean_object* v_resStartStop_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v_collapsed_boxed_1640_; uint8_t v_clsEnabled_boxed_1641_; lean_object* v_res_1642_; 
v_collapsed_boxed_1640_ = lean_unbox(v_collapsed_1627_);
v_clsEnabled_boxed_1641_ = lean_unbox(v_clsEnabled_1630_);
v_res_1642_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v_cls_1626_, v_collapsed_boxed_1640_, v_tag_1628_, v_opts_1629_, v_clsEnabled_boxed_1641_, v_oldTraces_1631_, v_ref_1632_, v_msg_1633_, v_resStartStop_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_opts_1629_);
return v_res_1642_;
}
}
static double _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0(void){
_start:
{
lean_object* v___x_1643_; double v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1000000000u);
v___x_1644_ = lean_float_of_nat(v___x_1643_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1(void){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__1, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__1_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__1);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__2, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__2_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__2);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__9));
v___x_1660_ = l_Lean_Name_append(v___x_1659_, v___x_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; uint8_t v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; uint8_t v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v_a_1682_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; uint8_t v___y_1695_; lean_object* v___y_1696_; uint8_t v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v_a_1705_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; uint8_t v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v_toCold_1734_; lean_object* v_currRecDepth_1735_; lean_object* v_ref_1736_; uint8_t v_suppressElabErrors_1737_; lean_object* v___y_1738_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; uint8_t v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; uint8_t v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1842_; uint8_t v___y_1843_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; uint8_t v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1881_; lean_object* v_lhs_1900_; lean_object* v_rhs_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; 
if (lean_obj_tag(v_x_1661_) == 1)
{
if (lean_obj_tag(v_x_1662_) == 1)
{
lean_object* v_a_1931_; lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v_x_1661_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v_x_1661_, 1);
v_a_1932_ = lean_ctor_get(v_x_1662_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v_x_1662_, 1);
v___x_1933_ = lean_is_level_def_eq(v_a_1931_, v_a_1932_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1933_;
}
else
{
v_lhs_1900_ = v_x_1661_;
v_rhs_1901_ = v_x_1662_;
v___y_1902_ = v_a_1663_;
v___y_1903_ = v_a_1664_;
v___y_1904_ = v_a_1665_;
v___y_1905_ = v_a_1666_;
goto v___jp_1899_;
}
}
else
{
v_lhs_1900_ = v_x_1661_;
v_rhs_1901_ = v_x_1662_;
v___y_1902_ = v_a_1663_;
v___y_1903_ = v_a_1664_;
v___y_1904_ = v_a_1665_;
v___y_1905_ = v_a_1666_;
goto v___jp_1899_;
}
v___jp_1668_:
{
lean_object* v___x_1683_; double v___x_1684_; double v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1683_ = lean_io_get_num_heartbeats();
v___x_1684_ = lean_float_of_nat(v___y_1674_);
v___x_1685_ = lean_float_of_nat(v___x_1683_);
v___x_1686_ = lean_box_float(v___x_1684_);
v___x_1687_ = lean_box_float(v___x_1685_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_a_1682_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1681_);
v___x_1690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1681_, v___y_1672_, v___y_1669_, v___y_1670_, v___y_1675_, v___y_1673_, v___y_1676_, v___y_1678_, v___x_1689_, v___y_1679_, v___y_1671_, v___y_1680_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1679_);
lean_dec_ref(v___y_1670_);
return v___x_1690_;
}
v___jp_1691_:
{
lean_object* v___x_1706_; double v___x_1707_; double v___x_1708_; double v___x_1709_; double v___x_1710_; double v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1706_ = lean_io_mono_nanos_now();
v___x_1707_ = lean_float_of_nat(v___y_1703_);
v___x_1708_ = lean_float_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__0, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__0_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__0);
v___x_1709_ = lean_float_div(v___x_1707_, v___x_1708_);
v___x_1710_ = lean_float_of_nat(v___x_1706_);
v___x_1711_ = lean_float_div(v___x_1710_, v___x_1708_);
v___x_1712_ = lean_box_float(v___x_1709_);
v___x_1713_ = lean_box_float(v___x_1711_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_a_1705_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1704_);
v___x_1716_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5(v___y_1704_, v___y_1695_, v___y_1692_, v___y_1693_, v___y_1697_, v___y_1696_, v___y_1698_, v___y_1700_, v___x_1715_, v___y_1701_, v___y_1694_, v___y_1702_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1693_);
return v___x_1716_;
}
v___jp_1717_:
{
lean_object* v_fileName_1739_; lean_object* v_fileMap_1740_; lean_object* v_currNamespace_1741_; lean_object* v_openDecls_1742_; lean_object* v_initHeartbeats_1743_; lean_object* v_maxHeartbeats_1744_; lean_object* v_quotContext_1745_; lean_object* v_currMacroScope_1746_; lean_object* v_cancelTk_x3f_1747_; lean_object* v_inheritedTraceOptions_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1800_; 
v_fileName_1739_ = lean_ctor_get(v_toCold_1734_, 0);
v_fileMap_1740_ = lean_ctor_get(v_toCold_1734_, 1);
v_currNamespace_1741_ = lean_ctor_get(v_toCold_1734_, 4);
v_openDecls_1742_ = lean_ctor_get(v_toCold_1734_, 5);
v_initHeartbeats_1743_ = lean_ctor_get(v_toCold_1734_, 6);
v_maxHeartbeats_1744_ = lean_ctor_get(v_toCold_1734_, 7);
v_quotContext_1745_ = lean_ctor_get(v_toCold_1734_, 8);
v_currMacroScope_1746_ = lean_ctor_get(v_toCold_1734_, 9);
v_cancelTk_x3f_1747_ = lean_ctor_get(v_toCold_1734_, 10);
v_inheritedTraceOptions_1748_ = lean_ctor_get(v_toCold_1734_, 11);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_toCold_1734_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; 
v_unused_1801_ = lean_ctor_get(v_toCold_1734_, 3);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_toCold_1734_, 2);
lean_dec(v_unused_1802_);
v___x_1750_ = v_toCold_1734_;
v_isShared_1751_ = v_isSharedCheck_1800_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_inheritedTraceOptions_1748_);
lean_inc(v_cancelTk_x3f_1747_);
lean_inc(v_currMacroScope_1746_);
lean_inc(v_quotContext_1745_);
lean_inc(v_maxHeartbeats_1744_);
lean_inc(v_initHeartbeats_1743_);
lean_inc(v_openDecls_1742_);
lean_inc(v_currNamespace_1741_);
lean_inc(v_fileMap_1740_);
lean_inc(v_fileName_1739_);
lean_dec(v_toCold_1734_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1800_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1752_ = l_Lean_maxRecDepth;
v___x_1753_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__4(v___y_1721_, v___x_1752_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 3, v___x_1753_);
lean_ctor_set(v___x_1750_, 2, v___y_1721_);
v___x_1755_ = v___x_1750_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_fileName_1739_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_fileMap_1740_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v___y_1721_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_currNamespace_1741_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_openDecls_1742_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_initHeartbeats_1743_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_maxHeartbeats_1744_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_quotContext_1745_);
lean_ctor_set(v_reuseFailAlloc_1799_, 9, v_currMacroScope_1746_);
lean_ctor_set(v_reuseFailAlloc_1799_, 10, v_cancelTk_x3f_1747_);
lean_ctor_set(v_reuseFailAlloc_1799_, 11, v_inheritedTraceOptions_1748_);
v___x_1755_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1756_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_currRecDepth_1735_);
lean_ctor_set(v___x_1756_, 2, v_ref_1736_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*3, v___y_1732_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*3 + 1, v_suppressElabErrors_1737_);
v___x_1757_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v___y_1730_, v___y_1729_, v___y_1719_, v___x_1756_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref_known(v___x_1756_, 3);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2_spec__3(v_a_1758_, v___y_1729_, v___y_1719_, v___y_1724_, v___y_1727_);
lean_dec_ref(v___y_1724_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1762_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___y_1720_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_io_mono_nanos_now();
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1729_);
v___x_1764_ = lean_apply_5(v___y_1728_, v___y_1729_, v___y_1719_, v___y_1731_, v___y_1727_, lean_box(0));
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 1);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
v___y_1692_ = v___y_1718_;
v___y_1693_ = v___y_1720_;
v___y_1694_ = v___y_1719_;
v___y_1695_ = v___y_1722_;
v___y_1696_ = v___y_1723_;
v___y_1697_ = v___y_1725_;
v___y_1698_ = v___y_1726_;
v___y_1699_ = v___y_1727_;
v___y_1700_ = v_a_1760_;
v___y_1701_ = v___y_1729_;
v___y_1702_ = v___y_1731_;
v___y_1703_ = v___x_1763_;
v___y_1704_ = v___y_1733_;
v_a_1705_ = v___x_1770_;
goto v___jp_1691_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_a_1773_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1764_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1764_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 0);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
v___y_1692_ = v___y_1718_;
v___y_1693_ = v___y_1720_;
v___y_1694_ = v___y_1719_;
v___y_1695_ = v___y_1722_;
v___y_1696_ = v___y_1723_;
v___y_1697_ = v___y_1725_;
v___y_1698_ = v___y_1726_;
v___y_1699_ = v___y_1727_;
v___y_1700_ = v_a_1760_;
v___y_1701_ = v___y_1729_;
v___y_1702_ = v___y_1731_;
v___y_1703_ = v___x_1763_;
v___y_1704_ = v___y_1733_;
v_a_1705_ = v___x_1778_;
goto v___jp_1691_;
}
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1729_);
v___x_1782_ = lean_apply_5(v___y_1728_, v___y_1729_, v___y_1719_, v___y_1731_, v___y_1727_, lean_box(0));
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 1);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
v___y_1669_ = v___y_1718_;
v___y_1670_ = v___y_1720_;
v___y_1671_ = v___y_1719_;
v___y_1672_ = v___y_1722_;
v___y_1673_ = v___y_1723_;
v___y_1674_ = v___x_1781_;
v___y_1675_ = v___y_1725_;
v___y_1676_ = v___y_1726_;
v___y_1677_ = v___y_1727_;
v___y_1678_ = v_a_1760_;
v___y_1679_ = v___y_1729_;
v___y_1680_ = v___y_1731_;
v___y_1681_ = v___y_1733_;
v_a_1682_ = v___x_1788_;
goto v___jp_1668_;
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1782_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1782_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 0);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
v___y_1669_ = v___y_1718_;
v___y_1670_ = v___y_1720_;
v___y_1671_ = v___y_1719_;
v___y_1672_ = v___y_1722_;
v___y_1673_ = v___y_1723_;
v___y_1674_ = v___x_1781_;
v___y_1675_ = v___y_1725_;
v___y_1676_ = v___y_1726_;
v___y_1677_ = v___y_1727_;
v___y_1678_ = v_a_1760_;
v___y_1679_ = v___y_1729_;
v___y_1680_ = v___y_1731_;
v___y_1681_ = v___y_1733_;
v_a_1682_ = v___x_1796_;
goto v___jp_1668_;
}
}
}
}
}
}
}
v___jp_1803_:
{
lean_object* v_toCold_1822_; lean_object* v_currRecDepth_1823_; lean_object* v_ref_1824_; uint8_t v_suppressElabErrors_1825_; 
v_toCold_1822_ = lean_ctor_get(v___y_1820_, 0);
lean_inc_ref(v_toCold_1822_);
v_currRecDepth_1823_ = lean_ctor_get(v___y_1820_, 1);
lean_inc(v_currRecDepth_1823_);
v_ref_1824_ = lean_ctor_get(v___y_1820_, 2);
lean_inc(v_ref_1824_);
v_suppressElabErrors_1825_ = lean_ctor_get_uint8(v___y_1820_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_1820_);
v___y_1718_ = v___y_1804_;
v___y_1719_ = v___y_1805_;
v___y_1720_ = v___y_1806_;
v___y_1721_ = v___y_1807_;
v___y_1722_ = v___y_1808_;
v___y_1723_ = v___y_1809_;
v___y_1724_ = v___y_1810_;
v___y_1725_ = v___y_1811_;
v___y_1726_ = v___y_1812_;
v___y_1727_ = v___y_1813_;
v___y_1728_ = v___y_1814_;
v___y_1729_ = v___y_1815_;
v___y_1730_ = v___y_1816_;
v___y_1731_ = v___y_1817_;
v___y_1732_ = v___y_1818_;
v___y_1733_ = v___y_1819_;
v_toCold_1734_ = v_toCold_1822_;
v_currRecDepth_1735_ = v_currRecDepth_1823_;
v_ref_1736_ = v_ref_1824_;
v_suppressElabErrors_1737_ = v_suppressElabErrors_1825_;
v___y_1738_ = v___y_1821_;
goto v___jp_1717_;
}
v___jp_1826_:
{
if (v___y_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v_env_1845_; lean_object* v_nextMacroScope_1846_; lean_object* v_ngen_1847_; lean_object* v_auxDeclNGen_1848_; lean_object* v_traceState_1849_; lean_object* v_messages_1850_; lean_object* v_infoState_1851_; lean_object* v_snapshotTasks_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1862_; 
v___x_1844_ = lean_st_ref_take(v___y_1836_);
v_env_1845_ = lean_ctor_get(v___x_1844_, 0);
v_nextMacroScope_1846_ = lean_ctor_get(v___x_1844_, 1);
v_ngen_1847_ = lean_ctor_get(v___x_1844_, 2);
v_auxDeclNGen_1848_ = lean_ctor_get(v___x_1844_, 3);
v_traceState_1849_ = lean_ctor_get(v___x_1844_, 4);
v_messages_1850_ = lean_ctor_get(v___x_1844_, 6);
v_infoState_1851_ = lean_ctor_get(v___x_1844_, 7);
v_snapshotTasks_1852_ = lean_ctor_get(v___x_1844_, 8);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1844_, 5);
lean_dec(v_unused_1863_);
v___x_1854_ = v___x_1844_;
v_isShared_1855_ = v_isSharedCheck_1862_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_snapshotTasks_1852_);
lean_inc(v_infoState_1851_);
lean_inc(v_messages_1850_);
lean_inc(v_traceState_1849_);
lean_inc(v_auxDeclNGen_1848_);
lean_inc(v_ngen_1847_);
lean_inc(v_nextMacroScope_1846_);
lean_inc(v_env_1845_);
lean_dec(v___x_1844_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1862_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1856_ = l_Lean_Kernel_enableDiag(v_env_1845_, v___y_1841_);
v___x_1857_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__3, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__3_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__3);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 5, v___x_1857_);
lean_ctor_set(v___x_1854_, 0, v___x_1856_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_nextMacroScope_1846_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_ngen_1847_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_auxDeclNGen_1848_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_traceState_1849_);
lean_ctor_set(v_reuseFailAlloc_1861_, 5, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1861_, 6, v_messages_1850_);
lean_ctor_set(v_reuseFailAlloc_1861_, 7, v_infoState_1851_);
lean_ctor_set(v_reuseFailAlloc_1861_, 8, v_snapshotTasks_1852_);
v___x_1859_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_st_ref_put(v___y_1836_, v___x_1859_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1833_);
v___y_1804_ = v___y_1827_;
v___y_1805_ = v___y_1828_;
v___y_1806_ = v___y_1829_;
v___y_1807_ = v___y_1830_;
v___y_1808_ = v___y_1831_;
v___y_1809_ = v___y_1832_;
v___y_1810_ = v___y_1833_;
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1837_;
v___y_1816_ = v___y_1839_;
v___y_1817_ = v___y_1840_;
v___y_1818_ = v___y_1841_;
v___y_1819_ = v___y_1842_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1836_;
goto v___jp_1803_;
}
}
}
else
{
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1833_);
v___y_1804_ = v___y_1827_;
v___y_1805_ = v___y_1828_;
v___y_1806_ = v___y_1829_;
v___y_1807_ = v___y_1830_;
v___y_1808_ = v___y_1831_;
v___y_1809_ = v___y_1832_;
v___y_1810_ = v___y_1833_;
v___y_1811_ = v___y_1834_;
v___y_1812_ = v___y_1835_;
v___y_1813_ = v___y_1836_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1837_;
v___y_1816_ = v___y_1839_;
v___y_1817_ = v___y_1840_;
v___y_1818_ = v___y_1841_;
v___y_1819_ = v___y_1842_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1836_;
goto v___jp_1803_;
}
}
v___jp_1864_:
{
lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v_env_1885_; lean_object* v_ref_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__1___redArg(v___y_1874_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = lean_st_ref_get(v___y_1874_);
v_env_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc_ref(v_env_1885_);
lean_dec(v___x_1884_);
v_ref_1886_ = l_Lean_replaceRef(v___y_1872_, v___y_1872_);
lean_inc(v_ref_1886_);
lean_inc(v___y_1870_);
lean_inc_ref(v___y_1875_);
v___x_1887_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1887_, 0, v___y_1875_);
lean_ctor_set(v___x_1887_, 1, v___y_1870_);
lean_ctor_set(v___x_1887_, 2, v_ref_1886_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*3, v___y_1880_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*3 + 1, v___y_1878_);
v___x_1888_ = l_Lean_MessageData_ofLevel(v___y_1869_);
v___x_1889_ = lean_obj_once(&l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4, &l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4_once, _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_ofLevel(v___y_1873_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__6));
v___x_1894_ = 0;
lean_inc_ref(v___y_1867_);
v___x_1895_ = l_Lean_Options_set___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__2(v___y_1867_, v___x_1893_, v___x_1894_);
v___x_1896_ = l_Lean_diagnostics;
v___x_1897_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v___x_1895_, v___x_1896_);
v___x_1898_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1885_);
lean_dec_ref(v_env_1885_);
if (v___x_1897_ == 0)
{
if (v___x_1898_ == 0)
{
lean_inc(v___y_1874_);
v___y_1718_ = v___y_1865_;
v___y_1719_ = v___y_1866_;
v___y_1720_ = v___y_1867_;
v___y_1721_ = v___x_1895_;
v___y_1722_ = v___y_1868_;
v___y_1723_ = v_a_1883_;
v___y_1724_ = v___x_1887_;
v___y_1725_ = v___y_1871_;
v___y_1726_ = v___y_1872_;
v___y_1727_ = v___y_1874_;
v___y_1728_ = v___y_1876_;
v___y_1729_ = v___y_1877_;
v___y_1730_ = v___x_1892_;
v___y_1731_ = v___y_1879_;
v___y_1732_ = v___x_1897_;
v___y_1733_ = v___y_1881_;
v_toCold_1734_ = v___y_1875_;
v_currRecDepth_1735_ = v___y_1870_;
v_ref_1736_ = v_ref_1886_;
v_suppressElabErrors_1737_ = v___y_1878_;
v___y_1738_ = v___y_1874_;
goto v___jp_1717_;
}
else
{
lean_dec(v_ref_1886_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1870_);
v___y_1827_ = v___y_1865_;
v___y_1828_ = v___y_1866_;
v___y_1829_ = v___y_1867_;
v___y_1830_ = v___x_1895_;
v___y_1831_ = v___y_1868_;
v___y_1832_ = v_a_1883_;
v___y_1833_ = v___x_1887_;
v___y_1834_ = v___y_1871_;
v___y_1835_ = v___y_1872_;
v___y_1836_ = v___y_1874_;
v___y_1837_ = v___y_1877_;
v___y_1838_ = v___y_1876_;
v___y_1839_ = v___x_1892_;
v___y_1840_ = v___y_1879_;
v___y_1841_ = v___x_1897_;
v___y_1842_ = v___y_1881_;
v___y_1843_ = v___x_1897_;
goto v___jp_1826_;
}
}
else
{
lean_dec(v_ref_1886_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1870_);
v___y_1827_ = v___y_1865_;
v___y_1828_ = v___y_1866_;
v___y_1829_ = v___y_1867_;
v___y_1830_ = v___x_1895_;
v___y_1831_ = v___y_1868_;
v___y_1832_ = v_a_1883_;
v___y_1833_ = v___x_1887_;
v___y_1834_ = v___y_1871_;
v___y_1835_ = v___y_1872_;
v___y_1836_ = v___y_1874_;
v___y_1837_ = v___y_1877_;
v___y_1838_ = v___y_1876_;
v___y_1839_ = v___x_1892_;
v___y_1840_ = v___y_1879_;
v___y_1841_ = v___x_1897_;
v___y_1842_ = v___y_1881_;
v___y_1843_ = v___x_1898_;
goto v___jp_1826_;
}
}
v___jp_1899_:
{
lean_object* v_toCold_1906_; lean_object* v_options_1907_; lean_object* v_currRecDepth_1908_; lean_object* v_ref_1909_; uint8_t v_diag_1910_; uint8_t v_suppressElabErrors_1911_; lean_object* v_inheritedTraceOptions_1912_; uint8_t v_hasTrace_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___y_1922_; 
v_toCold_1906_ = lean_ctor_get(v___y_1904_, 0);
v_options_1907_ = lean_ctor_get(v_toCold_1906_, 2);
v_currRecDepth_1908_ = lean_ctor_get(v___y_1904_, 1);
v_ref_1909_ = lean_ctor_get(v___y_1904_, 2);
v_diag_1910_ = lean_ctor_get_uint8(v___y_1904_, sizeof(void*)*3);
v_suppressElabErrors_1911_ = lean_ctor_get_uint8(v___y_1904_, sizeof(void*)*3 + 1);
v_inheritedTraceOptions_1912_ = lean_ctor_get(v_toCold_1906_, 11);
v_hasTrace_1913_ = lean_ctor_get_uint8(v_options_1907_, sizeof(void*)*1);
v___x_1914_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4));
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5));
v___x_1916_ = l_Lean_Level_getLevelOffset(v_lhs_1900_);
v___x_1917_ = l_Lean_Level_getLevelOffset(v_rhs_1901_);
v___x_1918_ = lean_level_eq(v___x_1916_, v___x_1917_);
lean_dec(v___x_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = 1;
v___x_1920_ = lean_box(v___x_1918_);
v___x_1921_ = lean_box(v___x_1919_);
lean_inc(v_rhs_1901_);
lean_inc(v_lhs_1900_);
v___y_1922_ = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 11, 6);
lean_closure_set(v___y_1922_, 0, v___x_1920_);
lean_closure_set(v___y_1922_, 1, v_lhs_1900_);
lean_closure_set(v___y_1922_, 2, v_rhs_1901_);
lean_closure_set(v___y_1922_, 3, v___x_1914_);
lean_closure_set(v___y_1922_, 4, v___x_1915_);
lean_closure_set(v___y_1922_, 5, v___x_1921_);
if (v_hasTrace_1913_ == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref(v___y_1922_);
v___x_1923_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1918_, v_lhs_1900_, v_rhs_1901_, v___x_1914_, v___x_1915_, v___x_1919_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1924_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_1925_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__2___closed__1));
v___x_1926_ = lean_obj_once(&l_Lean_Meta_isLevelDefEqAuxImpl___closed__8, &l_Lean_Meta_isLevelDefEqAuxImpl___closed__8_once, _init_l_Lean_Meta_isLevelDefEqAuxImpl___closed__8);
v___x_1927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1912_, v_options_1907_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = l_Lean_trace_profiler;
v___x_1929_ = l_Lean_Option_get___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__3(v_options_1907_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref(v___y_1922_);
v___x_1930_ = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(v___x_1918_, v_lhs_1900_, v_rhs_1901_, v___x_1914_, v___x_1915_, v___x_1919_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v___x_1930_;
}
else
{
lean_inc(v_ref_1909_);
lean_inc(v_currRecDepth_1908_);
lean_inc_ref(v_options_1907_);
lean_inc_ref(v_toCold_1906_);
v___y_1865_ = v___x_1925_;
v___y_1866_ = v___y_1903_;
v___y_1867_ = v_options_1907_;
v___y_1868_ = v___x_1919_;
v___y_1869_ = v_lhs_1900_;
v___y_1870_ = v_currRecDepth_1908_;
v___y_1871_ = v___x_1927_;
v___y_1872_ = v_ref_1909_;
v___y_1873_ = v_rhs_1901_;
v___y_1874_ = v___y_1905_;
v___y_1875_ = v_toCold_1906_;
v___y_1876_ = v___y_1922_;
v___y_1877_ = v___y_1902_;
v___y_1878_ = v_suppressElabErrors_1911_;
v___y_1879_ = v___y_1904_;
v___y_1880_ = v_diag_1910_;
v___y_1881_ = v___x_1924_;
goto v___jp_1864_;
}
}
else
{
lean_inc(v_ref_1909_);
lean_inc(v_currRecDepth_1908_);
lean_inc_ref(v_options_1907_);
lean_inc_ref(v_toCold_1906_);
v___y_1865_ = v___x_1925_;
v___y_1866_ = v___y_1903_;
v___y_1867_ = v_options_1907_;
v___y_1868_ = v___x_1919_;
v___y_1869_ = v_lhs_1900_;
v___y_1870_ = v_currRecDepth_1908_;
v___y_1871_ = v___x_1927_;
v___y_1872_ = v_ref_1909_;
v___y_1873_ = v_rhs_1901_;
v___y_1874_ = v___y_1905_;
v___y_1875_ = v_toCold_1906_;
v___y_1876_ = v___y_1922_;
v___y_1877_ = v___y_1902_;
v___y_1878_ = v_suppressElabErrors_1911_;
v___y_1879_ = v___y_1904_;
v___y_1880_ = v_diag_1910_;
v___y_1881_ = v___x_1924_;
goto v___jp_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___boxed(lean_object* v_x_1934_, lean_object* v_x_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = lean_is_level_def_eq(v_x_1934_, v_x_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(lean_object* v_00_u03b1_1942_, lean_object* v_x_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___redArg(v_x_1943_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1950_, lean_object* v_x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___at___00Lean_Meta_isLevelDefEqAuxImpl_spec__5_spec__6(v_00_u03b1_1950_, v_x_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = ((lean_object*)(l_Lean_Meta_isLevelDefEqAuxImpl___closed__7));
v___x_2015_ = 0;
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_));
v___x_2017_ = l_Lean_registerTraceClass(v___x_2014_, v___x_2015_, v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref_known(v___x_2017_, 1);
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1));
v___x_2019_ = 1;
v___x_2020_ = l_Lean_registerTraceClass(v___x_2018_, v___x_2019_, v___x_2016_);
return v___x_2020_;
}
else
{
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2____boxed(lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_LevelDefEq_1935786688____hygCtx___hyg_2_();
return v_res_2022_;
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
